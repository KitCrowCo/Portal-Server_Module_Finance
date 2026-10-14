# /modules/finance/finance.py
"""
Finance - simple, AuDHD-friendly household cash flow tracker.
Data lives in one SQLite file per group (data/finance/{group_id}.db) - directly exportable,
directly readable by an external widget app with no server involvement.
Liquid cash and debt are tracked separately and never netted automatically - the goal is
two numbers a person can hold in their head, not a single misleading net-worth figure.
"""
import io, re, csv, json, uuid, sqlite3, calendar, asyncio
from pathlib import Path
from datetime import date, timedelta, datetime
from sqlalchemy import text
from fastapi import APIRouter, Request
from fastapi.responses import HTMLResponse, FileResponse

MODULE_META = {"label": "Finance", "icon": "&#x1F4B0;", "description": "Household cash flow, bills, and balance tracking"}

router = APIRouter()
_P = "/module/finance"
DATA_DIR = Path("./data/finance")
GROUPS_FILE = DATA_DIR / "groups.json"
HORIZON_DAYS = 120

ENV = {}
UI = BI = IM = TM = None

def _esc(s): return str(s).replace("&","&amp;").replace("<","&lt;").replace(">","&gt;").replace('"',"&quot;")
def _money(v): return f"${v:,.2f}" if v >= 0 else f"-${abs(v):,.2f}"

# --- Groups (household scoping) ---

def _load_groups() -> dict: return json.loads(GROUPS_FILE.read_text()) if GROUPS_FILE.exists() else {}
def _save_groups(g: dict): GROUPS_FILE.parent.mkdir(parents=True, exist_ok=True); GROUPS_FILE.write_text(json.dumps(g, indent=2))

def _ensure_personal_group(username: str) -> str:
    groups = _load_groups()
    gid = f"personal_{username}"
    if gid not in groups:
        groups[gid] = {"label": f"{username}'s Finances", "members": [username], "low_balance_threshold": 100.0, "last_low_balance_notify": None}
        _save_groups(groups)
    return gid

def _user_groups(username: str) -> list: return [{"id": gid, **g} for gid, g in _load_groups().items() if username in g.get("members", [])]

async def _active_group(request) -> str:
    gid = await ENV["get_state"](request, scope="user", namespace="finance", key="active_group")
    groups = _load_groups()
    if gid and gid in groups and request.state.user.username in groups[gid].get("members", []): return gid
    default_gid = await ENV["get_state"](request, scope="user", namespace="finance", key="default_group")
    if default_gid and default_gid in groups and request.state.user.username in groups[default_gid].get("members", []): return default_gid
    return _ensure_personal_group(request.state.user.username)

def _real_usernames() -> set:
    """Reads usernames via the platform's already-injected db dependency and a raw SQL SELECT - avoids importing the core User model from an uncertain relative path (a dynamically loaded module's __package__ doesn't reliably resolve '..database' style imports back into the core package). Raw SQL against the known 'users' table is deliberately minimal surface: one column read, no ORM coupling, no guessed import path."""
    from contextlib import contextmanager
    with contextmanager(ENV["db"])() as db:
        return {r[0] for r in db.execute(text("SELECT username FROM users"))}

# --- DB ---

def _db_path(gid: str) -> Path: return DATA_DIR / f"{Path(gid).name}.db"

def _ensure_column(conn, table, col, coltype):
    cols = {r[1] for r in conn.execute(f"PRAGMA table_info({table})")}
    if col not in cols: conn.execute(f"ALTER TABLE {table} ADD COLUMN {col} {coltype}")

def _conn(gid: str) -> sqlite3.Connection:
    p = _db_path(gid)
    p.parent.mkdir(parents=True, exist_ok=True)
    c = sqlite3.connect(p)
    c.row_factory = sqlite3.Row
    c.execute("CREATE TABLE IF NOT EXISTS accounts (id TEXT PRIMARY KEY, label TEXT, type TEXT, is_liquid INTEGER, balance REAL, asof TEXT, notes TEXT, credit_limit REAL, apr REAL)")
    c.execute("CREATE TABLE IF NOT EXISTS recurring (id TEXT PRIMARY KEY, label TEXT, kind TEXT, account_id TEXT, to_account_id TEXT, amount REAL, is_estimate INTEGER, frequency TEXT, anchor_date TEXT, day1 INTEGER, day2 INTEGER, notify INTEGER, notify_days_before INTEGER, category TEXT, active INTEGER, last_notified_date TEXT, auto_pay INTEGER)")
    c.execute("CREATE TABLE IF NOT EXISTS entries (id TEXT PRIMARY KEY, account_id TEXT, date TEXT, label TEXT, amount REAL, category TEXT, projected INTEGER, recurring_id TEXT, linked_entry_id TEXT, confirmed INTEGER)")
    c.execute("CREATE TABLE IF NOT EXISTS exceptions (recurring_id TEXT, date TEXT, PRIMARY KEY(recurring_id, date))")
    c.execute("CREATE TABLE IF NOT EXISTS notes (id TEXT PRIMARY KEY, date TEXT, text TEXT, author TEXT, t TEXT)")
    c.execute("CREATE TABLE IF NOT EXISTS imports (id TEXT PRIMARY KEY, t TEXT, kind TEXT, label TEXT, ids TEXT)")
    for col, t in (("credit_limit","REAL"), ("apr","REAL")): _ensure_column(c, "accounts", col, t)
    _ensure_column(c, "recurring", "auto_pay", "INTEGER")
    _ensure_column(c, "recurring", "hourly_rate", "REAL")
    _ensure_column(c, "recurring", "hours_per_day", "REAL")
    _ensure_column(c, "recurring", "deduction_pct", "REAL")
    return c

def _accounts(gid: str) -> list: c = _conn(gid); rows = [dict(r) for r in c.execute("SELECT * FROM accounts ORDER BY type, label")]; c.close(); return rows
def _account_map(gid: str) -> dict: return {a["id"]: a for a in _accounts(gid)}
def _entry(gid: str, eid: str): c = _conn(gid); r = c.execute("SELECT * FROM entries WHERE id=?", (eid,)).fetchone(); c.close(); return dict(r) if r else None

def _display_day(r: dict) -> str:
    if r["frequency"] == "monthly": return f"day {r['day1']}"
    if r["frequency"] == "semimonthly": return f"days {r['day1']} & {r['day2']}"
    if r["frequency"] in ("weekly","biweekly"): return date.fromisoformat(r["anchor_date"]).strftime("%A")
    if r["frequency"] == "yearly": return date.fromisoformat(r["anchor_date"]).strftime("%b %d")
    return ""

def _recurring(gid: str) -> list:
    c = _conn(gid)
    rows = [dict(r) for r in c.execute("SELECT * FROM recurring")]
    c.close()
    def sort_key(r):
        day = date.fromisoformat(r["anchor_date"]).day if r["frequency"] in ("weekly","biweekly","yearly") else (r["day1"] or 1)
        return (not r["active"], day, r["label"])
    return sorted(rows, key=sort_key)

# --- Occurrence generation (recurring rule -> concrete calendar dates) ---

def _occurrences(rec: dict, start: date, end: date) -> list:
    freq, anchor = rec["frequency"], date.fromisoformat(rec["anchor_date"])
    out = []
    if freq in ("weekly", "biweekly"):
        step = 7 if freq == "weekly" else 14
        d = anchor
        while d < start: d += timedelta(days=step)
        while d <= end:
            if d >= anchor: out.append(d)
            d += timedelta(days=step)
    elif freq == "monthly":
        d = date(start.year, start.month, 1)
        while d <= end:
            last = calendar.monthrange(d.year, d.month)[1]
            occ = date(d.year, d.month, min(rec["day1"] or 1, last))
            if start <= occ <= end and occ >= anchor: out.append(occ)
            d = date(d.year + (d.month == 12), d.month % 12 + 1, 1)
    elif freq == "semimonthly":
        d = date(start.year, start.month, 1)
        while d <= end:
            last = calendar.monthrange(d.year, d.month)[1]
            for dd in (rec["day1"] or 1, rec["day2"] or 15):
                occ = date(d.year, d.month, min(dd, last))
                if start <= occ <= end and occ >= anchor: out.append(occ)
            d = date(d.year + (d.month == 12), d.month % 12 + 1, 1)
    elif freq == "yearly":
        for y in range(start.year, end.year + 1):
            month, day = anchor.month, anchor.day
            if month == 2 and day == 29 and not calendar.isleap(y): day = 28
            occ = date(y, month, day)
            if start <= occ <= end and occ >= anchor: out.append(occ)
    return sorted(set(out))

def _materialize(gid: str, horizon_days: int = HORIZON_DAYS):
    """Regenerates all future unconfirmed projected entries from active recurring rules. Idempotent - safe to call on every calendar render.
    Skips any (recurring_id, date) pair recorded in the exceptions table - the mechanism per-occurrence skip/delete uses."""
    conn = _conn(gid)
    today = date.today(); end = today + timedelta(days=horizon_days)
    conn.execute("DELETE FROM entries WHERE projected=1 AND confirmed=0 AND date>=?", (today.isoformat(),))
    for rec in [dict(r) for r in conn.execute("SELECT * FROM recurring WHERE active=1")]:
        skip = {r["date"] for r in conn.execute("SELECT date FROM exceptions WHERE recurring_id=?", (rec["id"],))}
        for occ in _occurrences(rec, today, end):
            if occ.isoformat() in skip: continue
            if rec["kind"] == "wage":
                p_start, p_end = _wage_period_bounds(rec, occ)
                amt = _weekday_count(p_start, p_end) * (rec["hours_per_day"] or 8.0) * (rec["hourly_rate"] or 0.0) * (1 - (rec.get("deduction_pct") or 0)/100)
                conn.execute("INSERT INTO entries VALUES (?,?,?,?,?,?,?,?,?,?)", (uuid.uuid4().hex[:10], rec["account_id"], occ.isoformat(), rec["label"], amt, rec["category"], 1, rec["id"], None, 0))
            elif rec["kind"] == "transfer":
                e1, e2 = uuid.uuid4().hex[:10], uuid.uuid4().hex[:10]
                conn.execute("INSERT INTO entries VALUES (?,?,?,?,?,?,?,?,?,?)", (e1, rec["account_id"], occ.isoformat(), rec["label"], -abs(rec["amount"]), rec["category"], 1, rec["id"], e2, 0))
                conn.execute("INSERT INTO entries VALUES (?,?,?,?,?,?,?,?,?,?)", (e2, rec["to_account_id"], occ.isoformat(), rec["label"], abs(rec["amount"]), rec["category"], 1, rec["id"], e1, 0))
            else:
                sign = 1 if rec["kind"] == "income" else -1
                conn.execute("INSERT INTO entries VALUES (?,?,?,?,?,?,?,?,?,?)", (uuid.uuid4().hex[:10], rec["account_id"], occ.isoformat(), rec["label"], sign * abs(rec["amount"]), rec["category"], 1, rec["id"], None, 0))
    conn.commit(); conn.close()

# --- Balance calculation ---

def _in_balance(e, asof: str, auto: set) -> bool:
    """An auto-pay occurrence dated on or before the account's entered balance date is already in that balance (the bank took it), so it is not counted again."""
    return bool(e["projected"] and e["recurring_id"] in auto and e["date"] <= (asof or ""))

def _balances_at(gid: str, target: date) -> dict:
    """Each account on target: the balance you entered (as of its date), plus confirmed entries after that date up to target; from today on also the unconfirmed ones dated up to target
    (bills not marked paid - overdue ones included - and projected occurrences), so each future day shows what the plan leaves on that day."""
    conn, out, t = _conn(gid), {}, target.isoformat()
    auto = {r["id"] for r in conn.execute("SELECT id FROM recurring WHERE auto_pay=1")}
    for a in [dict(r) for r in conn.execute("SELECT * FROM accounts")]:
        asof = a["asof"] or t
        confirmed_delta = conn.execute("SELECT COALESCE(SUM(amount),0) s FROM entries WHERE account_id=? AND confirmed=1 AND date>? AND date<=?", (a["id"], asof, t)).fetchone()["s"]
        pending_delta = sum(e["amount"] for e in conn.execute("SELECT amount, date, projected, recurring_id FROM entries WHERE account_id=? AND confirmed=0 AND date<=?", (a["id"], t)) if not _in_balance(e, asof, auto)) if target >= date.today() else 0.0
        out[a["id"]] = {**a, "balance": a["balance"] + confirmed_delta + pending_delta, "is_liquid": bool(a["is_liquid"])}
    conn.close()
    return out

def _settled_liquid(gid: str) -> float:
    """Liquid money as the accounts stand today: entered balances plus confirmed entries since their dates - nothing still due is taken off (Upcoming does that, row by row)."""
    conn, t = _conn(gid), date.today().isoformat()
    total = sum(a["balance"] + conn.execute("SELECT COALESCE(SUM(amount),0) s FROM entries WHERE account_id=? AND confirmed=1 AND date>? AND date<=?", (a["id"], a["asof"] or t, t)).fetchone()["s"] for a in conn.execute("SELECT * FROM accounts WHERE is_liquid=1").fetchall())
    conn.close()
    return total


def _liquid_total(balances: dict) -> float: return sum(v["balance"] for v in balances.values() if v["is_liquid"])
def _debt_total(balances: dict) -> float: return sum(v["balance"] for v in balances.values() if v["type"] in ("credit", "debt"))

# --- Calendar rendering ---
# Grid always spans full weeks including adjacent-month lead/trail days, so end-of-month never leaves the next few days looking unknown.

def _extended_grid(gid: str, center_year: int, center_month: int) -> list:
    """9 full weeks (63 days), centered on the MIDDLE of center_month (not day 1) so coverage into the adjacent month on either side stays roughly symmetric regardless of which weekday the month happens to start on."""
    conn = _conn(gid)
    last_day = calendar.monthrange(center_year, center_month)[1]
    center_anchor = date(center_year, center_month, min(15, last_day))
    center_start = center_anchor - timedelta(days=center_anchor.weekday())
    grid_start = center_start - timedelta(days=28)
    grid_end = grid_start + timedelta(days=62)
    entries = conn.execute("SELECT * FROM entries WHERE date>=? AND date<=? ORDER BY date", (grid_start.isoformat(), grid_end.isoformat())).fetchall()
    noted = {r["date"] for r in conn.execute("SELECT DISTINCT date FROM notes WHERE date>=? AND date<=?", (grid_start.isoformat(), grid_end.isoformat()))}
    conn.close()
    by_day = {}
    for e in entries: by_day.setdefault(e["date"], []).append(dict(e))
    weeks, week, d = [], [], grid_start
    while d <= grid_end:
        week.append({"date": d, "entries": by_day.get(d.isoformat(), []), "liquid": _liquid_total(_balances_at(gid, d)), "in_month": d.month == center_month and d.year == center_year, "noted": d.isoformat() in noted})
        if len(week) == 7: weeks.append(week); week = []
        d += timedelta(days=1)
    return weeks

def _day_cell_html(cell, gid) -> str:
    d, entries, liquid, in_month = cell["date"], cell["entries"], cell["liquid"], cell["in_month"]
    cls = "fin-day" + (" fin-day-today" if d == date.today() else "") + ("" if in_month else " fin-day-other-month")
    rows = "".join(f"""<div class="fin-entry" style="color:{'#00ffa2' if e['amount']>=0 else '#ff8c8c'}" title="{_esc(e['label'])}">{_esc(e['label'][:14])} {_money(e['amount'])}{' ~' if not e.get('confirmed') and e.get('projected') else ''}</div>""" for e in entries[:3])
    more_labels = "; ".join(f"{e['label']} {_money(e['amount'])}" for e in entries[3:])
    more = f'<div class="dim tiny" title="{_esc(more_labels)}">+{len(entries)-3} more</div>' if len(entries) > 3 else ""
    return f"""<div class="{cls}" hx-post="/im/in" hx-target="body" hx-swap="none" hx-vals='{json.dumps({"type":"finance_day_open","lvl":1,"date":d.isoformat()})}'>
                   <div class="fin-day-num">{d.day}{' <span class="dim tiny">&#x1F4DD;</span>' if cell["noted"] else ""}</div>{rows}{more}
                   <div class="fin-day-liquid" style="color:{'#00ffa2' if liquid>=0 else '#ff5f5f'}">{_money(liquid)}</div>
               </div>"""

def _calendar_html(gid: str, year: int, month: int) -> str:
    _materialize(gid)
    weeks = _extended_grid(gid, year, month)
    dow = "".join(f'<div class="fin-dow">{d}</div>' for d in ("Mon","Tue","Wed","Thu","Fri","Sat","Sun"))
    grid = "".join(f'<div class="fin-week">{"".join(_day_cell_html(c, gid) for c in w)}</div>' for w in weeks)
    prev_y, prev_m = (year-1, 12) if month == 1 else (year, month-1)
    next_y, next_m = (year+1, 1) if month == 12 else (year, month+1)
    nav = lambda y, m: json.dumps({"type":"finance_calendar_nav","lvl":1,"year":y,"month":m})
    balances = _balances_at(gid, date.today())
    liquid, debt = _liquid_total(balances), _debt_total(balances)
    header = f"""<div class="info-bar" style="justify-content:space-between">
                     <span>Liquid now: <b style="color:{'#00ffa2' if liquid>=0 else '#ff5f5f'};font-size:1.3em">{_money(liquid)}</b></span>
                     <span>Debt owed: <b style="color:#ffaa44">{_money(debt)}</b></span>
                 </div>
                 <div style="display:flex;align-items:center;gap:.5rem;margin-bottom:.4rem">
                     <button class="btn-icon" hx-post="/im/in" hx-target="body" hx-swap="none" hx-vals='{nav(prev_y,prev_m)}'>&#x25C0;</button>
                     <span style="flex:1;text-align:center;font-weight:600">{calendar.month_name[month]} {year} <span class="dim tiny">(&#177;4 weeks shown)</span></span>
                     <button class="btn-icon" hx-post="/im/in" hx-target="body" hx-swap="none" hx-vals='{nav(next_y,next_m)}'>&#x25B6;</button>
                 </div>"""
    return f'<div id="fin-calendar">{header}<div class="fin-cal-grid"><div class="fin-week fin-dow-row">{dow}</div>{grid}</div></div>'

def _day_detail_html(gid: str, d: date) -> str:
    """Each row is its own tiny save-form: editing label/amount and hitting the checkmark both corrects the entry AND confirms it in one action - separate 'edit' vs 'confirm' steps would just be extra friction for a correction that's already 'good enough, not perfect' by design."""
    conn = _conn(gid); entries = [dict(r) for r in conn.execute("SELECT * FROM entries WHERE date=? ORDER BY amount", (d.isoformat(),))]; conn.close()
    accounts = _account_map(gid)
    rows = ""
    for e in entries:
        badge = "" if e["confirmed"] else '<span class="dim tiny">projected</span>'
        del_title = "Delete / skip this occurrence" if (e["recurring_id"] and not e["confirmed"]) else "Delete"
        rows += f"""<form hx-post="/im/in" hx-target="body" hx-swap="none" hx-include="this" style="display:flex;gap:.3rem;align-items:center;padding:.3rem 0;border-bottom:var(--border-thick) solid var(--border);font-size:.78rem">
                        <input type="hidden" name="type" value="finance_entry_save"><input type="hidden" name="lvl" value="1"><input type="hidden" name="id" value="{e['id']}">
                        <input type="text" name="label" value="{_esc(e['label'])}" class="module-select" style="flex:1;margin:0">
                        <span class="dim tiny">{_esc(accounts.get(e['account_id'],{}).get('label','?'))}</span>
                        <input type="number" name="amount" step="0.01" value="{e['amount']}" class="module-select" style="width:6rem;margin:0">
                        {badge}
                        <button type="submit" class="btn-icon" title="Save and confirm">&#x2713;</button>
                        <button type="button" class="btn-icon" style="color:#ff5f5f" hx-post="/im/in" hx-target="body" hx-swap="none" hx-vals='{json.dumps({"type":"finance_entry_delete","lvl":1,"id":e["id"]})}' title="{del_title}">&#x2715;</button>
                    </form>"""
    notes = "".join(f"""<div class="list-row row"><span class="grow pre-wrap">{_esc(n["text"])}</span><span class="dim tiny">{_esc(n["author"])} {n["t"][5:16].replace("T", " ")}</span><button type="button" class="btn-icon" style="color:#ff5f5f" {_vals("note_delete", id=n["id"], date=d.isoformat())} hx-confirm="Delete this note?">&#x2715;</button></div>""" for n in _notes(gid, d.isoformat()))
    add = f"""<form hx-post="/im/in" hx-target="body" hx-swap="none" hx-include="this" class="row" style="margin-top:.4rem"><input type="hidden" name="type" value="finance_note_add"><input type="hidden" name="lvl" value="1"><input type="hidden" name="date" value="{d.isoformat()}"><input name="text" class="module-select grow" placeholder="Note for this day (anything: what it was for, who to call, a reminder)" required><button type="submit" class="btn-icon" title="Add note">+</button></form>"""
    return UI.modal("fin-day", d.strftime("%A, %B %d, %Y"), (rows or '<div class="dim">Nothing scheduled this day.</div>') + f"""<div class="fsect-hd" style="margin-top:.6rem">Notes</div>{notes}{add}""")

# --- Quick add / correction ---

def _quick_add_html(gid: str) -> str:
    accounts = _accounts(gid)
    opts = "".join(f'<option value="{a["id"]}">{_esc(a["label"])}</option>' for a in accounts)
    return f"""<form hx-post="/im/in" hx-target="body" hx-swap="none" hx-include="this" style="display:flex;flex-direction:column;gap:.4rem">
                   <input type="hidden" name="type" value="finance_quick_add"><input type="hidden" name="lvl" value="1">
                   <div style="display:flex;gap:.4rem">
                       <input type="number" name="amount" step="0.01" min="0" placeholder="$ per unit" class="module-select" style="flex:1" required>
                       <input type="number" name="qty" step="any" min="0" value="1" placeholder="x qty" class="module-select" style="width:5rem">
                       <label style="display:flex;align-items:center;gap:.4rem;font-size:.8rem"><input type="checkbox" name="pending" value="1" checked> Not paid yet (bill I owe)</label>
                   </div>
                   <select name="kind" class="module-select"><option value="expense">Expense</option><option value="income">Income</option></select>
                   <select name="account_id" class="module-select">{opts or '<option value="">Add an account first</option>'}</select>
                   <input type="text" name="label" placeholder="e.g. Groceries, Gas" class="module-select" required>
                   <input type="date" name="date" value="{date.today().isoformat()}" class="module-select">
                   <button type="submit" class="button">Add</button>
               </form>"""

def _correction_html(gid: str) -> str:
    accounts = _accounts(gid)
    rows = "".join(f"""<form hx-post="/im/in" hx-target="body" hx-swap="none" hx-include="this" style="display:flex;gap:.3rem;align-items:center;padding:.3rem 0;border-bottom:var(--border-thick) solid var(--border)">
                            <input type="hidden" name="type" value="finance_correction"><input type="hidden" name="lvl" value="1"><input type="hidden" name="account_id" value="{a['id']}">
                            <span style="flex:1;font-size:.8rem">{_esc(a['label'])}</span>
                            <input type="number" name="balance" step="0.01" value="{a['balance']}" class="module-select" style="width:7rem">
                            <input type="date" name="asof" value="{a['asof']}" class="module-select" style="width:9rem">
                            <textarea name="notes" placeholder="Notes (account number tail, login hints, whatever's useful - not encrypted, don't put a full password here)" class="cm-input" rows="2">{_esc(a.get('notes',''))}</textarea>
                            <button type="submit" class="btn-icon">&#x2713;</button>
                        </form>""" for a in accounts)
    return f'<div id="fin-corrections">{rows or "<div class=dim>No accounts yet.</div>"}</div>'

# --- Accounts CRUD ---

def _account_form_html(a: dict = None) -> str:
    a = a or {"id":"","label":"","type":"checking","is_liquid":1,"balance":0,"asof":date.today().isoformat(),"notes":"","credit_limit":"","apr":""}
    return f"""<form hx-post="/im/in" hx-target="body" hx-swap="none" hx-include="this" class="glass" style="padding:.6rem;display:flex;flex-direction:column;gap:.4rem">
                   <input type="hidden" name="type" value="finance_account_save"><input type="hidden" name="lvl" value="1"><input type="hidden" name="id" value="{a['id']}">
                   <input type="text" name="label" value="{_esc(a['label'])}" placeholder="Account name" class="module-select" required>
                   <select name="acct_type" class="module-select">
                       {"".join(f'<option value="{t}" {"selected" if a["type"]==t else ""}>{l}</option>' for t,l in (("checking","Checking"),("savings","Savings"),("credit","Credit Card"),("debt","Loan / Other Debt")))}
                   </select>
                   <label style="display:flex;align-items:center;gap:.4rem;font-size:.8rem"><input type="checkbox" name="is_liquid" value="1" {"checked" if a["is_liquid"] else ""}> Counts as liquid cash (ignored for Credit/Debt - always excluded)</label>
                   <input type="number" name="balance" step="0.01" value="{a['balance']}" placeholder="Current balance" class="module-select">
                   <div style="display:flex;gap:.4rem">
                       <input type="number" name="credit_limit" step="0.01" value="{a['credit_limit']}" placeholder="Credit limit (credit cards only)" class="module-select" style="flex:1">
                       <input type="number" name="apr" step="0.01" value="{a['apr']}" placeholder="APR % (credit/debt only)" class="module-select" style="flex:1">
                   </div>
                   <input type="date" name="asof" value="{a['asof']}" class="module-select">
                   <button type="submit" class="button">Save Account</button>
               </form>"""

def _accounts_list_html(gid: str) -> str:
    rows = ""
    for a in _accounts(gid):
        util = f' <span class="dim tiny">({_money(abs(a["balance"]))} / {_money(a["credit_limit"])} limit, {abs(a["balance"])/a["credit_limit"]*100:.0f}%)</span>' if a["type"]=="credit" and a.get("credit_limit") else ""
        apr = f' <span class="dim tiny">{a["apr"]:.1f}% APR</span>' if a.get("apr") else ""
        notes_ind = f' <span class="dim tiny" title="{_esc(a["notes"])}">&#x1F4DD;</span>' if a.get("notes") else ""
        asof_ind = f' <span class="dim tiny">as of {a["asof"]}</span>' if a.get("asof") else ""
        rows += f"""<div class="glass" style="padding:.5rem .7rem;margin-bottom:.3rem;display:flex;align-items:center;gap:.5rem">
                        <span style="flex:1;font-weight:600">{_esc(a['label'])}{notes_ind}</span><span class="dim tiny">{a['type']}</span>
                        <span style="color:{'#00ffa2' if a['balance']>=0 else '#ff5f5f'}">{_money(a['balance'])}</span>{util}{apr}
                        <button class="cm-qbtn" hx-post="/im/in" hx-target="body" hx-swap="none" hx-vals='{json.dumps({"type":"finance_account_form","lvl":1,"id":a["id"]})}'>Edit</button>
                        <button class="cm-qbtn" style="color:#ff5f5f" hx-post="/im/in" hx-target="body" hx-swap="none" hx-vals='{json.dumps({"type":"finance_account_delete","lvl":1,"id":a["id"]})}' hx-confirm="Delete this account? Its entries stay but become orphaned.">&#x2715;</button>
                    </div>"""
    return f'<div id="fin-accounts-list">{rows or "<div class=dim>No accounts yet - add one below.</div>"}</div>'

# --- Recurring CRUD ---

def _recurring_form_html(gid: str, rec: dict = None) -> str:
    rec = rec or {"id":"","label":"","kind":"expense","account_id":"","to_account_id":"","amount":0,"is_estimate":0,"frequency":"monthly","anchor_date":date.today().isoformat(),"day1":1,"day2":15,"notify":1,"notify_days_before":2,"category":"","active":1,"auto_pay":0}
    accounts = _accounts(gid)
    opts = lambda sel: "".join(f'<option value="{a["id"]}" {"selected" if a["id"]==sel else ""}>{_esc(a["label"])}</option>' for a in accounts)
    return f"""<form hx-post="/im/in" hx-target="body" hx-swap="none" hx-include="this" class="glass" style="padding:.6rem;display:flex;flex-direction:column;gap:.4rem">
                   <input type="hidden" name="type" value="finance_recurring_save"><input type="hidden" name="lvl" value="1"><input type="hidden" name="id" value="{rec['id']}">
                   <input type="text" name="label" value="{_esc(rec['label'])}" placeholder="e.g. Rent, Paycheck, Card Payment" class="module-select" required>
                   <select name="kind" class="module-select">{"".join(f'<option value="{k}" {"selected" if rec["kind"]==k else ""}>{l}</option>' for k,l in (("expense","Bill / Expense (leaves an account)"),("income","Income (arrives in an account)"),("wage","Hourly Wage (paid per worked weekday)"),("transfer","Transfer / Card Payment (moves between two of your own accounts)")))}</select>
                   <label class="dim">From / affected account<select name="account_id" class="module-select">{opts(rec["account_id"])}</select></label>
                   <label class="dim">To account (transfer only)<select name="to_account_id" class="module-select"><option value="">-</option>{opts(rec["to_account_id"])}</select></label>
                   <div style="display:flex;gap:.4rem">
                       <input type="number" name="amount" step="0.01" min="0" value="{rec['amount']}" placeholder="Amount" class="module-select" style="flex:1">
                       <label style="display:flex;align-items:center;gap:.3rem;font-size:.78rem;white-space:nowrap"><input type="checkbox" name="is_estimate" value="1" {"checked" if rec["is_estimate"] else ""}> Estimate</label>
                   </div>
                   <div style="display:flex;gap:.4rem">
                       <input type="number" name="hourly_rate" step="0.01" value="{rec.get('hourly_rate') or ''}" placeholder="Hourly rate (wage kind only)" class="module-select" style="flex:1">
                       <input type="number" name="hours_per_day" step="0.25" value="{rec.get('hours_per_day') or 8}" placeholder="Hours/weekday" class="module-select" style="flex:1">
                       <input type="number" name="deduction_pct" step="0.0001" value="{rec.get('deduction_pct') or 0}" placeholder="Deduction % (taxes etc)" class="module-select" style="flex:1">
                   </div>
                   <select name="frequency" class="module-select">{"".join(f'<option value="{f}" {"selected" if rec["frequency"]==f else ""}>{l}</option>' for f,l in (("weekly","Weekly"),("biweekly","Every 2 weeks"),("semimonthly","Twice a month (e.g. 1st & 15th)"),("monthly","Monthly"),("yearly","Yearly")))}</select>
                   <div style="display:flex;gap:.4rem">
                       <label class="dim" style="flex:1">Starts / anchor date<input type="date" name="anchor_date" value="{rec['anchor_date']}" class="module-select"></label>
                       <label class="dim" style="flex:1">Day of month<input type="number" name="day1" min="1" max="31" value="{rec['day1']}" class="module-select"></label>
                       <label class="dim" style="flex:1">2nd day (semimonthly)<input type="number" name="day2" min="1" max="31" value="{rec['day2']}" class="module-select"></label>
                   </div>
                   <input type="text" name="category" value="{_esc(rec['category'])}" placeholder="Category (optional)" class="module-select">
                   <label style="display:flex;align-items:center;gap:.4rem;font-size:.8rem">
                       <input type="checkbox" name="auto_pay" value="1" {"checked" if rec["auto_pay"] else ""}> This happens automatically (no action needed from you when it hits) - separate from whether you get notified below
                   </label>
                   <div style="display:flex;gap:.6rem;align-items:center">
                       <label style="display:flex;align-items:center;gap:.3rem;font-size:.8rem"><input type="checkbox" name="notify" value="1" {"checked" if rec["notify"] else ""}> Notify me</label>
                       <label class="dim" style="font-size:.8rem">days before<input type="number" name="notify_days_before" min="0" max="30" value="{rec['notify_days_before']}" class="module-select" style="width:4rem"></label>
                       <label style="display:flex;align-items:center;gap:.3rem;font-size:.8rem;margin-left:auto"><input type="checkbox" name="active" value="1" {"checked" if rec["active"] else ""}> Active</label>
                   </div>
                   <button type="submit" class="button">Save Recurring Item</button>
               </form>"""

def _recurring_list_html(gid: str) -> str:
    rows = ""
    for r in _recurring(gid):
        badge = f'<span class="status-badge" style="color:{"#00ffa2" if r["kind"]=="income" else "#ffaa44" if r["kind"]=="transfer" else "#ff8c8c"}">{r["kind"]}</span>'
        auto_badge = '<span class="dim tiny">auto</span>' if r["auto_pay"] else '<span class="dim tiny">manual</span>'
        est = " ~est" if r["is_estimate"] else ""
        rows += f"""<div class="glass" style="padding:.5rem .7rem;margin-bottom:.3rem;display:flex;align-items:center;gap:.5rem;opacity:{1 if r['active'] else .5}">
                        <span style="flex:1;font-weight:600">{_esc(r['label'])}</span>{badge}{auto_badge}
                        <span class="dim tiny">{r['frequency']}</span>
                        <span>{_money(r['amount'])}{est}</span>
                        <span class="dim tiny">{_display_day(r)}</span>
                        <button class="cm-qbtn" hx-post="/im/in" hx-target="body" hx-swap="none" hx-vals='{json.dumps({"type":"finance_recurring_form","lvl":1,"id":r["id"]})}'>Edit</button>
                        <button class="cm-qbtn" style="color:#ff5f5f" hx-post="/im/in" hx-target="body" hx-swap="none" hx-vals='{json.dumps({"type":"finance_recurring_delete","lvl":1,"id":r["id"]})}' hx-confirm="Delete this recurring item?">&#x2715;</button>
                    </div>"""
    return f'<div id="fin-recurring-list">{rows or "<div class=dim>No recurring items yet.</div>"}</div>'


# --- Recurring as a table: every item one row, every value its own cell, saved when the cell changes (Tab moves on); filter, and fill one column for the rows shown ---

_KINDS = (("expense", "Bill"), ("income", "Income"), ("wage", "Wage"), ("transfer", "Transfer"))
_FREQS = (("weekly", "Weekly"), ("biweekly", "2 weeks"), ("semimonthly", "2x month"), ("monthly", "Monthly"), ("yearly", "Yearly"))
_REC_COLS = {"label": "text", "kind": "kind", "account_id": "account", "amount": "money", "is_estimate": "bool", "frequency": "freq", "day1": "day", "day2": "day", "anchor_date": "date", "auto_pay": "bool", "notify": "bool", "notify_days_before": "int", "category": "text", "active": "bool"}

async def _rec_view(request) -> dict: return {"view": "table", "q": "", "kind": "", **(await ENV["get_state"](request, scope="user", namespace="finance", key="rec_view") or {})}

def _rec_value(col: str, v, accounts: dict):
    """A cell's text as the stored value; ValueError when it cannot be one (the cell is marked and nothing is saved)."""
    t, v = _REC_COLS[col], "" if v is None else str(v).strip()
    if t == "bool": return 1 if v in ("1", "on", "true", "yes", "x") else 0
    if t == "money":
        n = _num(v)
        if n is None: raise ValueError("not an amount")
        return abs(n)
    if t in ("int", "day"):
        n = int(v)
        if t == "day" and not 1 <= n <= 31: raise ValueError("day 1-31")
        return n
    if t == "date": return date.fromisoformat(v).isoformat()
    if t == "kind" and v not in dict(_KINDS): raise ValueError("kind")
    if t == "freq" and v not in dict(_FREQS): raise ValueError("frequency")
    if t == "account" and v not in accounts: raise ValueError("no such account")
    if col == "label" and not v: raise ValueError("a name is needed")
    return v

def _rec_cell(r: dict, col: str, accounts: dict) -> str:
    t, v = _REC_COLS[col], r[col]
    attrs = f"""name="v" class="module-select fin-cell fin-c-{t}" hx-post="/im/in" hx-target="body" hx-swap="none" hx-trigger="change" hx-vals='{json.dumps({"type": "finance_rec_cell", "lvl": 1, "id": r["id"], "col": col})}'"""
    if t == "bool": return f"""<input type="checkbox" value="1" {"checked" if v else ""} {attrs}>"""
    if t in ("kind", "freq", "account"): return f"""<select {attrs}>{"".join(f'<option value="{k}"{" selected" if k == v else ""}>{_esc(l)}</option>' for k, l in (_KINDS if t == "kind" else _FREQS if t == "freq" else [(k, a["label"]) for k, a in accounts.items()]))}</select>"""
    kind = {"money": 'type="number" step="0.01" min="0"', "int": 'type="number" min="0" max="30"', "day": 'type="number" min="1" max="31"', "date": 'type="date"'}.get(t, 'type="text"')
    return f"""<input {kind} value="{_esc(v if v is not None else "")}" {attrs}>"""

def _rec_rows(gid: str, q: str, kind: str) -> list:
    ql = q.lower()
    return [r for r in _recurring(gid) if (not kind or r["kind"] == kind) and (not ql or ql in f"""{r["label"]} {r["category"]}""".lower())]

def _recurring_table_html(gid: str, v: dict, msg: str = "") -> str:
    rows, accounts = _rec_rows(gid, v["q"], v["kind"]), _account_map(gid)
    head = "".join(f"<th>{h}</th>" for h in ("Name", "Kind", "Account", "Amount", "~", "How often", "Day", "2nd day", "From date", "Auto", "Notify", "days", "Category", "Active", ""))
    body = "".join(f"""<tr style="opacity:{1 if r["active"] else .55}">{"".join(f"<td>{_rec_cell(r, c, accounts)}</td>" for c in _REC_COLS)}<td id="fin-rc-{r["id"]}" class="dim tiny"></td></tr>""" for r in rows)
    chips = "".join(f"""<button class="chip"{' style="background:var(--accent);color:var(--bg)"' if v["kind"] == k else ""} {_vals("rec_view", kind="" if v["kind"] == k else k)}>{l}</button>""" for k, l in _KINDS)
    fill_cols = "".join(f'<option value="{c}">{h}</option>' for c, h in (("day1", "Day"), ("day2", "2nd day"), ("frequency", "How often"), ("account_id", "Account"), ("auto_pay", "Auto"), ("notify", "Notify"), ("notify_days_before", "Notify days"), ("is_estimate", "Estimate"), ("active", "Active"), ("category", "Category"), ("anchor_date", "From date")))
    fill = f"""<form class="row" {_vals("rec_fill", ids=",".join(r["id"] for r in rows))} hx-include="this" hx-confirm="Set this value on all {len(rows)} rows shown?"><span class="dim tiny">Fill</span><select name="col" class="module-select" style="width:auto">{fill_cols}</select><input name="v" class="module-select" placeholder="value" title="Yes / no columns: 1 or 0. How often: weekly, biweekly, semimonthly, monthly, yearly. Account: its name. Date: YYYY-MM-DD" style="width:9rem"><button type="submit" class="ui-btn">for the {len(rows)} shown</button></form>"""
    return f"""<div class="row">{chips}<span class="grow"></span>{fill}</div>
               {f'<div class="info-bar">{msg}</div>' if msg else ""}<div class="dim tiny" style="margin:.2rem 0">Each cell is saved when you leave it (Tab moves to the next). A value that cannot be used is not saved; the row's last column says why.</div>
               <div style="overflow-x:auto"><table class="data-table fin-rec-table"><thead><tr>{head}</tr></thead><tbody>{body or '<tr><td colspan="15" class="dim">No recurring items match.</td></tr>'}</tbody></table></div>"""

def _panel_recurring_body(gid: str, v: dict) -> str:
    """Table (every value editable in place) or Cards (one item at a time, the full form); adding a new item uses the form in both."""
    switch = "".join(f"""<button class="chip"{' style="background:var(--accent);color:var(--bg)"' if v["view"] == k else ""} {_vals("rec_view", view=k)}>{l}</button>""" for k, l in (("table", "Table"), ("cards", "Cards")))
    form = f"""<details class="sec"{" open" if v["view"] == "cards" else ""}><summary>Add / Edit Recurring Item</summary><div id="fin-recurring-form">{_recurring_form_html(gid)}</div></details>"""
    if v["view"] == "cards": return f"""<div class="row">{switch}</div>{_recurring_list_html(gid)}{form}"""
    return f"""<div class="row">{switch}<input name="q" value="{_esc(v["q"])}" class="module-select" placeholder="Filter: name or category" style="width:14rem" {_vals("rec_view")} hx-trigger="keyup changed delay:400ms" hx-include="this"></div>
               <div id="fin-rec-table">{_recurring_table_html(gid, v)}</div>{form}"""

async def _h_rec_cell(request, payload, imr):
    """One cell: stored at once and the projections rebuilt; the row's last cell says saved, or the cell is marked when the value cannot be used."""
    gid, rid, col = await _active_group(request), payload["id"], payload["col"]
    if col not in _REC_COLS: return imr
    try: val = _rec_value(col, payload.get("v"), _account_map(gid))
    except (ValueError, TypeError) as e: return imr.oob(f"""<span style="color:#ff5f5f">{_esc(col)}: {_esc(str(e) or "not a value")}</span>""", f"fin-rc-{rid}")
    conn = _conn(gid)
    conn.execute(f"UPDATE recurring SET {col}=? WHERE id=?", (val, rid))   # col is one of _REC_COLS' keys (checked above)
    conn.commit()
    conn.close()
    _materialize(gid)
    return imr.oob("&#x2713; saved", f"fin-rc-{rid}")

async def _h_rec_view(request, payload, imr):
    v = await _rec_view(request)
    v.update({k: payload[k] for k in ("view", "q", "kind") if k in payload})
    await ENV["set_state"](request, v, scope="user", namespace="finance", key="rec_view")
    gid = await _active_group(request)
    if "view" in payload: return imr.oob(_panel_recurring_body(gid, v), "fin-rec-body")
    return imr.oob(_recurring_table_html(gid, v), "fin-rec-table")

async def _h_rec_fill(request, payload, imr):
    """One column set to one value on every row shown (the filter decides which); an account may be given by its name."""
    gid, col, ids = await _active_group(request), payload.get("col", ""), [i for i in str(payload.get("ids", "")).split(",") if i]
    accounts, v = _account_map(gid), await _rec_view(request)
    raw = next((k for k, a in accounts.items() if a["label"].lower() == str(payload.get("v", "")).strip().lower()), payload.get("v")) if col == "account_id" else payload.get("v")
    try: val = _rec_value(col, raw, accounts) if col in _REC_COLS else None
    except (ValueError, TypeError) as e: return imr.oob(_recurring_table_html(gid, v, f"""Nothing changed - {_esc(col)}: {_esc(str(e) or "not a value")}"""), "fin-rec-table")
    if col in _REC_COLS and ids:
        conn = _conn(gid)
        conn.executemany(f"UPDATE recurring SET {col}=? WHERE id=?", [(val, i) for i in ids])
        conn.commit()
        conn.close()
        _materialize(gid)
    return imr.oob(_recurring_table_html(gid, v, f"{len(ids)} row(s) set."), "fin-rec-table")

# --- Panels ---

async def _panel_calendar(request, gid):
    today = date.today()
    ym = await ENV["get_state"](request, scope="user", namespace="finance", key="cal_ym") or {"y": today.year, "m": today.month}
    return f"""<div style="padding:.9rem;height:100%;overflow-y:auto;box-sizing:border-box">
                   {_calendar_html(gid, ym["y"], ym["m"])}
                   <div class="fsect-hd">Pending Bills</div><div id="fin-pending">{_pending_html(gid)}</div>
                   <div class="fsect-hd" style="margin-top:1rem">Quick Add</div>
                   {_quick_add_html(gid)}
                   <div class="fsect-hd" style="margin-top:1rem">Correct a Balance</div>
                   <p class="dim tiny">Set what an account actually has right now - everything projected forward recalculates from this point. No need to find and fix individual past entries.</p>
                   {_correction_html(gid)}
               </div>"""

def _panel_upcoming(gid, days): return f'<div style="padding:.9rem;height:100%;overflow-y:auto;box-sizing:border-box"><div id="fin-upcoming">{_upcoming_html(gid, days)}</div></div>'
def _panel_import(gid): return f'<div style="padding:.9rem;height:100%;overflow-y:auto;box-sizing:border-box"><div id="fin-import">{_import_html(gid)}</div></div>'

def _panel_accounts(gid): return f'<div style="padding:.9rem;height:100%;overflow-y:auto;box-sizing:border-box">{_accounts_list_html(gid)}<div class="fsect-hd" style="margin-top:1rem">Add / Edit Account</div><div id="fin-account-form">{_account_form_html()}</div></div>'
def _panel_recurring(gid, v): return f'<div style="padding:.9rem;height:100%;overflow-y:auto;box-sizing:border-box"><div id="fin-rec-body">{_panel_recurring_body(gid, v)}</div></div>'

def _panel_settings(request, gid, warn=""):
    groups = _user_groups(request.state.user.username)
    g_opts = "".join(f'<option value="{g["id"]}" {"selected" if g["id"]==gid else ""}>{_esc(g["label"])}</option>' for g in groups)
    cur = _load_groups().get(gid, {})
    members = ", ".join(cur.get("members", []))
    return f"""<div style="padding:.9rem;height:100%;overflow-y:auto;box-sizing:border-box;max-width:36rem">
                   <div class="fsect-hd">Active Group</div>
                   <div style="display:flex;gap:.4rem;align-items:center">
                       <select class="module-select" style="flex:1;margin:0" hx-post="/im/in" hx-target="#finance-panel" hx-swap="innerHTML" hx-trigger="change" hx-vals='{{"type":"finance_group_switch","lvl":1}}' hx-include="this" name="gid">{g_opts}</select>
                       <button type="button" class="cm-qbtn" hx-post="/im/in" hx-target="#finance-panel" hx-swap="innerHTML" hx-vals='{{"type":"finance_group_set_default","lvl":1,"gid":"{gid}"}}'>Set as Default</button>
                   </div>
                   <form hx-post="/im/in" hx-target="#finance-panel" hx-swap="innerHTML" hx-include="this" style="display:flex;gap:.4rem;margin-top:.5rem">
                       <input type="hidden" name="type" value="finance_group_create"><input type="hidden" name="lvl" value="1">
                       <input type="text" name="label" placeholder="New group name" class="module-select" style="flex:1">
                       <button type="submit" class="button">+ Create Group</button>
                   </form>
                   <button type="button" class="cm-qbtn" style="color:#ff5f5f;margin-top:.4rem" hx-post="/im/in" hx-target="#finance-panel" hx-swap="innerHTML" hx-vals='{{"type":"finance_group_leave","lvl":1,"gid":"{gid}"}}' hx-confirm="Leave &#39;{_esc(cur.get('label',gid))}&#39;? If you&#39;re the only member, all its data is deleted permanently.">Leave / Delete This Group</button>
                   <div class="fsect-hd" style="margin-top:1rem">Group Members</div>
                   <p class="dim tiny">Only real usernames on this server are accepted - a typo is silently dropped rather than granting access to nobody.</p>
                   <form hx-post="/im/in" hx-target="#finance-panel" hx-swap="innerHTML" hx-include="this" style="display:flex;gap:.4rem">
                       <input type="hidden" name="type" value="finance_group_members_save"><input type="hidden" name="lvl" value="1"><input type="hidden" name="gid" value="{gid}">
                       <input type="text" name="members" value="{_esc(members)}" placeholder="comma-separated usernames" class="module-select" style="flex:1">
                       <button type="submit" class="button">Save</button>
                   </form>{warn}
                   <div class="fsect-hd" style="margin-top:1rem">Low Balance Warning</div>
                   <form hx-post="/im/in" hx-target="body" hx-swap="none" hx-include="this" style="display:flex;gap:.4rem;align-items:center">
                       <input type="hidden" name="type" value="finance_threshold_save"><input type="hidden" name="lvl" value="1"><input type="hidden" name="gid" value="{gid}">
                       <input type="number" name="threshold" step="1" value="{cur.get('low_balance_threshold',100)}" class="module-select" style="width:8rem">
                       <button type="submit" class="button">Save</button>
                   </form>
                   <div class="fsect-hd" style="margin-top:1rem">Export</div>
                   <a class="ui-btn" href="{_P}/export/{gid}" download="{gid}.db">&#x2B07; Download SQLite file</a>
               </div>"""

async def _render_panel(request, state):
    gid = await _active_group(request)
    active = state.get("active", "calendar")
    if active == "accounts": return state, _panel_accounts(gid)
    if active == "recurring": return state, _panel_recurring(gid, await _rec_view(request))
    if active == "settings": return state, _panel_settings(request, gid)
    if active == "breakdown": return state, _panel_breakdown(gid)
    if active == "upcoming": return state, _panel_upcoming(gid, await _up_days(request))
    if active == "plan": return state, _panel_plan(gid, await _plan_days(request))
    if active == "import": return state, _panel_import(gid)
    return state, await _panel_calendar(request, gid)

# --- Notification loop ---

async def _run_notify_pass():
    """Checks every active group's recurring items and low-balance threshold. Recurring-item reminders were already throttled to once/day per item (last_notified_date on the recurring row). Low-balance is now throttled the same way, tracked per-group in groups.json."""
    today = date.today()
    groups = _load_groups()
    for gid, g in groups.items():
        try:
            _materialize(gid)
            balances = _balances_at(gid, today)
            liquid = _liquid_total(balances)
            threshold = g.get("low_balance_threshold", 100.0)
            for rec in _recurring(gid):
                if not (rec["active"] and rec["notify"]): continue
                occs = _occurrences(rec, today, today + timedelta(days=rec["notify_days_before"] or 0))
                if occs and rec.get("last_notified_date") != today.isoformat():
                    due = occs[0]
                    for member in g.get("members", []): await ENV["send_push"](member, "Upcoming: " + rec["label"], f"{rec['label']} ({_money(rec['amount'])}) due {due.isoformat()}", url=_P)
                    conn = _conn(gid); conn.execute("UPDATE recurring SET last_notified_date=? WHERE id=?", (today.isoformat(), rec["id"])); conn.commit(); conn.close()
            if liquid < threshold and g.get("last_low_balance_notify") != today.isoformat():
                for member in g.get("members", []): await ENV["send_push"](member, "Low balance warning", f"{g.get('label','Finances')}: liquid cash is {_money(liquid)}, below your {_money(threshold)} threshold.", url=_P)
                groups[gid]["last_low_balance_notify"] = today.isoformat()
                _save_groups(groups)
        except Exception as e: print(f"[finance] notify pass error for group {gid}: {e}")

async def _notify_loop():
    while True:
        try: await _run_notify_pass()
        except Exception as e: print(f"[finance] notify loop error: {e}")
        await asyncio.sleep(3600)

# --- Init ---

def init_module(env: dict):
    global ENV, UI, BI, IM, TM
    ENV.update(env)
    UI = ENV["templates"].env.globals.get("UI")
    BI = ENV["tools"]["built_ins"]
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    IM = ENV["InterfaceManager"](nesting_level=1, db_path="finance_im.db")
    TM = BI.TabManager(namespace="finance", tab_bar_id="fin-tab-bar", content_id="finance-panel", render_content_fn=_render_panel, intent_prefix="finance", IM=IM, scope="user", nesting_level=1, allow_new=False, closable=False, empty={"tabs": {"calendar":{"id":"calendar","order":0,"label":"Calendar","icon":"&#x1F4C5;"}, "upcoming":{"id":"upcoming","order":0.5,"label":"Upcoming","icon":"&#x1F4CB;"}, "plan":{"id":"plan","order":0.7,"label":"Plan","icon":"&#x1F4C8;"}, "accounts":{"id":"accounts","order":1,"label":"Accounts","icon":"&#x1F3E6;"}, "breakdown":{"id":"breakdown","order":2,"label":"Breakdown","icon":"&#x1F4CA;"}, "recurring":{"id":"recurring","order":3,"label":"Recurring","icon":"&#x1F501;"}, "import":{"id":"import","order":3.5,"label":"Import","icon":"&#x1F4E5;"}, "settings":{"id":"settings","order":4,"label":"Settings","icon":"&#x2699;"}}, "active":"calendar"})
    IM.scripts.update({
        "finance_calendar_nav": [_h_calendar_nav], "finance_day_open": [_h_day_open],
        "finance_quick_add": [_h_quick_add], "finance_correction": [_h_correction],
        "finance_entry_save": [_h_entry_save], "finance_entry_delete": [_h_entry_delete],
        "finance_account_form": [_h_account_form], "finance_account_save": [_h_account_save], "finance_account_delete": [_h_account_delete],
        "finance_recurring_form": [_h_recurring_form], "finance_recurring_save": [_h_recurring_save], "finance_recurring_delete": [_h_recurring_delete],
        "finance_pending_pay_now": [_h_pending_pay_now], "finance_pending_mark_paid": [_h_pending_mark_paid],
        "finance_group_create": [_h_group_create], "finance_group_set_default": [_h_group_set_default], "finance_group_leave": [_h_group_leave],
        "finance_group_switch": [_h_group_switch], "finance_group_members_save": [_h_group_members_save], "finance_threshold_save": [_h_threshold_save],
        "finance_note_add": [_h_note_add], "finance_note_delete": [_h_note_delete], "finance_upcoming_days": [_h_upcoming_days], "finance_up_paid": [_h_up_paid], "finance_up_skip": [_h_up_skip],
        "finance_import_read": [_h_import_read], "finance_import_go": [_h_import_go], "finance_import_undo": [_h_import_undo],
        "finance_plan_days": [_h_plan_days], "finance_plan_whatif": [_h_plan_whatif], "finance_plan_add": [_h_plan_add],
        "finance_rec_cell": [_h_rec_cell], "finance_rec_view": [_h_rec_view], "finance_rec_fill": [_h_rec_fill]})
    ENV["register_service"]("finance", {"due_items": due_items, "command": {"help": _CMD_HELP, "parse": _cmd_parse, "run": _cmd_run, "aliases": ["fin"]}})   # Muninn's Today (and any summary view) lists bills that need you; @finance lines in Muninn captures add entries
    ENV["register_startup"](_notify_loop)   # init runs before the server's event loop exists; the loop starts with the server
    print("[finance] ready")

# --- Intent handlers ---

async def _refresh_calendar(request, gid, imr):
    ym = await ENV["get_state"](request, scope="user", namespace="finance", key="cal_ym") or {"y": date.today().year, "m": date.today().month}
    imr.oob(_calendar_html(gid, ym["y"], ym["m"]), "fin-calendar", swap="outerHTML")
    imr.oob(_upcoming_html(gid, await _up_days(request)), "fin-upcoming")

async def _h_calendar_nav(request, payload, imr):
    await ENV["set_state"](request, {"y": int(payload.get("year")), "m": int(payload.get("month"))}, scope="user", namespace="finance", key="cal_ym")
    gid = await _active_group(request)
    imr.oob(_calendar_html(gid, int(payload.get("year")), int(payload.get("month"))), "fin-calendar", swap="outerHTML")
    return imr

async def _h_day_open(request, payload, imr):
    gid = await _active_group(request)
    imr.oob(_day_detail_html(gid, date.fromisoformat(payload.get("date"))), "fin-modal")
    return imr

async def _h_correction(request, payload, imr):
    gid = await _active_group(request)
    conn = _conn(gid)
    conn.execute("UPDATE accounts SET balance=?, asof=? WHERE id=?", (float(payload.get("balance",0) or 0), payload.get("asof", date.today().isoformat()), payload.get("account_id","")))
    conn.commit(); conn.close()
    await _refresh_calendar(request, gid, imr)
    imr.oob(_correction_html(gid), "fin-corrections", swap="outerHTML")
    return imr

async def _h_entry_save(request, payload, imr):
    """Editing an entry's label/amount and hitting save also confirms it - a correction implies the person is now vouching for the number."""
    gid = await _active_group(request)
    eid = payload.get("id","")
    conn = _conn(gid)
    conn.execute("UPDATE entries SET label=?, amount=?, confirmed=1 WHERE id=?", (payload.get("label","").strip(), float(payload.get("amount",0) or 0), eid))
    conn.commit(); conn.close()
    e = _entry(gid, eid)
    if e: imr.oob(_day_detail_html(gid, date.fromisoformat(e["date"])), "fin-modal")
    await _refresh_calendar(request, gid, imr)
    return imr

async def _h_entry_delete(request, payload, imr):
    """Deleting an unconfirmed recurring-generated entry records a per-occurrence exception so it doesn't reappear on the next materialize pass - the rest of that recurring item's schedule is untouched. Deleting a manual or already-confirmed entry just removes the row."""
    gid = await _active_group(request)
    eid = payload.get("id","")
    e = _entry(gid, eid)
    if not e: return imr
    conn = _conn(gid)
    if e["recurring_id"] and not e["confirmed"]: conn.execute("INSERT OR IGNORE INTO exceptions (recurring_id,date) VALUES (?,?)", (e["recurring_id"], e["date"]))
    conn.execute("DELETE FROM entries WHERE id=?", (eid,))
    if e["linked_entry_id"]: conn.execute("DELETE FROM entries WHERE id=?", (e["linked_entry_id"],))
    conn.commit(); conn.close()
    imr.oob(_day_detail_html(gid, date.fromisoformat(e["date"])), "fin-modal")
    await _refresh_calendar(request, gid, imr)
    return imr

async def _h_account_form(request, payload, imr):
    gid = await _active_group(request)
    a = next((x for x in _accounts(gid) if x["id"] == payload.get("id","")), None)
    return imr.oob(_account_form_html(a), "fin-account-form", swap="outerHTML")

async def _h_account_save(request, payload, imr):
    gid = await _active_group(request)
    aid = payload.get("id","") or uuid.uuid4().hex[:10]
    acct_type = payload.get("acct_type","checking")
    is_debtlike = acct_type in ("credit","debt")
    bal = float(payload.get("balance",0) or 0)
    if is_debtlike: bal = -abs(bal)  # a debt is always owed, never entered as positive by mistake
    is_liquid = 0 if is_debtlike else (1 if payload.get("is_liquid") else 0)
    limit_raw, apr_raw = payload.get("credit_limit",""), payload.get("apr","")
    conn = _conn(gid)
    conn.execute("INSERT OR REPLACE INTO accounts (id,label,type,is_liquid,balance,asof,notes,credit_limit,apr) VALUES (?,?,?,?,?,?,?,?,?)",
                 (aid, payload.get("label","").strip(), acct_type, is_liquid, bal, payload.get("asof", date.today().isoformat()), "", float(limit_raw) if limit_raw not in ("",None) else None, float(apr_raw) if apr_raw not in ("",None) else None))
    conn.commit(); conn.close()
    imr.oob(_accounts_list_html(gid), "fin-accounts-list", swap="outerHTML")
    imr.oob(_account_form_html(), "fin-account-form", swap="outerHTML")
    return imr

async def _h_account_delete(request, payload, imr):
    gid = await _active_group(request)
    conn = _conn(gid); conn.execute("DELETE FROM accounts WHERE id=?", (payload.get("id",""),)); conn.commit(); conn.close()
    return imr.oob(_accounts_list_html(gid), "fin-accounts-list", swap="outerHTML")

async def _h_recurring_form(request, payload, imr):
    gid = await _active_group(request)
    r = next((x for x in _recurring(gid) if x["id"] == payload.get("id","")), None)
    return imr.oob(_recurring_form_html(gid, r), "fin-recurring-form", swap="outerHTML")

async def _h_recurring_save(request, payload, imr):
    gid = await _active_group(request)
    rid = payload.get("id","") or uuid.uuid4().hex[:10]
    conn = _conn(gid)
    conn.execute("INSERT OR REPLACE INTO recurring (id,label,kind,account_id,to_account_id,amount,is_estimate,frequency,anchor_date,day1,day2,notify,notify_days_before,category,active,last_notified_date,auto_pay,hourly_rate,hours_per_day,deduction_pct) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",(
        rid,
        payload.get("label", "").strip(),
        payload.get("kind", "expense"),
        payload.get("account_id", ""),
        payload.get("to_account_id", "") or None,
        float(payload.get("amount", 0) or 0),
        1 if payload.get("is_estimate") else 0,
        payload.get("frequency", "monthly"),
        payload.get("anchor_date", date.today().isoformat()),
        int(payload.get("day1", 1) or 1),
        int(payload.get("day2", 15) or 15),
        1 if payload.get("notify") else 0,
        int(payload.get("notify_days_before", 2) or 2),
        payload.get("category", "").strip(),
        1 if payload.get("active") else 0,
        None,
        1 if payload.get("auto_pay") else 0,
        float(payload.get("hourly_rate")) if payload.get("hourly_rate") not in ("", None) else None,
        float(payload.get("hours_per_day")) if payload.get("hours_per_day") not in ("", None) else None,
        float(payload.get("deduction_pct")) if payload.get("deduction_pct") not in ("", None) else None,),)
    # conn.execute("INSERT OR REPLACE INTO recurring (id,label,kind,account_id,to_account_id,amount,is_estimate,frequency,anchor_date,day1,day2,notify,notify_days_before,category,active,last_notified_date,auto_pay,hourly_rate,hours_per_day,deduction_pct) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
    #              (rid, payload.get("label","").strip(), payload.get("kind","expense"), payload.get("account_id",""), payload.get("to_account_id","") or None,
    #               float(payload.get("amount",0) or 0), 1 if payload.get("is_estimate") else 0, payload.get("frequency","monthly"), payload.get("anchor_date", date.today().isoformat()),
    #               int(payload.get("day1",1) or 1), int(payload.get("day2",15) or 15), 1 if payload.get("notify") else 0, int(payload.get("notify_days_before",2) or 2),
    #               payload.get("category","").strip(), 1 if payload.get("active") else 0, None, 1 if payload.get("auto_pay") else 0,
    #               float(payload.get("hourly_rate")) if payload.get("hourly_rate") not in ("",None) else None, float(payload.get("hours_per_day")) if payload.get("hours_per_day") not in ("",None) else None))
    conn.commit(); conn.close()
    _materialize(gid)
    imr.oob(_recurring_list_html(gid), "fin-recurring-list", swap="outerHTML")
    imr.oob(_recurring_form_html(gid), "fin-recurring-form", swap="outerHTML")
    return imr.oob(_recurring_table_html(gid, await _rec_view(request)), "fin-rec-table")   # the Table view, when it is the one open

async def _h_recurring_delete(request, payload, imr):
    gid = await _active_group(request)
    conn = _conn(gid); conn.execute("DELETE FROM recurring WHERE id=?", (payload.get("id",""),)); conn.commit(); conn.close()
    _materialize(gid)
    return imr.oob(_recurring_list_html(gid), "fin-recurring-list", swap="outerHTML")

async def _h_group_switch(request, payload, imr):
    await ENV["set_state"](request, payload.get("gid",""), scope="user", namespace="finance", key="active_group")
    return imr.raw(_panel_settings(request, payload.get("gid","")))

async def _h_group_members_save(request, payload, imr):
    groups = _load_groups()
    gid = payload.get("gid","")
    if gid not in groups or request.state.user.username not in groups[gid].get("members", []): return imr
    requested = [m.strip() for m in payload.get("members","").split(",") if m.strip()]
    real = _real_usernames()
    valid = [m for m in requested if m in real]
    if request.state.user.username not in valid: valid.append(request.state.user.username)
    rejected = [m for m in requested if m not in real]
    newly_added = set(valid) - set(groups[gid].get("members", []))
    groups[gid]["members"] = valid
    _save_groups(groups)
    for member in newly_added:
        if member != request.state.user.username: await ENV["send_push"](member, "Added to a finance group", f"You were added to '{groups[gid]['label']}'.", url=f"{_P}/?join_group={gid}")
    warn = f'<div style="color:#ffaa44;font-size:.75rem;margin-top:.3rem">Not added (no matching username on this server): {", ".join(rejected)}</div>' if rejected else ""
    return imr.raw(_panel_settings(request, gid, warn))

async def _h_threshold_save(request, payload, imr):
    groups = _load_groups()
    gid = payload.get("gid","")
    if gid in groups and request.state.user.username in groups[gid].get("members", []):
        groups[gid]["low_balance_threshold"] = float(payload.get("threshold", 100) or 100)
        _save_groups(groups)
    return imr

async def _h_quick_add(request, payload, imr):
    """amount x qty, signed by kind; "Not paid yet" adds it as a pending bill (unconfirmed) instead of money already spent."""
    gid = await _active_group(request)
    sign = 1 if payload.get("kind") == "income" else -1
    amt = float(payload.get("amount",0) or 0) * float(payload.get("qty",1) or 1)
    conn = _conn(gid)
    conn.execute("INSERT INTO entries VALUES (?,?,?,?,?,?,?,?,?,?)", (uuid.uuid4().hex[:10], payload.get("account_id",""), payload.get("date", date.today().isoformat()), payload.get("label","").strip(), sign*abs(amt), "", 0, None, None, 0 if payload.get("pending") == "1" else 1))
    conn.commit(); conn.close()
    await _refresh_calendar(request, gid, imr)
    return imr.oob(_pending_html(gid), "fin-pending")

async def _h_pending_pay_now(request, payload, imr):
    """Money leaves today, regardless of the bill's original due date."""
    gid = await _active_group(request)
    conn = _conn(gid)
    conn.execute("UPDATE entries SET date=?, confirmed=1 WHERE id=?", (date.today().isoformat(), payload.get("id","")))
    conn.commit(); conn.close()
    await _refresh_calendar(request, gid, imr)
    return imr.oob(_pending_html(gid), "fin-pending")

async def _h_pending_mark_paid(request, payload, imr):
    """Already handled elsewhere (e.g. autopay) - stop reserving against it, but don't touch today's actual liquid; keeps its original date so normal accounting picks it up on/after that date."""
    gid = await _active_group(request)
    conn = _conn(gid)
    conn.execute("UPDATE entries SET confirmed=1 WHERE id=?", (payload.get("id",""),))
    conn.commit(); conn.close()
    await _refresh_calendar(request, gid, imr)
    return imr.oob(_pending_html(gid), "fin-pending")

async def _h_group_create(request, payload, imr):
    name = (payload.get("label") or "").strip()
    if not name: return imr
    groups = _load_groups()
    gid = f"g_{uuid.uuid4().hex[:10]}"
    groups[gid] = {"label": name, "members": [request.state.user.username], "low_balance_threshold": 100.0, "last_low_balance_notify": None}
    _save_groups(groups)
    await ENV["set_state"](request, gid, scope="user", namespace="finance", key="active_group")
    return imr.raw(_panel_settings(request, gid))

async def _h_group_set_default(request, payload, imr):
    gid = payload.get("gid","")
    groups = _load_groups()
    if gid in groups and request.state.user.username in groups[gid].get("members", []):
        await ENV["set_state"](request, gid, scope="user", namespace="finance", key="default_group")
    return imr.raw(_panel_settings(request, gid))

async def _h_group_leave(request, payload, imr):
    gid = payload.get("gid",""); username = request.state.user.username
    groups = _load_groups()
    if gid not in groups or username not in groups[gid].get("members", []): return imr
    groups[gid]["members"] = [m for m in groups[gid]["members"] if m != username]
    if not groups[gid]["members"]:
        groups.pop(gid)
        _db_path(gid).unlink(missing_ok=True)
    _save_groups(groups)
    if await ENV["get_state"](request, scope="user", namespace="finance", key="default_group") == gid:
        await ENV["clear_state"](request, scope="user", namespace="finance", key="default_group")
    remaining = _user_groups(username)
    new_gid = remaining[0]["id"] if remaining else _ensure_personal_group(username)
    await ENV["set_state"](request, new_gid, scope="user", namespace="finance", key="active_group")
    return imr.raw(_panel_settings(request, new_gid))

def _panel_breakdown(gid):
    conn = _conn(gid)
    recs = [dict(r) for r in conn.execute("SELECT * FROM recurring WHERE active=1")]
    conn.close()
    def _monthly_equiv(r):
        mult = {"weekly": 4.333, "biweekly": 2.167, "semimonthly": 2.0, "monthly": 1.0, "yearly": 1/12}
        return abs(r["amount"]) * mult.get(r["frequency"], 1.0)
    income = sorted([r for r in recs if r["kind"] == "income"], key=_monthly_equiv, reverse=True)
    bills = sorted([r for r in recs if r["kind"] in ("expense", "transfer")], key=_monthly_equiv, reverse=True)
    total_income = sum(_monthly_equiv(r) for r in income)
    total_bills = sum(_monthly_equiv(r) for r in bills)
    def _rows(items):
        return "".join(f"""<tr><td>{_esc(r['label'])}</td><td class="dim">{r['frequency']}</td><td>{_money(abs(r['amount']))}{' ~est' if r['is_estimate'] else ''}</td><td>{_money(_monthly_equiv(r))}/mo</td></tr>""" for r in items) or '<tr><td colspan="4" class="dim">None active.</td></tr>'
    surplus = total_income - total_bills
    return f"""<div style="padding:.9rem;height:100%;overflow-y:auto;box-sizing:border-box">
                   <div class="info-bar" style="justify-content:space-between">
                       <span>Monthly income (est): <b style="color:#00ffa2">{_money(total_income)}</b></span>
                       <span>Monthly bills (est): <b style="color:#ff8c8c">{_money(total_bills)}</b></span>
                       <span>Surplus: <b style="color:{'#00ffa2' if surplus>=0 else '#ff5f5f'}">{_money(surplus)}</b></span>
                   </div>
                   <div class="fsect-hd" style="margin-top:1rem">Ongoing Income</div>
                   <table class="data-table"><thead><tr><th>Item</th><th>Frequency</th><th>Amount</th><th>Monthly equiv.</th></tr></thead><tbody>{_rows(income)}</tbody></table>
                   <div class="fsect-hd" style="margin-top:1rem">Ongoing Bills / Transfers</div>
                   <table class="data-table"><thead><tr><th>Item</th><th>Frequency</th><th>Amount</th><th>Monthly equiv.</th></tr></thead><tbody>{_rows(bills)}</tbody></table>
                   <p class="dim tiny" style="margin-top:.5rem">Monthly equivalents are a normalized comparison figure (e.g. weekly &#215; 4.333) - not a prediction of any specific month, which will vary based on how many of each cycle actually falls in it.</p>
               </div>"""

def _weekday_count(start: date, end: date) -> int:
    """Counts Mon-Fri days in [start, end] inclusive - the unit a standard hourly M-F schedule is paid against."""
    days = (end - start).days + 1
    full_weeks, rem = divmod(days, 7)
    count = full_weeks * 5
    d = start
    for _ in range(rem):
        if d.weekday() < 5: count += 1
        d += timedelta(days=1)
    return count

def _wage_period_bounds(rec: dict, pay_date: date) -> tuple:
    """Semimonthly wage: period ending on day1 covers (prior period's end, day1]; period ending on day2 covers (day1, day2]. Wraps correctly across month boundaries."""
    last = calendar.monthrange(pay_date.year, pay_date.month)[1]
    d1, d2 = min(rec["day1"] or 1, last), min(rec["day2"] or 15, last)
    if pay_date.day == d1:
        prev_month = pay_date.replace(day=1) - timedelta(days=1)
        prev_last = calendar.monthrange(prev_month.year, prev_month.month)[1]
        return prev_month.replace(day=min(rec["day2"] or 15, prev_last)) + timedelta(days=1), pay_date
    return pay_date.replace(day=d1) + timedelta(days=1), pay_date

def _pending_html(gid: str) -> str:
    conn = _conn(gid)
    rows = [dict(r) for r in conn.execute("SELECT * FROM entries WHERE confirmed=0 ORDER BY date")]
    conn.close()
    if not rows: return '<div class="dim tiny" style="padding:.4rem 0">No pending bills.</div>'
    today = date.today()
    out = ""
    for e in rows:
        overdue = date.fromisoformat(e["date"]) < today
        out += f"""<div class="glass" style="padding:.5rem .7rem;margin-bottom:.3rem;display:flex;align-items:center;gap:.5rem">
                       <span style="flex:1">{_esc(e["label"])} <span class="dim tiny">{'OVERDUE - was due' if overdue else 'due'} {e["date"]}</span></span>
                       <b style="color:{'#ff5f5f' if overdue else 'var(--text)'}">{_money(e["amount"])}</b>
                       <button class="cm-qbtn" hx-post="/im/in" hx-target="body" hx-swap="none" hx-vals='{{"type":"finance_pending_pay_now","lvl":1,"id":"{e["id"]}"}}'>Pay Now</button>
                       <button class="cm-qbtn" hx-post="/im/in" hx-target="body" hx-swap="none" hx-vals='{{"type":"finance_pending_mark_paid","lvl":1,"id":"{e["id"]}"}}'>Mark Paid</button>
                   </div>"""
    return out

# --- Notes: free text on any day (the day view lists them; the calendar and Upcoming mark the day) ---

def _vals(action: str, **kw) -> str: return f"""hx-post="/im/in" hx-target="body" hx-swap="none" hx-vals='{json.dumps({"type": f"finance_{action}", "lvl": 1, **kw})}'"""

def _notes(gid: str, day: str) -> list:
    conn = _conn(gid)
    rows = [dict(r) for r in conn.execute("SELECT * FROM notes WHERE date=? ORDER BY t", (day,))]
    conn.close()
    return rows

async def _h_note_add(request, payload, imr):
    gid, d = await _active_group(request), payload.get("date", date.today().isoformat())
    conn = _conn(gid)
    conn.execute("INSERT INTO notes VALUES (?,?,?,?,?)", (uuid.uuid4().hex[:10], d, payload.get("text", "").strip(), request.state.user.username, datetime.now().isoformat(timespec="seconds")))
    conn.commit()
    conn.close()
    imr.oob(_day_detail_html(gid, date.fromisoformat(d)), "fin-modal")
    await _refresh_calendar(request, gid, imr)
    return imr

async def _h_note_delete(request, payload, imr):
    gid = await _active_group(request)
    conn = _conn(gid)
    conn.execute("DELETE FROM notes WHERE id=?", (payload.get("id", ""),))
    conn.commit()
    conn.close()
    imr.oob(_day_detail_html(gid, date.fromisoformat(payload["date"])), "fin-modal")
    await _refresh_calendar(request, gid, imr)
    return imr

# --- Upcoming: what is due and coming, in date order, with the balance after each - and what is really available now ---

async def _up_days(request) -> int: return int(await ENV["get_state"](request, scope="user", namespace="finance", key="up_days") or 31)

def _upcoming(gid: str, days: int) -> dict:
    """Unconfirmed entries (bills not marked paid, projected occurrences, income not yet in) up to today + days, oldest first, so overdue ones lead; rows on liquid accounts carry the liquid balance after them.
    now = liquid money as the accounts stand today; available = now minus everything due up to and including the day of the next income, minus the group's low-balance buffer."""
    _materialize(gid)
    today, end = date.today().isoformat(), (date.today() + timedelta(days=days)).isoformat()
    conn = _conn(gid)
    rows = [dict(r) for r in conn.execute("SELECT * FROM entries WHERE confirmed=0 AND date<=? ORDER BY date, amount", (end,))]
    recs = {r["id"]: dict(r) for r in conn.execute("SELECT id, auto_pay, is_estimate FROM recurring")}
    noted = {r["date"] for r in conn.execute("SELECT DISTINCT date FROM notes")}
    conn.close()
    accts, auto = _account_map(gid), {k for k, r in recs.items() if r["auto_pay"]}
    run = now = _settled_liquid(gid)
    for e in rows:
        a, r = accts.get(e["account_id"], {}), recs.get(e["recurring_id"] or "", {})
        e.update(account=a.get("label", "?"), liquid=bool(a.get("is_liquid")), auto=bool(r.get("auto_pay")), estimate=bool(r.get("is_estimate")), overdue=e["date"] < today, noted=e["date"] in noted, covered=_in_balance(e, a.get("asof"), auto))
        if e["liquid"] and not e["covered"]: run += e["amount"]
        e["after"] = run if e["liquid"] and not e["covered"] else None
    live = [e for e in rows if e["after"] is not None]
    nxt = next((e for e in live if e["amount"] > 0 and e["date"] >= today), None)
    due = sum(e["amount"] for e in live if e["amount"] < 0 and (not nxt or e["date"] <= nxt["date"]))
    buffer = _load_groups().get(gid, {}).get("low_balance_threshold", 100.0)
    return {"rows": rows, "now": now, "next": nxt, "due": due, "buffer": buffer, "available": now + due - buffer, "low": min(live, key=lambda e: e["after"], default=None)}

def _upcoming_row(e: dict, today: str) -> str:
    when = f"""<span style="color:#ff5f5f">{e["date"][5:]} overdue</span>""" if e["overdue"] else f"""<b>{e["date"][5:]} today</b>""" if e["date"] == today else e["date"][5:]
    tags = "".join(f"""<span class="chip">{t}</span>""" for t, on in (("auto", e["auto"]), ("~est", e["estimate"]), ("&#x1F4DD;", e["noted"]), ("in your balance", e["covered"]), ("not liquid", not e["liquid"])) if on)
    pay_now = f"""<button class="btn-icon" title="Paying it now (leaves today)" {_vals("up_paid", id=e["id"], now=1)}>&#x1F4B5;</button>""" if e["amount"] < 0 else ""
    skip = f"""<button class="btn-icon" title="Skip this occurrence (the rest of its schedule stays)" {_vals("up_skip", id=e["id"])}>&#x23ED;</button>""" if e["recurring_id"] else ""
    return f"""<tr style="opacity:{.55 if e["after"] is None else 1}"><td style="cursor:pointer;white-space:nowrap" title="Open this day (notes, edits)" {_vals("day_open", date=e["date"])}>{when}</td><td>{_esc(e["label"])} {tags}</td><td class="dim tiny">{_esc(e["account"])}</td>
               <td style="color:{"#00ffa2" if e["amount"] >= 0 else "#ff8c8c"}">{_money(e["amount"])}</td><td>{_money(e["after"]) if e["after"] is not None else ""}</td>
               <td><div class="row" style="flex-wrap:nowrap;gap:.1rem"><button class="btn-icon" title="{"Paid" if e["amount"] < 0 else "Arrived"} (on its date; today if that has not come yet)" {_vals("up_paid", id=e["id"])}>&#x2713;</button>{pay_now}{skip}</div></td></tr>"""

def _upcoming_html(gid: str, days: int) -> str:
    u, today = _upcoming(gid, days), date.today().isoformat()
    until = f"""before the next income ({_esc(u["next"]["label"])} {u["next"]["date"][5:]})""" if u["next"] else f"in the next {days} days (no income expected)"
    low = f"""<span>Lowest ahead: <b style="color:{"#ff5f5f" if u["low"]["after"] < u["buffer"] else "inherit"}">{_money(u["low"]["after"])}</b> on {u["low"]["date"][5:]}</span>""" if u["low"] else ""
    span = "".join(f"""<button class="chip"{' style="background:var(--accent);color:var(--bg)"' if n == days else ""} {_vals("upcoming_days", days=n)}>{n} days</button>""" for n in (14, 31, 62, 120))
    return f"""<div class="info-bar row" style="justify-content:space-between"><span>Liquid now: <b>{_money(u["now"])}</b></span><span>Due {until}: <b style="color:#ff8c8c">{_money(-u["due"])}</b></span>
                   <span>Available now: <b style="color:{"#00ffa2" if u["available"] >= 0 else "#ff5f5f"};font-size:1.25em">{_money(u["available"])}</b> <span class="dim tiny">after your {_money(u["buffer"])} buffer</span></span>{low}</div>
               <div class="row" style="margin:.3rem 0"><span class="dim tiny grow">Not paid or not in yet, oldest first. Liquid now = the balances you entered plus confirmed entries after them (enter the bank's number after paying).</span>{span}</div>
               <table class="data-table"><thead><tr><th>Date</th><th>Item</th><th>Account</th><th>Amount</th><th>Balance after</th><th></th></tr></thead><tbody>{"".join(_upcoming_row(e, today) for e in u["rows"]) or '<tr><td colspan="6" class="dim">Nothing due in this window.</td></tr>'}</tbody></table>"""

async def _h_upcoming_days(request, payload, imr):
    await ENV["set_state"](request, int(payload.get("days") or 31), scope="user", namespace="finance", key="up_days")
    return imr.oob(_upcoming_html(await _active_group(request), int(payload.get("days") or 31)), "fin-upcoming")

async def _h_up_paid(request, payload, imr):
    """Paid (a bill) or arrived (income): on its own date when that has come, today when it was early; now=1 moves it to today (paying it now)."""
    gid = await _active_group(request)
    e = _entry(gid, payload.get("id", ""))
    if not e: return imr
    conn = _conn(gid)
    conn.execute("UPDATE entries SET confirmed=1, date=? WHERE id=?", (date.today().isoformat() if payload.get("now") else min(e["date"], date.today().isoformat()), e["id"]))
    conn.commit()
    conn.close()
    await _refresh_calendar(request, gid, imr)
    return imr

async def _h_up_skip(request, payload, imr):
    """This occurrence will not happen: recorded as an exception so it is not projected again; the rest of the schedule stays."""
    gid = await _active_group(request)
    e = _entry(gid, payload.get("id", ""))
    if not e or not e["recurring_id"]: return imr
    conn = _conn(gid)
    conn.execute("INSERT OR IGNORE INTO exceptions (recurring_id,date) VALUES (?,?)", (e["recurring_id"], e["date"]))
    conn.execute("DELETE FROM entries WHERE id=? OR id=?", (e["id"], e["linked_entry_id"] or ""))
    conn.commit()
    conn.close()
    await _refresh_calendar(request, gid, imr)
    return imr

# --- Plan: from one income to the next - what each one has to cover and what is left, the balance line ahead, and "what if I spend X on a day" (nothing is saved until you add it) ---

async def _plan_days(request) -> int: return int(await ENV["get_state"](request, scope="user", namespace="finance", key="plan_days") or 62)

def _plan(gid: str, days: int, extra: dict = None) -> dict:
    """Upcoming's rows on liquid accounts (plus an optional what-if row), each with the liquid balance after it, split into periods at every income still to come.
    A period: start (today, or the income's day), incomes, other rows, end (the liquid balance when it closes) and low (its lowest point). Overdue rows count from today."""
    u, today = _upcoming(gid, days), date.today().isoformat()
    rows = sorted([e for e in u["rows"] if e["after"] is not None] + ([extra] if extra else []), key=lambda e: (max(e["date"], today), e["amount"]))
    run, periods = u["now"], [{"start": today, "incomes": [], "rows": [], "end": u["now"], "low": u["now"]}]
    for e in rows:
        run += e["amount"]
        p = periods[-1]
        if e["amount"] > 0 and e["date"] > today and not (p["start"] == e["date"] and not p["rows"]): periods.append(p := {"start": e["date"], "incomes": [], "rows": [], "end": run, "low": run})
        (p["incomes"] if e["amount"] > 0 and e["date"] >= p["start"] and not p["rows"] else p["rows"]).append({**e, "after": run})
        p["end"], p["low"] = run, min(p["low"], run)
    nxt = next((e for e in rows if e["amount"] > 0 and e["date"] >= today), None)   # available now, as Upcoming counts it - with the what-if row
    due = sum(e["amount"] for e in rows if e["amount"] < 0 and (not nxt or e["date"] <= nxt["date"]))
    return {**u, "periods": periods, "points": [(today, u["now"])] + [(max(r["date"], today), r["after"]) for p in periods for r in p["incomes"] + p["rows"]], "low": min(periods, key=lambda p: p["low"]), "available": u["now"] + due - u["buffer"]}

def _plan_chart(points: list, base: list, days: int, buffer: float, marks: list) -> str:
    """The liquid balance as a step line from today over days (base: the line without the what-if row, drawn faint behind it), with the buffer dashed and zero marked.
    marks: the days named under the line (the incomes). The drawing stretches to the width; its labels are page text placed on it, so they stay readable on a phone."""
    d0 = date.today()
    vals = [v for _, v in points + base] + [buffer, 0]
    lo, hi = min(vals), max(vals)
    pad = (hi - lo) * .08 or 50
    lo, hi = lo - pad, hi + pad
    x = lambda d: round(20 + (date.fromisoformat(d) - d0).days / max(days, 1) * 960, 1)
    y = lambda v: round(4 + (hi - v) / (hi - lo) * 92, 1)
    def line(pts): return f"""{x(pts[0][0])},{y(pts[0][1])} """ + " ".join(f"{x(d)},{y(v1)} {x(d)},{y(v2)}" for (_, v1), (d, v2) in zip(pts, pts[1:])) + f" 990,{y(pts[-1][1])}"
    lbl = lambda left, top, text, style="": f"""<span class="fin-ch-lbl" style="left:{left / 10}%;top:{top}%;{style}">{text}</span>"""
    low = min(points, key=lambda p: p[1])
    ticks = "".join(lbl(x(d), 100, d[5:]) for d in marks[::max(1, len(marks) // 8)])
    faint = f"""<polyline points="{line(base)}" vector-effect="non-scaling-stroke" style="fill:none;stroke:var(--text_muted);stroke-width:1;opacity:.6"/>""" if base != points else ""
    return f"""<div class="fin-chart"><svg viewBox="0 0 1000 100" preserveAspectRatio="none" role="img" aria-label="Liquid balance ahead">
                   <line x1="20" x2="990" y1="{y(buffer)}" y2="{y(buffer)}" vector-effect="non-scaling-stroke" style="stroke:#ffaa44;stroke-dasharray:4 3;stroke-width:1"/>
                   <line x1="20" x2="990" y1="{y(0)}" y2="{y(0)}" vector-effect="non-scaling-stroke" style="stroke:var(--border);stroke-width:1"/>{faint}
                   <polyline points="{line(points)}" vector-effect="non-scaling-stroke" style="fill:none;stroke:var(--accent);stroke-width:2"/></svg>
               {lbl(990, y(buffer), f"buffer {_money(buffer)}", "transform:translate(-100%,-110%);color:#ffaa44")}{lbl(20, 0, _money(hi - pad)[:-3], "transform:translate(0,-100%)")}
               <span class="fin-ch-dot" style="left:{x(low[0]) / 10}%;top:{y(low[1])}%;background:{"#ff5f5f" if low[1] < buffer else "var(--accent)"}"></span>{lbl(x(low[0]), y(low[1]), _money(low[1]), "transform:translate(-50%,40%);color:var(--text)")}{ticks}</div>"""

def _plan_period(p: dict, nxt: str, buffer: float) -> str:
    chip = lambda e: f"""<span class="chip" title="{e["date"]}{" - what if" if e.get("whatif") else ""}" style="{"font-style:italic;border-color:var(--accent)" if e.get("whatif") else ""}">{_esc(e["label"])} {_money(e["amount"])} <span class="dim">{e["date"][5:]}</span></span>"""
    span = f"""{"Today" if not p["incomes"] else date.fromisoformat(p["start"]).strftime("%a %m-%d")} &#x2192; {date.fromisoformat(nxt).strftime("%a %m-%d") if nxt else "end of view"}"""
    bills = sum(e["amount"] for e in p["rows"])
    return f"""<tr><td style="white-space:nowrap">{span}</td><td>{"".join(chip(e) for e in p["incomes"]) or '<span class="dim">-</span>'}</td><td>{"".join(chip(e) for e in p["rows"]) or '<span class="dim">nothing due</span>'}</td>
               <td style="color:#ff8c8c;white-space:nowrap">{_money(bills)}</td><td style="white-space:nowrap"><b style="color:{"#ff5f5f" if p["end"] < buffer else "inherit"}">{_money(p["end"])}</b></td><td style="white-space:nowrap;color:{"#ff5f5f" if p["low"] < buffer else "inherit"}">{_money(p["low"])}</td></tr>"""

def _plan_html(gid: str, days: int, w: dict = None) -> str:
    """w: a what-if spend (amount, date, label) shown on top of the plan; Add puts it in as a bill not paid yet."""
    extra = {"id": "", "label": (w.get("label") or "what if").strip(), "amount": -abs(float(w["amount"])), "date": w.get("date") or date.today().isoformat(), "whatif": True} if w and _num(str(w.get("amount", ""))) else None
    base, pl = _plan(gid, days), _plan(gid, days, extra)
    ps, bf = pl["periods"], pl["buffer"]
    rows = "".join(_plan_period(p, ps[i + 1]["start"] if i + 1 < len(ps) else "", bf) for i, p in enumerate(ps))
    span = "".join(f"""<button class="chip"{' style="background:var(--accent);color:var(--bg)"' if n == days else ""} {_vals("plan_days", days=n)}>{n} days</button>""" for n in (31, 62, 120))
    diff = f"""<div class="info-bar">With &ldquo;{_esc(extra["label"])}&rdquo; ({_money(extra["amount"])} on {extra["date"][5:]}): available now <b>{_money(pl["available"])}</b> (was {_money(base["available"])}), lowest ahead <b style="color:{"#ff5f5f" if pl["low"]["low"] < bf else "inherit"}">{_money(pl["low"]["low"])}</b> (was {_money(base["low"]["low"])}){" - below your buffer" if pl["low"]["low"] < bf else ""}.
               <button class="ui-btn" {_vals("plan_add", amount=-extra["amount"], date=extra["date"], label=extra["label"])}>Add it as a bill (not paid yet)</button><button class="ui-btn" {_vals("plan_whatif")}>Clear</button></div>""" if extra else ""
    form = f"""<form class="row" {_vals("plan_whatif")} hx-include="this"><span class="dim tiny">What if I spend</span><input type="number" name="amount" step="0.01" min="0" class="module-select" style="width:7rem" value="{-extra["amount"] if extra else ""}" required>
               <span class="dim tiny">on</span><input type="date" name="date" class="module-select" value="{extra["date"] if extra else date.today().isoformat()}"><input name="label" class="module-select" placeholder="for what" value="{_esc(extra["label"]) if extra else ""}"><button type="submit" class="ui-btn">Show</button></form>"""
    return f"""<div class="info-bar row" style="justify-content:space-between"><span>Liquid now: <b>{_money(pl["now"])}</b></span><span>Available now: <b style="color:{"#00ffa2" if pl["available"] >= 0 else "#ff5f5f"}">{_money(pl["available"])}</b></span>
                   <span>Lowest ahead: <b style="color:{"#ff5f5f" if pl["low"]["low"] < bf else "inherit"}">{_money(pl["low"]["low"])}</b> in the period from {pl["low"]["start"][5:]}</span><span class="row">{span}</span></div>
               {_plan_chart(pl["points"], base["points"], days, bf, [p["start"] for p in ps[1:]])}{form}{diff}
               <div class="dim tiny" style="margin:.3rem 0">Each row runs from an income to the day before the next one: what that income has to cover, and what is left. Rows are the bills and income not marked paid or in yet (Upcoming), on liquid accounts.</div>
               <div style="overflow-x:auto"><table class="data-table"><thead><tr><th>Period</th><th>Income</th><th>To pay in it</th><th>Total</th><th>Left at its end</th><th>Lowest</th></tr></thead><tbody>{rows}</tbody></table></div>"""

def _panel_plan(gid, days): return f'<div style="padding:.9rem;height:100%;overflow-y:auto;box-sizing:border-box"><div id="fin-plan">{_plan_html(gid, days)}</div></div>'

async def _h_plan_days(request, payload, imr):
    await ENV["set_state"](request, int(payload.get("days") or 62), scope="user", namespace="finance", key="plan_days")
    return imr.oob(_plan_html(await _active_group(request), int(payload.get("days") or 62)), "fin-plan")

async def _h_plan_whatif(request, payload, imr): return imr.oob(_plan_html(await _active_group(request), await _plan_days(request), payload if payload.get("amount") else None), "fin-plan")

async def _h_plan_add(request, payload, imr):
    """The what-if spend becomes a bill not paid yet on the first liquid account (change it in that day's view)."""
    gid = await _active_group(request)
    acct = next((a for a in _accounts(gid) if a["is_liquid"]), None)
    if not acct: return imr.oob('<div class="err-box">Add a liquid account first (Accounts).</div>' + _plan_html(gid, await _plan_days(request)), "fin-plan")
    conn = _conn(gid)
    conn.execute("INSERT INTO entries VALUES (?,?,?,?,?,?,?,?,?,?)", (uuid.uuid4().hex[:10], acct["id"], payload.get("date") or date.today().isoformat(), str(payload.get("label") or "what if").strip(), -abs(float(payload["amount"])), "", 0, None, None, 0))
    conn.commit()
    conn.close()
    await _refresh_calendar(request, gid, imr)
    return imr.oob(_plan_html(gid, await _plan_days(request)), "fin-plan")

# --- Import: a sheet's rows (a CSV file, or cells copied from the sheet and pasted) as bills or transactions; you map the columns, see each row as it will be read, and can undo an import ---

_IMPORT_FIELDS = {"bills": [("label", "Name", True), ("amount", "Amount", True), ("due", "Due day or date", True), ("frequency", "How often (monthly when empty)", False), ("kind", "Income / expense", False), ("category", "Category", False), ("auto", "Auto-pay (yes / no)", False)],
                  "transactions": [("date", "Date", True), ("label", "Description", True), ("amount", "Amount", False), ("debit", "Debit (money out)", False), ("credit", "Credit (money in)", False), ("category", "Category", False), ("note", "Note (kept on that day)", False)]}
_DATE_FORMATS = ("%Y-%m-%d", "%m/%d/%Y", "%m/%d/%y", "%m-%d-%Y", "%m-%d-%y", "%Y/%m/%d", "%b %d, %Y", "%B %d, %Y", "%b %d %Y", "%B %d %Y", "%d %b %Y", "%d %B %Y")

def _sheet_rows(text: str) -> list:
    """Rows of cells copied from a sheet (tab-separated) or of CSV text (comma, semicolon or bar)."""
    sample = text[:4096]
    try: delim = "\t" if "\t" in sample else csv.Sniffer().sniff(sample, delimiters=",;|").delimiter
    except csv.Error: delim = ","
    return [r for r in csv.reader(io.StringIO(text), delimiter=delim) if any(c.strip() for c in r)]

def _num(s: str):
    """$1,234.56 / -12 / (12.00) / 12- as a number (US style: comma = thousands); None when it is not one."""
    t = re.sub(r"[\s$€£,]", "", s or "")
    neg = (t.startswith("(") and t.endswith(")")) or t.endswith("-") or t.startswith("-")
    try: v = float(t.strip("()").strip("-"))
    except ValueError: return None
    return -v if neg else v

def _sheet_date(s: str):
    for f in _DATE_FORMATS:
        try: return datetime.strptime((s or "").strip(), f).date()
        except ValueError: pass
    return None

def _due(s: str) -> tuple:
    """(day of month, first date) from "15", "15th", "the 15th" or a date; (None, None) when it is neither."""
    d = _sheet_date(s)
    if d: return d.day, d
    m = re.search(r"\b([1-9]|[12]\d|3[01])(?:st|nd|rd|th)?\b", s or "")
    return (int(m.group(1)), None) if m else (None, None)

def _freq(s: str) -> str:
    t = (s or "").lower()
    return "biweekly" if re.search(r"bi-?week|every (2|two) weeks|fortnight", t) else "weekly" if "week" in t else "semimonthly" if re.search(r"semi|twice a month|2x", t) else "yearly" if re.search(r"year|annual", t) else "monthly"

def _interpret(kind: str, row: list, m: dict, sign: str) -> dict:
    """One sheet row as it will be imported; "problem" says why it will be skipped. sign: expense / income (every amount is that) or sign (negative = money out)."""
    cell = lambda k: row[int(m[k])].strip() if str(m.get(k, "")).isdigit() and int(m[k]) < len(row) else ""
    label = cell("label")
    if kind == "bills":
        amt, (day, first) = _num(cell("amount")), _due(cell("due"))
        k = cell("kind").lower()
        income = any(w in k for w in ("income", "deposit", "paycheck", "salary", "wage")) or (not k and (sign == "income" or (sign == "sign" and (amt or 0) > 0)))
        problem = "no name" if not label else "no amount" if amt is None else "no due day" if not day else ""
        return {"label": label, "amount": abs(amt or 0), "kind": "income" if income else "expense", "frequency": _freq(cell("frequency")), "day": day, "first": first, "category": cell("category"), "auto": cell("auto").lower() in ("yes", "y", "true", "1", "auto", "x"), "problem": problem}
    d, amt = _sheet_date(cell("date")), _num(cell("amount"))
    if amt is None and (cell("debit") or cell("credit")): amt = (_num(cell("credit")) or 0) - abs(_num(cell("debit")) or 0)
    elif amt is not None and sign != "sign": amt = abs(amt) if sign == "income" else -abs(amt)
    return {"date": d, "label": label, "amount": amt, "category": cell("category"), "note": cell("note"), "problem": "no date" if not d else "no description" if not label else "no amount" if amt is None else ""}

def _imports(gid: str) -> list:
    conn = _conn(gid)
    rows = [dict(r) for r in conn.execute("SELECT * FROM imports ORDER BY t DESC LIMIT 10")]
    conn.close()
    return rows

def _import_html(gid: str, f: dict = None, msg: str = "") -> str:
    """Step 1: paste cells or pick a file, say what the rows are. Step 2 (after Read): map the columns, check the preview, import. Recent imports can be undone."""
    f = f or {}
    text, kind, sign = f.get("text", ""), f.get("kind", "bills"), f.get("sign", "expense")
    rows, hdr = _sheet_rows(text) if text.strip() else [], f.get("header") == "1" if f.get("read") else True   # the checkbox sends nothing when cleared, so "read" tells a cleared box from a first visit
    head = rows[0] if rows and hdr else []
    data = rows[1:] if head else rows
    cols = [(str(i), f"{i + 1}: {(head[i] if i < len(head) else (data[0][i] if data and i < len(data[0]) else ''))[:30]}") for i in range(max((len(r) for r in rows), default=0))]
    guess = lambda key, label: next((i for i, h in enumerate(head) if key in h.lower() or label.split()[0].lower() in h.lower()), None)
    mapping = {k: f[f"map_{k}"] if f"map_{k}" in f else (str(g) if (g := guess(k, lbl)) is not None else "") for k, lbl, _ in _IMPORT_FIELDS[kind]}   # a column you chose, else the one whose header names the field
    accts = _accounts(gid)
    acct = f.get("account_id") or (accts[0]["id"] if accts else "")
    sel = lambda name, opts, cur: f"""<select name="{name}" class="module-select">{"".join(f'<option value="{v}"{" selected" if v == cur else ""}>{_esc(t)}</option>' for v, t in opts)}</select>"""
    step1 = f"""<label class="dim tiny">Paste cells copied from your sheet (or a CSV), or pick a CSV file - Google Sheets: File &gt; Download &gt; CSV.</label>
                <textarea name="text" class="cm-input mono" rows="{4 if rows else 10}" placeholder="Name&#9;Amount&#9;Due">{_esc(text)}</textarea>
                <div class="row"><input type="file" accept=".csv,.tsv,.txt" onchange="var x = this.files[0], t = this.form.querySelector('textarea[name=text]'); if (x) x.text().then(function(s) {{ t.value = s; }});">
                <span class="dim tiny">The rows are</span>{sel("kind", [("bills", "bills / income that repeat"), ("transactions", "transactions (one-time, already happened)")], kind)}
                <label class="row dim tiny"><input type="checkbox" name="header" value="1"{" checked" if hdr else ""}> first row is the column names</label><input type="hidden" name="read" value="1"></div>"""
    if not rows: return f"""<div class="fsect-hd">Import</div><form hx-post="/im/in" hx-target="body" hx-swap="none" hx-include="this" class="node-form"><input type="hidden" name="type" value="finance_import_read"><input type="hidden" name="lvl" value="1">{step1}<div class="row"><span class="dim tiny grow">{msg}</span><button type="submit" class="ui-btn">Read</button></div></form>{_undo_html(gid)}"""
    maps = "".join(f"""<label class="row"><span class="dim tiny" style="min-width:11rem">{lbl}{" *" if req else ""}</span>{sel(f"map_{k}", [("", "-")] + cols, mapping[k])}</label>""" for k, lbl, req in _IMPORT_FIELDS[kind])
    signs = [("expense", "every amount is money out"), ("income", "every amount is money in"), ("sign", "by sign: negative = money out")]
    items = [_interpret(kind, r, mapping, sign) for r in data]
    ok = [x for x in items if not x["problem"]]
    cells = (lambda x: (x["label"], _money(x["amount"]), x["kind"], f"""{x["frequency"]}, day {x["day"]}""", x["category"], "auto" if x["auto"] else "")) if kind == "bills" else (lambda x: (str(x["date"] or ""), x["label"], _money(x["amount"]) if x["amount"] is not None else "", x["category"], x["note"]))
    heads = ("Name", "Amount", "Kind", "When", "Category", "Auto") if kind == "bills" else ("Date", "Description", "Amount", "Category", "Note")
    preview = "".join(f"""<tr style="opacity:{.5 if x["problem"] else 1}">{"".join(f"<td>{_esc(c)}</td>" for c in cells(x))}<td style="color:#ff8c8c">{_esc(x["problem"])}</td></tr>""" for x in items[:15])
    go = f"""<button type="button" class="ui-btn" hx-post="/im/in" hx-target="body" hx-swap="none" hx-include="closest form" hx-vals='{{"type": "finance_import_go", "lvl": 1}}'>Import {len(ok)} row(s)</button>"""
    return f"""<div class="fsect-hd">Import</div><form hx-post="/im/in" hx-target="body" hx-swap="none" hx-include="this" class="node-form"><input type="hidden" name="type" value="finance_import_read"><input type="hidden" name="lvl" value="1">{step1}
               <div class="fsect-hd">Columns</div><div class="settings-compact">{maps}<label class="row"><span class="dim tiny" style="min-width:11rem">Account</span>{sel("account_id", [(a["id"], a["label"]) for a in accts], acct)}</label><label class="row"><span class="dim tiny" style="min-width:11rem">Amounts</span>{sel("sign", signs, sign)}</label></div>
               <div class="row"><span class="dim tiny grow">{len(data)} row(s): {len(ok)} will be imported, {len(items) - len(ok)} skipped (reason shown). {"Already-imported rows are skipped too (same name for bills; same date, description, amount and account for transactions)." if ok else ""} {msg}</span><button type="submit" class="ui-btn">Update preview</button>{go if ok and acct else ""}</div>
               <table class="data-table"><thead><tr>{"".join(f"<th>{h}</th>" for h in heads)}<th></th></tr></thead><tbody>{preview}</tbody></table></form>{_undo_html(gid)}"""

def _undo_html(gid: str) -> str:
    rows = "".join(f"""<div class="list-row row"><span class="grow">{_esc(i["label"])}</span><span class="dim tiny">{i["t"][:16].replace("T", " ")} &#xB7; {len(json.loads(i["ids"]))} row(s)</span><button class="cm-qbtn" style="color:#ff5f5f" {_vals("import_undo", id=i["id"])} hx-confirm="Remove the {len(json.loads(i["ids"]))} row(s) this import added (and anything projected from them)? Edits you made to them are lost.">Undo</button></div>""" for i in _imports(gid))
    return f"""<div class="fsect-hd" style="margin-top:1rem">Recent imports</div>{rows or '<div class="dim tiny">None yet.</div>'}"""

async def _h_import_read(request, payload, imr): return imr.oob(_import_html(await _active_group(request), payload), "fin-import")

async def _h_import_go(request, payload, imr):
    """Adds the previewed rows: bills as recurring items (reminder 2 days before, active), transactions as confirmed entries (with their notes on that day). Rows already there are skipped. Recorded so it can be undone."""
    gid, kind = await _active_group(request), payload.get("kind", "bills")
    rows = _sheet_rows(payload.get("text", ""))
    mapping = {k: payload.get(f"map_{k}", "") for k, _, _ in _IMPORT_FIELDS[kind]}
    items = [x for x in (_interpret(kind, r, mapping, payload.get("sign", "expense")) for r in (rows[1:] if payload.get("header") == "1" else rows)) if not x["problem"]]
    acct, today, ids, names, skipped = payload.get("account_id", ""), date.today(), [], [], 0
    conn = _conn(gid)
    if kind == "bills":
        have = {r["label"].strip().lower() for r in conn.execute("SELECT label FROM recurring")}
        for x in items:
            if x["label"].lower() in have:
                skipped += 1
                continue
            anchor = x["first"] or date(today.year, today.month, min(x["day"], calendar.monthrange(today.year, today.month)[1]))
            ids.append(uuid.uuid4().hex[:10])
            names.append(x["label"])
            have.add(x["label"].lower())
            conn.execute("INSERT INTO recurring (id,label,kind,account_id,to_account_id,amount,is_estimate,frequency,anchor_date,day1,day2,notify,notify_days_before,category,active,last_notified_date,auto_pay) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                         (ids[-1], x["label"], x["kind"], acct, None, x["amount"], 0, x["frequency"], anchor.isoformat(), x["day"], 15, 1, 2, x["category"], 1, None, 1 if x["auto"] else 0))
    else:
        for x in items:
            if conn.execute("SELECT 1 FROM entries WHERE account_id=? AND date=? AND label=? AND ABS(amount-?)<0.005", (acct, x["date"].isoformat(), x["label"], x["amount"])).fetchone():
                skipped += 1
                continue
            ids.append(uuid.uuid4().hex[:10])
            names.append(x["label"])
            conn.execute("INSERT INTO entries VALUES (?,?,?,?,?,?,?,?,?,?)", (ids[-1], acct, x["date"].isoformat(), x["label"], x["amount"], x["category"], 0, None, None, 1))
            if x["note"]: conn.execute("INSERT INTO notes VALUES (?,?,?,?,?)", (uuid.uuid4().hex[:10], x["date"].isoformat(), f"""{x["label"]}: {x["note"]}""", request.state.user.username, datetime.now().isoformat(timespec="seconds")))
    if ids: conn.execute("INSERT INTO imports VALUES (?,?,?,?,?)", (uuid.uuid4().hex[:10], datetime.now().isoformat(timespec="seconds"), kind, f"""{len(ids)} {kind}: {", ".join(names[:3])}{"..." if len(names) > 3 else ""}""", json.dumps(ids)))
    conn.commit()
    conn.close()
    _materialize(gid)
    return imr.oob(_import_html(gid, msg=f"Imported {len(ids)} row(s){f', skipped {skipped} already there' if skipped else ''}."), "fin-import")

async def _h_import_undo(request, payload, imr):
    gid = await _active_group(request)
    conn = _conn(gid)
    row = conn.execute("SELECT * FROM imports WHERE id=?", (payload.get("id", ""),)).fetchone()
    if row:
        ids = json.loads(row["ids"])
        marks = ",".join("?" * len(ids))
        if row["kind"] == "bills":
            conn.execute(f"DELETE FROM recurring WHERE id IN ({marks})", ids)
            conn.execute(f"DELETE FROM entries WHERE confirmed=0 AND recurring_id IN ({marks})", ids)
        else: conn.execute(f"DELETE FROM entries WHERE id IN ({marks})", ids)
        conn.execute("DELETE FROM imports WHERE id=?", (row["id"],))
        conn.commit()
    conn.close()
    _materialize(gid)
    return imr.oob(_import_html(gid, msg="Import undone." if row else ""), "fin-import")

# --- For other modules (the "finance" service) ---

def due_items(username: str, days: int = 14) -> list:
    """Bills not marked paid that need you (auto-pay ones are left out), overdue or due within days, from every finance group username is in - for Muninn's Today and other summary views."""
    out, end = [], (date.today() + timedelta(days=days)).isoformat()
    for g in _user_groups(username):
        _materialize(g["id"])
        conn = _conn(g["id"])
        auto = {r["id"] for r in conn.execute("SELECT id FROM recurring WHERE auto_pay=1")}
        out += [{"date": e["date"], "label": e["label"], "amount": e["amount"], "where": g.get("label", g["id"]), "app": "Finance", "url": f"{_P}/"} for e in conn.execute("SELECT * FROM entries WHERE confirmed=0 AND amount<0 AND date<=?", (end,)) if e["recurring_id"] not in auto]
        conn.close()
    return sorted(out, key=lambda x: x["date"])

_CMD_HELP = "@finance gas 40 - an expense paid today from your first cash account in the group Finance has open; also: 12.50 lunch yesterday | income 1200 paycheck | bill 85 internet 10/20 (not paid yet) | gas 40 from visa (an account by name)"
_CMD_KINDS = {"income": ("income", 1), "+": ("income", 1), "bill": ("bill", 0), "owe": ("bill", 0), "expense": ("expense", 1), "spent": ("expense", 1), "paid": ("expense", 1)}   # first word -> (kind, confirmed)

def _cmd_date(word: str):
    """today / yesterday / tomorrow, a date as Import reads one, or M/D (this year); None when the word is not a date."""
    w = word.lower()
    if w in ("today", "yesterday", "tomorrow"): return date.today() + timedelta(days={"today": 0, "yesterday": -1, "tomorrow": 1}[w])
    m = re.fullmatch(r"(\d{1,2})/(\d{1,2})", w)
    try: return date(date.today().year, int(m[1]), int(m[2])) if m else _sheet_date(word)
    except ValueError: return None

async def _cmd_parse(request, text: str, ctx: dict) -> dict:
    """One entry from a command line: an optional kind word first (income / bill = not paid yet / expense, default an expense already paid), the amount ($ or decimals win, else the first number),
    a date word or date (default today), "from" or "to" and an account name (default the first cash account), and the rest as the label. Changes nothing."""
    gid, words = await _active_group(request), text.split()
    accounts = _accounts(gid)
    if not accounts: return {"error": "Finance has no account yet - add one in Finance > Accounts"}
    kind, confirmed = _CMD_KINDS.get(words[0].lower(), ("expense", 1)) if words else ("expense", 1)
    words = words[1:] if words and words[0].lower() in _CMD_KINDS else words
    acct = next((a for a in accounts if a["is_liquid"]), accounts[0])
    j = next((j for j, w in enumerate(words[:-1]) if w.lower() in ("from", "to")), None)
    if j is not None:
        name = words[j + 1].lower()
        acct = next((a for a in accounts if a["label"].lower().startswith(name)), None) or next((a for a in accounts if name in a["label"].lower()), None)
        if not acct: return {"error": f"""no account named like "{words[j + 1]}" - accounts: {", ".join(a["label"] for a in accounts)}"""}
        words = words[:j] + words[j + 2:]
    d = next((x for x in map(_cmd_date, words) if x), None)
    words = [w for w in words if not _cmd_date(w)] if d else words
    nums = [(j, _num(w)) for j, w in enumerate(words) if re.search(r"\d", w) and _num(w) is not None]
    pick = next((n for n in nums if "$" in words[n[0]]), None) or next((n for n in nums if "." in words[n[0]]), None) or (nums[0] if nums else None)
    if not pick or not pick[1]: return {"error": "no amount - e.g. @finance gas 40"}
    kind, confirmed = ("income", 1) if words[pick[0]].startswith("+") else (kind, confirmed)   # +1200 paycheck
    label = " ".join(w for j, w in enumerate(words) if j != pick[0]).strip(" -:,")
    if not label: return {"error": "say what it was for - e.g. @finance gas 40"}
    amount, d = abs(pick[1]) if kind == "income" else -abs(pick[1]), d or date.today()
    what = {"income": "Income", "bill": "Bill, not paid yet:", "expense": "Expense"}[kind]
    return {"summary": f"""{what} {_money(abs(amount))} {label} - {d.strftime("%a %m-%d")} - {acct["label"]} ({_load_groups().get(gid, {}).get("label", gid)})""", "args": {"gid": gid, "account_id": acct["id"], "date": d.isoformat(), "label": label, "amount": amount, "confirmed": confirmed}}

async def _cmd_run(request, args: dict) -> str:
    """Adds the entry _cmd_parse read, as Quick Add would."""
    if request.state.user.username not in _load_groups().get(args["gid"], {}).get("members", []): raise ValueError("you are not in that finance group")
    conn = _conn(args["gid"])
    conn.execute("INSERT INTO entries VALUES (?,?,?,?,?,?,?,?,?,?)", (uuid.uuid4().hex[:10], args["account_id"], args["date"], args["label"], args["amount"], "", 0, None, None, args["confirmed"]))
    conn.commit(); conn.close()
    return f"""added to Finance: {args["label"]} {_money(args["amount"])} on {args["date"]}{" (not paid yet)" if not args["confirmed"] else ""} - change or delete it in that day's view"""

# --- Routes ---

@router.get("/", response_class=HTMLResponse)
async def index(request: Request, join_group: str = ""):
    if join_group:
        groups = _load_groups()
        if join_group in groups and request.state.user.username in groups[join_group].get("members", []):
            await ENV["set_state"](request, join_group, scope="user", namespace="finance", key="active_group")
    gid = await _active_group(request)
    state = await TM._load(request)
    state["tabs"] = {**{k: dict(v) for k, v in TM.empty["tabs"].items()}, **state["tabs"]}   # tabs added since this person's tab state was saved
    await TM._save(request, state)
    state, panel_html = await _render_panel(request, state)
    tab_bar = await TM.tab_bar_fn(state, "fin-tab-bar", "finance", 1, allow_new=False, closable=False)
    return ENV["templates"].TemplateResponse(name="base.html", request=request, context={"request": request, "user": request.state.user, "nesting_level": 1, "shell_id": IM.branch_id,
        "toolbars": {"top": UI.toolbar(side="top", content=tab_bar, size="2.5rem", id="fin-top", nesting_level=1, start_open=True, locked=True)},
        "content": f'<div id="finance-panel" style="height:100%;overflow:hidden">{panel_html}</div><div id="fin-modal"></div>', "extra_css": CSS})   # fin-modal: the day view is swapped in here (an intent answer without hx-swap-oob is dropped)

@router.get("/export/{gid}")
async def export_db(gid: str, request: Request):
    groups = _load_groups()
    if gid not in groups or request.state.user.username not in groups[gid].get("members", []): return HTMLResponse("Not found or not a member", status_code=404)
    return FileResponse(_db_path(gid), filename=f"{gid}.db", media_type="application/x-sqlite3")

# --- CSS (module-specific calendar grid only - everything else reuses shared style.css classes) ---

CSS = """
.fin-cal-grid { display:flex; flex-direction:column; gap:var(--border-thick); border:var(--border-thick) solid var(--border); border-radius:var(--radius); overflow:hidden; }
.fin-week { display:grid; grid-template-columns:repeat(7,1fr); gap:var(--border-thick); background:var(--border); }
.fin-day { background:var(--bg); min-height:5rem; max-height:9rem; min-width:0; overflow:hidden; padding:0.25rem 0.3rem; cursor:pointer; display:flex; flex-direction:column; gap:0.05rem; font-size:calc(var(--font-size)*0.7); }
.fin-dow-row { background:transparent; }
.fin-dow { text-align:center; font-size:calc(var(--font-size)*0.7); color:var(--text_muted); text-transform:uppercase; padding:0.2rem 0; background:var(--bg_panel); }
.fin-day:hover { background:var(--accent_dim); }
.fin-day-other-month { opacity:0.4; }
.fin-day-today { border:var(--border-thick) solid var(--accent); }
.fin-day-num { font-weight:700; font-size:calc(var(--font-size)*0.8); }
.fin-entry { overflow:hidden; text-overflow:ellipsis; white-space:nowrap; }
.fin-day-liquid { margin-top:auto; font-weight:600; font-size:calc(var(--font-size)*0.4); }
.fin-rec-table td { padding:.1rem .15rem; }
.fin-cell { margin:0; padding:.15rem .3rem; min-width:0; }
.fin-c-text { width:10rem; } .fin-c-money { width:6.5rem; } .fin-c-day, .fin-c-int { width:3.6rem; } .fin-c-date { width:9rem; } .fin-c-kind, .fin-c-freq { width:6.5rem; } .fin-c-account { width:8rem; }
.fin-chart { position:relative; height:9rem; margin:1.2rem 0 1.6rem; }
.fin-chart svg { position:absolute; inset:0; width:100%; height:100%; overflow:visible; }
.fin-ch-lbl { position:absolute; transform:translate(-50%, .2rem); font-size:.65rem; color:var(--text_muted); white-space:nowrap; pointer-events:none; }
.fin-ch-dot { position:absolute; width:.55rem; height:.55rem; border-radius:50%; transform:translate(-50%, -50%); }
"""