# /modules/finance/finance.py
"""
Finance - simple, AuDHD-friendly household cash flow tracker.
Data lives in one SQLite file per group (data/finance/{group_id}.db) - directly exportable,
directly readable by an external widget app with no server involvement.
Liquid cash and debt are tracked separately and never netted automatically - the goal is
two numbers a person can hold in their head, not a single misleading net-worth figure.
"""
import json, uuid, sqlite3, calendar, asyncio
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
_NOTIFY_TASK = None

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

def _balances_at(gid: str, target: date) -> dict:
    conn = _conn(gid); out = {}
    for a in [dict(r) for r in conn.execute("SELECT * FROM accounts")]:
        asof = date.fromisoformat(a["asof"]) if a.get("asof") else target
        confirmed_delta = conn.execute("SELECT COALESCE(SUM(amount),0) s FROM entries WHERE account_id=? AND confirmed=1 AND date>? AND date<=?", (a["id"], asof.isoformat(), target.isoformat())).fetchone()["s"]
        pending_delta = conn.execute("SELECT COALESCE(SUM(amount),0) s FROM entries WHERE account_id=? AND confirmed=0", (a["id"],)).fetchone()["s"] if target >= date.today() else 0.0
        out[a["id"]] = {**a, "balance": a["balance"] + confirmed_delta + pending_delta, "is_liquid": bool(a["is_liquid"])}
    conn.close()
    return out


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
    conn.close()
    by_day = {}
    for e in entries: by_day.setdefault(e["date"], []).append(dict(e))
    weeks, week, d = [], [], grid_start
    while d <= grid_end:
        week.append({"date": d, "entries": by_day.get(d.isoformat(), []), "liquid": _liquid_total(_balances_at(gid, d)), "in_month": d.month == center_month and d.year == center_year})
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
                   <div class="fin-day-num">{d.day}</div>{rows}{more}
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
    return UI.modal("fin-day", d.strftime("%A, %B %d, %Y"), rows or '<div class="dim">Nothing scheduled this day.</div>')

# --- Quick add / correction ---

def _quick_add_html(gid: str) -> str:
    accounts = _accounts(gid)
    opts = "".join(f'<option value="{a["id"]}">{_esc(a["label"])}</option>' for a in accounts)
    return f"""<form hx-post="/im/in" hx-target="body" hx-swap="none" hx-include="this" style="display:flex;flex-direction:column;gap:.4rem">
                   <div style="display:flex;gap:.4rem">
                       <input type="number" name="amount" step="0.01" min="0" placeholder="$ per unit" class="module-select" style="flex:1" required>
                       <input type="number" name="qty" step="any" min="0" value="1" placeholder="x qty" class="module-select" style="width:5rem">
                       <label style="display:flex;align-items:center;gap:.4rem;font-size:.8rem"><input type="checkbox" name="pending" value="1" checked> Not paid yet (bill I owe)</label>
                   </div>
                   <select name="kind" class="module-select"><option value="expense">Expense</option><option value="income">Income</option></select>
                   <select name="account_id" class="module-select">{opts or '<option value="">Add an account first</option>'}</select>
                   <input type="text" name="label" placeholder="e.g. Groceries, Gas" class="module-select" required>
                   <input type="number" name="amount" step="0.01" min="0" placeholder="Amount" class="module-select" required>
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

# --- Panels ---

async def _panel_calendar(request, gid):
    today = date.today()
    ym = await ENV["get_state"](request, scope="user", namespace="finance", key="cal_ym") or {"y": today.year, "m": today.month}
    return f"""<div style="padding:.9rem;height:100%;overflow-y:auto;box-sizing:border-box">
                   {_calendar_html(gid, ym["y"], ym["m"])}
                   <div class="fsect-hd">Pending Bills</div>{_pending_html(gid)}
                   <div class="fsect-hd" style="margin-top:1rem">Quick Add</div>
                   {_quick_add_html(gid)}
                   <div class="fsect-hd" style="margin-top:1rem">Correct a Balance</div>
                   <p class="dim tiny">Set what an account actually has right now - everything projected forward recalculates from this point. No need to find and fix individual past entries.</p>
                   {_correction_html(gid)}
               </div>"""

def _panel_accounts(gid): return f'<div style="padding:.9rem;height:100%;overflow-y:auto;box-sizing:border-box">{_accounts_list_html(gid)}<div class="fsect-hd" style="margin-top:1rem">Add / Edit Account</div><div id="fin-account-form">{_account_form_html()}</div></div>'
def _panel_recurring(gid): return f'<div style="padding:.9rem;height:100%;overflow-y:auto;box-sizing:border-box">{_recurring_list_html(gid)}<div class="fsect-hd" style="margin-top:1rem">Add / Edit Recurring Item</div><div id="fin-recurring-form">{_recurring_form_html(gid)}</div></div>'

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
    if active == "recurring": return state, _panel_recurring(gid)
    if active == "settings": return state, _panel_settings(request, gid)
    if active == "breakdown": return state, _panel_breakdown(gid)
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

def _ensure_notify_task():
    global _NOTIFY_TASK
    if _NOTIFY_TASK is None or _NOTIFY_TASK.done(): _NOTIFY_TASK = asyncio.create_task(_notify_loop())

# --- Init ---

def init_module(env: dict):
    global ENV, UI, BI, IM, TM
    ENV.update(env)
    UI = ENV["templates"].env.globals.get("UI")
    BI = ENV["tools"]["built_ins"]
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    IM = ENV["InterfaceManager"](nesting_level=1, db_path="finance_im.db")
    TM = BI.TabManager(namespace="finance", tab_bar_id="fin-tab-bar", content_id="finance-panel", render_content_fn=_render_panel, intent_prefix="finance", IM=IM, scope="user", nesting_level=1, allow_new=False, closable=False, empty={"tabs": {"calendar":{"id":"calendar","order":0,"label":"Calendar","icon":"&#x1F4C5;"}, "accounts":{"id":"accounts","order":1,"label":"Accounts","icon":"&#x1F3E6;"}, "breakdown":{"id":"breakdown","order":2,"label":"Breakdown","icon":"&#x1F4CA;"}, "recurring":{"id":"recurring","order":3,"label":"Recurring","icon":"&#x1F501;"}, "settings":{"id":"settings","order":4,"label":"Settings","icon":"&#x2699;"}}, "active":"calendar"})
    IM.scripts.update({
        "finance_calendar_nav": [_h_calendar_nav], "finance_day_open": [_h_day_open],
        "finance_quick_add": [_h_quick_add], "finance_correction": [_h_correction],
        "finance_entry_save": [_h_entry_save], "finance_entry_delete": [_h_entry_delete],
        "finance_account_form": [_h_account_form], "finance_account_save": [_h_account_save], "finance_account_delete": [_h_account_delete],
        "finance_recurring_form": [_h_recurring_form], "finance_recurring_save": [_h_recurring_save], "finance_recurring_delete": [_h_recurring_delete],
        "finance_pending_pay_now": [_h_pending_pay_now], "finance_pending_mark_paid": [_h_pending_mark_paid],
        "finance_group_create": [_h_group_create], "finance_group_set_default": [_h_group_set_default], "finance_group_leave": [_h_group_leave],
        "finance_group_switch": [_h_group_switch], "finance_group_members_save": [_h_group_members_save], "finance_threshold_save": [_h_threshold_save]})
    _ensure_notify_task()
    print("[finance] ready")

# --- Intent handlers ---

async def _refresh_calendar(request, gid, imr):
    ym = await ENV["get_state"](request, scope="user", namespace="finance", key="cal_ym") or {"y": date.today().year, "m": date.today().month}
    imr.oob(_calendar_html(gid, ym["y"], ym["m"]), "fin-calendar", swap="outerHTML")

async def _h_calendar_nav(request, payload, imr):
    await ENV["set_state"](request, {"y": int(payload.get("year")), "m": int(payload.get("month"))}, scope="user", namespace="finance", key="cal_ym")
    gid = await _active_group(request)
    imr.oob(_calendar_html(gid, int(payload.get("year")), int(payload.get("month"))), "fin-calendar", swap="outerHTML")
    return imr

async def _h_day_open(request, payload, imr):
    gid = await _active_group(request)
    imr.raw(_day_detail_html(gid, date.fromisoformat(payload.get("date"))))
    return imr

async def _h_quick_add(request, payload, imr):
    gid = await _active_group(request)
    sign = 1 if payload.get("kind") == "income" else -1
    amt = float(payload.get("amount",0) or 0) * float(payload.get("qty",1) or 1)
    confirmed = 0 if payload.get("pending") == "1" else 1
    conn = _conn(gid)
    conn.execute("INSERT INTO entries VALUES (?,?,?,?,?,?,?,?,?,?)", (uuid.uuid4().hex[:10], payload.get("account_id",""), payload.get("date", date.today().isoformat()), payload.get("label","").strip(), sign*abs(amt), "", 0, None, None, confirmed))
    conn.commit(); conn.close()
    await _refresh_calendar(request, gid, imr)
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
    if e: imr.raw(_day_detail_html(gid, date.fromisoformat(e["date"])))
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
    imr.raw(_day_detail_html(gid, date.fromisoformat(e["date"])))
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
    return imr

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

# _h_quick_add - multiply before signing
async def _h_quick_add(request, payload, imr):
    gid = await _active_group(request)
    sign = 1 if payload.get("kind") == "income" else -1
    amt = float(payload.get("amount",0) or 0) * float(payload.get("qty",1) or 1)
    conn = _conn(gid)
    conn.execute("INSERT INTO entries VALUES (?,?,?,?,?,?,?,?,?,?)", (uuid.uuid4().hex[:10], payload.get("account_id",""), payload.get("date", date.today().isoformat()), payload.get("label","").strip(), sign*abs(amt), "", 0, None, None, 1))
    conn.commit(); conn.close()
    await _refresh_calendar(request, gid, imr)
    return imr

async def _h_pending_pay_now(request, payload, imr):
    """Money leaves today, regardless of the bill's original due date."""
    gid = await _active_group(request)
    conn = _conn(gid)
    conn.execute("UPDATE entries SET date=?, confirmed=1 WHERE id=?", (date.today().isoformat(), payload.get("id","")))
    conn.commit(); conn.close()
    await _refresh_calendar(request, gid, imr)
    return imr

async def _h_pending_mark_paid(request, payload, imr):
    """Already handled elsewhere (e.g. autopay) - stop reserving against it, but don't touch today's actual liquid; keeps its original date so normal accounting picks it up on/after that date."""
    gid = await _active_group(request)
    conn = _conn(gid)
    conn.execute("UPDATE entries SET confirmed=1 WHERE id=?", (payload.get("id",""),))
    conn.commit(); conn.close()
    await _refresh_calendar(request, gid, imr)
    return imr

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
                       <button class="cm-qbtn" hx-post="/im/in" hx-target="#finance-panel" hx-swap="innerHTML" hx-vals='{{"type":"finance_pending_pay_now","lvl":1,"id":"{e["id"]}"}}'>Pay Now</button>
                       <button class="cm-qbtn" hx-post="/im/in" hx-target="#finance-panel" hx-swap="innerHTML" hx-vals='{{"type":"finance_pending_mark_paid","lvl":1,"id":"{e["id"]}"}}'>Mark Paid</button>
                   </div>"""
    return out

# --- Routes ---

@router.get("/", response_class=HTMLResponse)
async def index(request: Request, join_group: str = ""):
    if join_group:
        groups = _load_groups()
        if join_group in groups and request.state.user.username in groups[join_group].get("members", []):
            await ENV["set_state"](request, join_group, scope="user", namespace="finance", key="active_group")
    gid = await _active_group(request)
    state = await TM._load(request)
    state, panel_html = await _render_panel(request, state)
    tab_bar = await TM.tab_bar_fn(state, "fin-tab-bar", "finance", 1, allow_new=False, closable=False)
    return ENV["templates"].TemplateResponse(name="base.html", request=request, context={"request": request, "user": request.state.user, "nesting_level": 1, "shell_id": IM.branch_id,
        "toolbars": {"top": UI.toolbar(side="top", content=tab_bar, size="2.5rem", id="fin-top", nesting_level=1, start_open=True, locked=True)},
        "content": f'<div id="finance-panel" style="height:100%;overflow:hidden">{panel_html}</div>', "extra_css": CSS})

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
"""