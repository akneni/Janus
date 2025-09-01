# TLA+ Error Trace Viewer
# Desc: Just run this tool in the background. Whenever you copy a TLA+ error log to your keyboard for the first time, it will open a webpage. 
# Whenever you copy a new TLA+ error trace, just refresh that page. 


import os
import sys
from datetime import datetime
import hashlib
import time
import pyperclip
import webbrowser
import html
import pathlib
from dataclasses import dataclass

def pfmt(s: str, indent: int = 0, indent_step: int = 2) -> str:
    """
    Pretty-format a single TLA+ value string by *unwrapping once*:
      - If it is a sequence `<< ... >>`, split top-level elements onto new lines.
      - If it is a mapping/record `[ ... ]`, split top-level pairs onto new lines.
    Nested structures are left intact (no recursive formatting).
    """
    s = s.strip()
    if not s:
        return s

    # Detect single outer wrapper we want to unwrap
    if s.startswith("<<") and s.endswith(">>"):
        open_tok, close_tok = "<<", ">>"
    elif s.startswith("[") and s.endswith("]"):
        open_tok, close_tok = "[", "]"
    else:
        return s  # nothing to do

    inner = s[len(open_tok): -len(close_tok)]

    # Split `inner` by commas that are at top level (not inside [], {}, (), or << >>, and not in strings)
    items = []
    buf = []
    stack = []  # holds tokens: "[", "{", "(", "<<"
    i = 0
    in_str = False

    def push(tok): stack.append(tok)
    def pop(tok): 
        if stack and stack[-1] == tok: stack.pop()

    while i < len(inner):
        ch = inner[i]

        # Handle strings: respect \" escape
        if in_str:
            buf.append(ch)
            if ch == '"' and inner[i-1] != '\\':
                in_str = False
            i += 1
            continue

        if ch == '"':
            in_str = True
            buf.append(ch)
            i += 1
            continue

        # Handle paired seq tokens << >>
        if ch == '<' and i+1 < len(inner) and inner[i+1] == '<':
            push("<<"); buf.append("<<"); i += 2; continue
        if ch == '>' and i+1 < len(inner) and inner[i+1] == '>' and stack and stack[-1] == "<<":
            pop("<<"); buf.append(">>"); i += 2; continue

        # Brackets
        if ch in "[{(":
            push(ch); buf.append(ch); i += 1; continue
        if ch in "]})":
            # map closing to opening
            opener = {"}":"{", ")":"(", "]":"["}[ch]
            pop(opener); buf.append(ch); i += 1; continue

        # Top-level comma -> split
        if ch == ',' and not stack:
            items.append(''.join(buf).strip())
            buf = []
            i += 1
            # Swallow optional single space after comma
            if i < len(inner) and inner[i] == ' ':
                i += 1
            continue

        # Default: accumulate
        buf.append(ch)
        i += 1

    # Last piece
    tail = ''.join(buf).strip()
    if tail:
        items.append(tail)

    # Build output with one extra indentation level for items
    base = ' ' * indent
    ind2 = ' ' * (indent + indent_step)

    # Keep trailing commas off (caller examples show no trailing comma on last line)
    sep = ",\n" + ind2
    body = (ind2 + sep.join(items)) if items else ""

    # Surround with wrapper lines
    return f"{open_tok}\n{body}\n{base}{close_tok}"


@dataclass
class State:
    position: int
    name: str
    variables: dict[str, str]

    @staticmethod
    def from_blob(s: str):
        position = int(s.partition('position |-> ')[2].partition(',')[0].strip())
        name = s.partition('name |->')[2].partition(',\n')[0].strip().strip('"')

        def update_depth(s: str, stack: list[str], in_str: bool) -> tuple[list[str], bool]:
            i = 0
            while i < len(s):
                ch = s[i]

                if in_str:
                    if ch == '"' and (i == 0 or s[i-1] != '\\'):
                        in_str = False
                    i += 1
                    continue

                if ch == '"':
                    in_str = True
                    i += 1
                    continue

                if ch == '<' and i+1 < len(s) and s[i+1] == '<':
                    stack.append("<<")
                    i += 2
                    continue
                if ch == '>' and i+1 < len(s) and s[i+1] == '>' and stack and stack[-1] == '<<':
                    stack.pop()
                    i += 2
                    continue

                if ch in '[{(':
                    stack.append(ch)
                    i += 1
                    continue
                if ch in ']})':
                    need = {']': '[', '}': '{', ')': '('}[ch]
                    if stack and stack[-1] == need:
                        stack.pop()
                    i += 1
                    continue

                i += 1
            return stack, in_str

        variables: dict[str, str] = {}

        var_blob = s.partition('],\n')[-1]
        lines = var_blob.splitlines()

        stack: list[str] = []
        in_str = False
        cur_key: str | None = None
        cur_val_chunks: list[str] = []

        for raw_line in lines:
            line = raw_line.rstrip()

            if cur_key is None:
                if '|->' not in line:
                    continue
                k, _, v = line.partition('|->')
                cur_key = k.strip().strip(',')
                v = v.lstrip()

                cur_val_chunks = [v]
                stack, in_str = update_depth(v, stack, in_str)

                if not stack and v.endswith(','):
                    val = v.rstrip(',').strip()
                    if len(val) > 30:
                        val = pfmt(val)
                    variables[cur_key] = val
                    cur_key = None
                    cur_val_chunks = []
                continue

            cur_val_chunks.append(line)
            stack, in_str = update_depth(line, stack, in_str)

            if not stack and line.endswith(','):
                val = '\n'.join(cur_val_chunks).rstrip(',').strip()
                if len(val) > 30:
                    val = pfmt(val)
                variables[cur_key] = val
                cur_key = None
                cur_val_chunks = []

        if cur_key is not None:
            val = '\n'.join(cur_val_chunks).strip()
            if len(val) > 30:
                val = pfmt(val)
            variables[cur_key] = val

        return State(position, name, variables)

def generate_trace_dump(states: list[State], out_path: str = "trace-dump.html") -> str:
    """Render a list[State] into a dark-mode HTML file, highlighting changed values."""
    states = sorted(states, key=lambda s: s.position)

    def ordered_keys(curr: dict[str, str], prev: dict[str, str] | None):
        # show keys in a stable order: current keys first (in insertion order), then any prev-only keys (sorted)
        if prev is None:
            return curr.keys()
        extra_prev = [k for k in prev.keys() if k not in curr]
        return list(curr.keys()) + sorted(extra_prev)

    def render_vars(curr: dict[str, str], prev: dict[str, str] | None) -> str:
        rows = []
        for k in ordered_keys(curr, prev):
            v = curr.get(k, "∅")
            pv = None if prev is None else prev.get(k, None)
            changed = (prev is not None) and (v != pv)
            cls = "vv changed" if changed else "vv"
            rows.append(
                f"""<tr>
                        <td class="vk">{html.escape(k)}</td>
                        <td class="{cls}"><pre>{html.escape(v)}</pre></td>
                    </tr>"""
            )
        return "\n".join(rows) if rows else '<tr><td colspan="2" class="empty">∅</td></tr>'

    sections = []
    for idx, st in enumerate(states):
        prev_vars = None if idx == 0 else states[idx - 1].variables
        sections.append(f"""
        <section class="state">
            <button class="hdr" onclick="toggle(this)" aria-expanded="false">
                <span class="pill">#{st.position}</span>
                <span class="title">{html.escape(st.name or "(no name)")}</span>
                <span class="chev">▸</span>
            </button>
            <div class="body" hidden>
                <table class="kv">
                    <thead><tr><th>Variable</th><th>Value</th></tr></thead>
                    <tbody>
                        {render_vars(st.variables, prev_vars)}
                    </tbody>
                </table>
            </div>
        </section>""")

    html_doc = f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8"/>
<meta name="viewport" content="width=device-width, initial-scale=1"/>
<title>TLC Trace Dump</title>
<style>
:root {{
  --bg:#0c0f12; --panel:#131820; --panel2:#0f141b;
  --fg:#e6edf3; --fg-dim:#9aa7b3; --line:#1c2430;
  --pill:#0b3a97; --pill-fg:#cfe2ff;
  --changed-bg:#3a0e12;           /* dark red */
  --changed-border:#66252b;       /* subtle red border */
  --mono: ui-monospace, SFMono-Regular, Menlo, Consolas, "Liberation Mono", monospace;
  --sans: system-ui, -apple-system, Segoe UI, Roboto, Ubuntu, Cantarell, Noto Sans, sans-serif;
}}
* {{ box-sizing: border-box; }}
html, body {{ margin:0; padding:0; background:var(--bg); color:var(--fg); font-family:var(--sans); }}
header {{ padding:20px; border-bottom:1px solid var(--line); background:var(--panel2); position:sticky; top:0; z-index:10; }}
header h1 {{ margin:0 0 6px 0; font-size:18px; font-weight:600; }}
header .meta {{ color:var(--fg-dim); font-size:12px; }}

main {{ max-width:1200px; margin:24px auto; padding:0 16px 64px; }}
.state {{ border:1px solid var(--line); border-radius:12px; overflow:hidden; margin:14px 0; background:var(--panel); }}
.hdr {{
  width:100%; text-align:left; background:transparent; border:0; color:var(--fg);
  padding:14px 16px; display:flex; align-items:center; gap:12px; cursor:pointer;
}}
.hdr:hover {{ background:var(--panel2); }}
.title {{ font-weight:600; }}
.pill {{ background:var(--pill); color:var(--pill-fg); border-radius:999px; padding:2px 8px; font-size:12px; font-family:var(--mono); }}
.chev {{ margin-left:auto; color:var(--fg-dim); transition: transform .15s ease; }}
.hdr[aria-expanded="true"] .chev {{ transform: rotate(90deg); }}

.body {{ padding:0 16px 16px; background:var(--panel); }}
.kv {{ width:100%; border-collapse:collapse; border-spacing:0; }}
.kv thead th {{
  position:sticky; top:0; background:var(--panel2); color:var(--fg-dim);
  font-size:12px; text-transform:uppercase; letter-spacing:.06em; padding:10px; text-align:left;
  border-bottom:1px solid var(--line);
}}
.kv td {{ vertical-align:top; border-bottom:1px solid var(--line); }}
.kv .vk {{
  white-space:nowrap; width:220px; color:var(--fg-dim); font-family:var(--mono);
  padding:10px; border-right:1px solid var(--line); background:var(--panel2);
}}
.kv .vv {{ padding:10px; }}
.kv .vv.changed {{
  background:var(--changed-bg);
  border:1px solid var(--changed-border);
  border-radius:8px;
}}
pre {{
  margin:0; font-family:var(--mono); font-size:12.5px; line-height:1.45;
  white-space:pre-wrap; word-break:break-word; color:var(--fg);
}}
.empty {{ color:var(--fg-dim); text-align:center; padding:14px; }}
footer {{ color:var(--fg-dim); font-size:12px; text-align:center; padding:24px 0; }}
</style>
<script>
function toggle(btn) {{
  const body = btn.nextElementSibling;
  const expanded = btn.getAttribute('aria-expanded') === 'true';
  btn.setAttribute('aria-expanded', String(!expanded));
  body.hidden = expanded;
}}
</script>
</head>
<body>
<header>
  <h1>TLC Trace Dump</h1>
  <div class="meta">{len(states)} state{'' if len(states) == 1 else 's'}</div>
</header>
<main>
  {"".join(sections)}
</main>
<footer>Generated by {sys.argv[0]}</footer>
</body>
</html>"""
    path = pathlib.Path(out_path).resolve()
    path.write_text(html_doc, encoding="utf-8")
    return str(path)

first_run = True
last_hash = ''
counter = 0
while True:
    text_dump = pyperclip.paste()
    if text_dump.startswith('<<') and '_TEAction' in text_dump:
        dump_hash = hashlib.sha256(text_dump.encode()).hexdigest()
        if dump_hash == last_hash:
            continue
        
        counter += 1
        last_hash = dump_hash
        states_blobs = text_dump.split('_TEAction')[1:]
        states: list[State] = []

        for blob in states_blobs:
            states.append(State.from_blob(blob))

        generate_trace_dump(states)
        print(f"generated trace dump {counter=}")
        if first_run:
            first_run = False
            webbrowser.open(os.path.abspath('trace-dump.html'))
    time.sleep(0.5)