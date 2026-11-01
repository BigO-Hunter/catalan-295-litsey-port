"""Build a set of modules through the lanes driver, each as soon as its in-set imports are built
(no level barriers).  Modules already queued/running are not resubmitted: their receipts are awaited.
usage: build_dag.py GB T0 Module...   (T0: epoch; receipts with ended >= T0 or a build after the source
counts as done).  Prints one line per module; stops submitting after the first failure."""
import os, sys, json, time, glob, subprocess, threading
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from closure_check import path_of, IMPORT
LANES = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'tools', 'lanes')
LANES = os.path.normpath(LANES)
PY = sys.executable
GB, T0, mods = sys.argv[1], float(sys.argv[2]), sys.argv[3:]
S = set(mods)
deps = {}
for m in mods:
    with open(path_of(m), encoding='utf-8') as fh:
        deps[m] = {d for d in IMPORT.findall(fh.read(20000).split('\nnamespace', 1)[0]) if d in S}
seen, REC, PEND = set(), {}, set()
def scan():
    """Index receipts (new files only, ended >= T0) and the targets queued or running."""
    for f in glob.glob(os.path.join(LANES, 'done', '*.json')):
        if f in seen or os.path.getmtime(f) < T0: continue
        seen.add(f)
        try: s = json.load(open(f, encoding='utf-8'))
        except Exception: seen.discard(f); continue
        t = s.get('target')
        if t in S and (t not in REC or s.get('ended', 0) > REC[t].get('ended', 0)): REC[t] = s
    PEND.clear()
    for d in ('queue', 'running'):
        for f in glob.glob(os.path.join(LANES, d, '*.json')):
            try: PEND.add(json.load(open(f, encoding='utf-8')).get('target'))
            except Exception: pass
def receipt(m): return REC.get(m)
def pending(m): return m in PEND
state = {}   # m -> 'sub' | 0 | rc
lock = threading.Lock()
def submit(m):
    r = subprocess.run([PY, '-I', '-X', 'utf8', 'scripts/claude/lanes.py', 'submit', m, GB], capture_output=True, text=True)
    rc = None
    for line in r.stdout.splitlines()[::-1]:
        if line.startswith('{') and '"rc"' in line: rc = json.loads(line).get('rc'); break
    with lock: state[m] = rc
    print(f'{m} rc={rc}', flush=True)
failed = False
while True:
    scan()
    with lock:
        for m in mods:
            if m in state and state[m] != 'wait': continue
            r = receipt(m)
            if r is not None and not pending(m):
                state[m] = r.get('rc'); print(f'{m} rc={state[m]} (receipt)', flush=True)
            elif pending(m): state[m] = 'wait'
        done = {m for m, v in state.items() if v == 0}
        if any(v not in (0, 'sub', 'wait', None) for v in state.values()): failed = True
        todo = [m for m in mods if m not in state and deps[m] <= done]
        for m in ([] if failed else todo):
            state[m] = 'sub'; threading.Thread(target=submit, args=(m,), daemon=True).start()
        if all(state.get(m) == 0 for m in mods): print('all built', flush=True); break
        if failed and not any(v in ('sub', 'wait') for v in state.values()): sys.exit('stopped: a module failed')
    time.sleep(5)
