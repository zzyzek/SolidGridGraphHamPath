# SPDX-License-Identifier: CC0-1.0
# Enumerate TL paths up to (min weight + slack) and classify invalid ones by the first
# failing step: 'pattern' (not a strip of the current factor) or 'sep'; and by whether an
# earlier non-consecutive strip is adjacent to the failing strip.
#
import sys
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/tl_algo.py').read())
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from parse import split_top

def tl_succ_all(V, cells, F, cands, x):
  run, tog = x
  u = run[-1]; s = strip_dir(run); y = run[0]
  extra = {side(u, LATA[s]), side(u, LATB[s])}
  banned = {side(y, d) for d in SIDES} | {side(u, s), side(u, OPP[s])}
  Dg = light_graph(cells, F, extra, banned)
  succ = []
  for z in cands:
    zr, zt = z
    if set(zr) & set(run): continue
    if zt is not None and zt not in extra: continue
    if zt is None and zr[0] in (nb(u, LATA[s]), nb(u, LATB[s])): continue
    if zt is not None: succ.append(z); continue
    if len(zr) == 1:
      ok = any(side(zr[0], d) not in F and in_cycle(Dg, zr[0], d) for d in SIDES)
    else:
      ok = any(in_cycle(Dg, c0, d) for c0, d in sep_sides(zr, zt))
    if ok: succ.append(z)
  return succ

def touches(r1, r2):
  A = set(r1)
  return any(c in A or any(nb(c, d) in A for d in SIDES) for c in r2)

st = {}
def bump(k): st[k] = st.get(k, 0) + 1
examples = []
for fn in args[0].split(','):
  for line in open(fn):
    if not line.startswith('LONG'): continue
    p = split_top(line); V = set(map(tuple, p[4])); F = {tuple(map(tuple, e)) for e in p[5]}
    G = ph.induced(V); cells = ph.unit_cells(G)
    best = tl_search(V, cells, F); wmin = sum(len(r) for r in best)
    cands = candidates(V, cells, F)
    pr = set(proper(V, cells, F))
    memo = {}
    paths = []
    def go(path, w):
      x = path[-1]
      if len(x[0]) % 2 == 1: paths.append(list(path)); return
      if len(path) >= 5: return
      if x not in memo: memo[x] = tl_succ_all(V, cells, F, cands, x)
      for z in memo[x]:
        if w + len(z[0]) <= wmin + int(args[1]):
          path.append(z); go(path, w + len(z[0])); path.pop()
    for x in cands:
      if x[1] is None and x[0] in pr: go([x], len(x[0]))
    n0 = ncomp(V, F)
    for p_ in paths:
      runs = [r for r, _ in p_]
      # counts along the path while the factor stays a 2-factor
      Fc = F; lowest = n0; broke = False
      for r in runs:
        Fc = apply(Fc, [list(r)])
        if not is_factor(V, Fc): broke = True; break
        lowest = min(lowest, ncomp(V, Fc))
      bump('prefix_lower' if lowest < n0 else ('prefix_broken' if broke else 'prefix_NOT_lower'))
      if lowest >= n0 and not broke: print('NOTLOWER', runs, flush=True)
      Fi = F; bad = None
      for i, r in enumerate(runs):
        if r not in set(proper(V, cells, Fi)):
          ok_pat = (len(r) == 1 and is_alt(Fi, r[0])) or (len(r) > 1 and strip_from(cells, Fi, r[0], strip_dir(r)) == list(r))
          bad = (i, 'sep' if ok_pat else 'pattern'); break
        Fi = apply(Fi, [list(r)])
      w = sum(len(r) for r in runs)
      if bad is None: bump('valid_w%+d' % (w - wmin)); continue
      i, why = bad
      Fq = F; clean = True
      for r in runs[:i]:
        Fq = apply(Fq, [list(r)])
        if ncomp(V, Fq) != n0: clean = False
      bump('clean%s_%s' % (clean, why))
      if clean and len(examples) < 4: examples.append((sorted(V), sorted(F), runs, i, why, best))
      far = any(touches(runs[j], runs[i]) for j in range(i - 1))
      bump('bad_%s_touch%s_w%+d' % (why, far, w - wmin))
print(sorted(st.items()))
import json
for e in examples: print('EX', json.dumps([e[0], e[1], [list(map(list, r)) for r in e[2]], e[3], e[4], [list(map(list, r)) for r in e[5]]]))
