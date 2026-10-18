# SPDX-License-Identifier: CC0-1.0
# Hill-climb for factors that have cr2 paths of length >= 3 whose first (even) strip leaves a
# clean factor; report near contacts between a_1 and later strips on such paths.
#
import sys, random, json
args = sys.argv[1:]
exec(open("/home/z/claude/ulhc-lean/checks/near_all.py").read().split("\nst = {}")[0])
def changed(run):
  cnt = {}
  for c in run:
    for e in cell_edges(c): cnt[e] = cnt.get(e, 0) + 1
  return {e for e, k in cnt.items() if k % 2}
def score(V, cells, F):
  n0 = ncomp(V, F)
  if n0 < 2: return 0, []
  cl = classes(V, F)
  if any(type3(F, cl, c) for c in cells): return 0, []
  cands = candidates(V, cells, F); pr = set(proper(V, cells, F)); memo = {}
  found = []; cnt = [0]
  def go(path):
    x = path[-1]
    if len(path) >= 3: cnt[0] += 1; found.append([r for r, _ in path])
    if len(x[0]) % 2 == 1 or len(path) >= 4 or cnt[0] > 200: return
    if x not in memo: memo[x] = tl_succ_all(V, cells, F, cands, x)
    for z in memo[x]:
      path.append(z); go(path); path.pop()
  for x in cands:
    if x[1] is None and x[0] in pr and len(x[0]) % 2 == 0:
      G1 = apply(F, [list(x[0])]); cl1 = classes(V, G1)
      if ncomp(V, G1) != n0 or any(type3(G1, cl1, c) for c in cells): continue
      go([x])
  return cnt[0], found
rng = random.Random(int(args[0]))
seen = 0
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from parse import split_top
SEEDS = []
for fn in ['/home/z/claude/runs/2026-10-09/long_climb.txt', '/home/z/claude/runs/2026-10-09/long_climb_run1.txt']:
  for line in open(fn):
    if line.startswith('LONG'):
      q = split_top(line); SEEDS.append((set(map(tuple, q[4])), {tuple(map(tuple, e)) for e in q[5]}))
for r in range(int(args[1])):
  SV, SF = rng.choice(SEEDS)
  V = set(SV); F = set(SF)
  Gr = ph.induced(V); cells = ph.unit_cells(Gr)
  for _ in range(rng.randint(0, 20)):
    alts = [c for c in cells if is_alt(F, c)]
    F = apply(F, [[rng.choice(alts)]])
  F = settle(V, cells, F)
  sc, found = score(V, cells, F)
  for it in range(30):
    moves = [[c] for c in cells if is_alt(F, c)]
    if not moves: break
    F2 = settle(V, cells, apply(F, [rng.choice(moves)]))
    s2, f2 = score(V, cells, F2)
    if s2 >= sc or rng.random() < 0.05: F, sc, found = F2, s2, f2
    if sc > 0:
      seen += 1
      for p in found:
        ch = changed(p[0])
        for j in range(2, len(p)):
          if (set(p[0]) & set(p[j])) or ({e for c in p[j] for e in cell_edges(c)} & ch):
            print('TOUCH', json.dumps([sorted(V), sorted(F), [list(map(list, q)) for q in p], j]), flush=True)
  if r % 20 == 0: print('round', r, 'instances with paths', seen, flush=True)
