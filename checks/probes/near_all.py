# SPDX-License-Identifier: CC0-1.0
# Near contacts on all cr2 paths (length <= 4) from random stuck factors with G xor a_1 clean:
# does some a_j (j >= 3) share a cell with a_1, or a side that a_1 changes?
#
import sys, random, json
args = sys.argv[1:]
exec(open("/home/z/claude/ulhc-lean/checks/iter_test.py").read().split("\nst = {}\ndef bump")[0])
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
def changed(run):
  cnt = {}
  for c in run:
    for e in cell_edges(c): cnt[e] = cnt.get(e, 0) + 1
  return {e for e, k in cnt.items() if k % 2}
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  if t % 2000 == 0: print('progress', t, st, flush=True)
  W = rng.choice([8, 10, 12, 14]); Hh = rng.choice([8, 10, 12, 14])
  V = set(E3['grow_shape'](W, Hh, rng))
  Fs = E3['two_factor'](V, rng)
  if Fs is None: continue
  F = {tuple(sorted(e)) for e in Fs}
  Gr = ph.induced(V); cells = ph.unit_cells(Gr)
  for _ in range(rng.randint(0, 40)):
    alts = [c for c in cells if is_alt(F, c)]
    if not alts: break
    F = apply(F, [[rng.choice(alts)]])
  F = settle(V, cells, F)
  n0 = ncomp(V, F)
  if n0 < 2: continue
  cands = candidates(V, cells, F); pr = set(proper(V, cells, F)); memo = {}
  def go(path):
    x = path[-1]
    if len(path) >= 3:
      a1 = path[0][0]; aj = x[0]
      ch = changed(a1)
      share = set(a1) & set(aj)
      sides = {e for c in aj for e in cell_edges(c)} & ch
      if share or sides:
        bump('touch_%s_%s' % ('cell' if share else 'side', 'odd' if len(aj) % 2 else 'even'))
        print('TOUCH', json.dumps([sorted(V), sorted(F), [list(map(list, r)) for r, _ in path]]), flush=True)
      else: bump('far')
    if len(x[0]) % 2 == 1 or len(path) >= 4: return
    if x not in memo: memo[x] = tl_succ_all(V, cells, F, cands, x)
    for z in memo[x]:
      path.append(z); go(path); path.pop()
  for x in cands:
    if x[1] is None and x[0] in pr and len(x[0]) % 2 == 0:
      G1 = apply(F, [list(x[0])]); cl = classes(V, G1)
      if ncomp(V, G1) != n0 or any(type3(G1, cl, c) for c in cells): continue
      go([x])
print('final', st)
