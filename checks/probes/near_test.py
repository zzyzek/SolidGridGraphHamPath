# SPDX-License-Identifier: CC0-1.0
# Near cases: on minimum cr2 paths from random stuck factors, does a strip a_j (j >= 3)
# share or touch a cell of a_1 (sides or corners), and is G xor a_1 clean then?
#
import sys, random, json
args = sys.argv[1:]
exec(open("/home/z/claude/ulhc-lean/checks/iter_test.py").read().split("\nst = {}\ndef bump")[0])
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
def touch(r1, r2, diag):
  A = set(r1)
  for c in r2:
    for dx in (-1, 0, 1):
      for dy in (-1, 0, 1):
        if not diag and abs(dx) + abs(dy) > 1: continue
        if (c[0] + dx, c[1] + dy) in A: return True
  return False
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
  if ncomp(V, F) < 2: continue
  d, p = min_path(V, cells, F, None)
  if p is None or len(p) < 3: continue
  bump('len%d' % len(p))
  G1 = apply(F, [list(p[0])]); cl = classes(V, G1)
  clean = ncomp(V, G1) == ncomp(V, F) and not any(type3(G1, cl, c) for c in cells)
  for j in range(2, len(p)):
    if touch(p[0], p[j], False): bump('side_touch_clean%s' % clean); print('TOUCH', clean, json.dumps([sorted(V), sorted(F), [list(map(list, r)) for r in p], j]), flush=True)
    elif touch(p[0], p[j], True): bump('corner_touch')
print('final', st)
