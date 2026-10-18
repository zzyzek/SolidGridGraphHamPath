# SPDX-License-Identifier: CC0-1.0
# Completeness step: G clean, s proper even with G xor s clean, F = G xor s, a = reverse of s.
# Q = minimum no-chain path of F (Lean-exact). Classify: does Q's first strip touch a (which
# cell), do later strips touch or get created by a's end, and is there a path of G of the
# expected shape (Q itself, s + Q, or via a shortcut)? Reports any case with no path in G.
#
import sys, random, json
myargs = sys.argv[1:]
sys.argv = [sys.argv[0], myargs[0], myargs[1], '1']
exec(open('/home/z/claude/ulhc-lean/checks/iter_exact.py').read().split("\nst = {}\ndef bump")[0])
from parse import split_top
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
SEEDS = []
for fn in ['/home/z/claude/runs/2026-10-09/long_climb.txt', '/home/z/claude/runs/2026-10-09/long_climb_run1.txt']:
  for line in open(fn):
    if line.startswith('LONG'):
      q = split_top(line); SEEDS.append((set(map(tuple, q[4])), {tuple(map(tuple, e)) for e in q[5]}))
def cells_of_x(x): return [cellj(x[0], x[1], j) for j in range(x[2])]
def touches(x, Acells):
  A = set(e for q in Acells for e in csides(q))
  return any(e in A for q in cells_of_x(x) for e in csides(q))
rng = random.Random(int(myargs[0]))
for t in range(int(myargs[1])):
  if t % 100 == 0: print('progress', t, st, flush=True)
  V, G = rng.choice(SEEDS); V = set(V); G = set(G)
  cells = set(ph.unit_cells(ph.induced(V)))
  for _ in range(rng.randint(0, 15)):
    alts = [c for c in cells if is_alt(G, c)]
    if not alts: break
    G = apply(G, [[rng.choice(alts)]])
  G = settle(V, cells, G)
  n0 = ncomp(V, G)
  if n0 < 2: continue
  clG = classes(V, G)
  if any(type3(G, clG, c) for c in cells): continue
  ss = [x for x in strips_of(G, cells) if x[2] % 2 == 0 and clG[lat1(x)[0]] != clG[lat1(x)[1]]]
  rng.shuffle(ss)
  for s in ss[:3]:
    Sc = cells_of_x(s)
    F = apply(G, [Sc]); clF = classes(V, F)
    if any(type3(F, clF, c) for c in cells): continue
    if ncomp(V, F) < 2: continue
    bump('situations')
    dF, Q = min_path_exact(V, cells, F)
    if Q is None: bump('F_no_path'); continue
    q = Q[0]
    tq = touches(q, Sc)
    bump('q_touches' if tq else 'q_far')
    if tq:
      ra = (Sc[-1], {'t': 'b', 'b': 't', 'l': 'r', 'r': 'l'}[s[1]], s[2])
      if tuple(q) == ra: bump('q_is_rev')
      else:
        bump('q_other_' + ('even' if q[2] % 2 == 0 else 'odd'))
        lk = links(V, cells, G, clG, tuple(s), {})
        inl = [ch for z, ch in lk if z == tuple(q)]
        lq = lat1(q); near = lq in set(csides(Sc[-1]))
        if inl:
          bump('sQ_link_' + ('chain' if inl[0] else 'plain') + ('_nearpair' if near else '_farpair'))
          if len(Q) >= 2:
            q2 = Q[1]; eq = cells_of_x(q)[-1]
            ch2 = any(e in set(csides(eq)) for x in cells_of_x(q2) for e in csides(x))
            bump('q2_chain_of_q' if ch2 else 'q2_nochain')
            eq = cells_of_x(q)[-1]; q2c = cells_of_x(q2)
            rel = ('q2_starts_beside_eq' if any(abs(q2c[0][0]-eq[0]) + abs(q2c[0][1]-eq[1]) == 1 for _ in [0]) else 'q2_starts_away')
            bump(rel + '_qlen%d' % min(q[2], 6))
            if rel == 'q2_starts_beside_eq': print('Q2BESIDE', json.dumps([sorted(V), sorted(G), Sc, Q]), flush=True)
            if ch2: print('Q2CHAIN', json.dumps([sorted(V), sorted(G), Sc, Q]), flush=True)
        else:
          vq = clG[lq[0]] != clG[lq[1]]
          bump('NO_LINK_' + ('q_valid_in_G' if vq else 'q_not_valid') + ('_nearpair' if near else '_farpair'))
        print('QOTHER', json.dumps([sorted(V), sorted(G), Sc, q]), flush=True)
    dG, P = min_path_exact(V, cells, G)
    if P is None:
      bump('G_NO_PATH'); print('GNOPATH', json.dumps([sorted(V), sorted(G), Sc]), flush=True)
print('final', st)
