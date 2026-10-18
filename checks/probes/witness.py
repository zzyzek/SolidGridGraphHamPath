# SPDX-License-Identifier: CC0-1.0
# For pairwise-exact shortest paths (px_search): at each link a_i -> a_(i+1), is the start
# of a_(i+1) still separated in F xor a_i when the sides of earlier start and end cells are
# forbidden to the witness? (Separation = the lateral side is a non-bridge of the light dual.)
#
import sys, random
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/px_algo.py').read())
src = open('/home/z/claude/ulhc-lean/checks/depth2_climb.py').read()
exec("def settle" + src.split("def settle")[1].split("best = None")[0])
E3 = {}
exec(open('/home/z/claude/ulhc-lean/checks/l57_check.py').read().split('def run(')[0], E3)
_e = open('/home/z/claude/ulhc-lean/checks/even_t3.py').read()
exec('import random\nimport networkx as nx\ndef grow_shape' + _e.split('def grow_shape')[1].rsplit('def run(', 1)[0], E3)
import networkx as nx

def light_dual(cells, F, banned):
  D = nx.MultiGraph()
  for c in cells:
    D.add_node(c)
    for d in SIDES:
      e = side(c, d)
      if e in F or e in banned: continue
      n = nb(c, d)
      if n in cells:
        if c < n: D.add_edge(c, n, key=e)
      else:
        D.add_edge(c, 'OUT', key=e)
  return D

def nonbridge(D, c, d):
  # Side d of cell c is in a cycle of the dual multigraph.
  #
  e = side(c, d); n = nb(c, d)
  a, b = (c, n) if n in D else (c, 'OUT')
  if not D.has_edge(a, b, key=e): return False
  D2 = D.copy(); D2.remove_edge(a, b, key=e)
  return nx.has_path(D2, a, b)

def sep_side(r):
  # The lateral side of the start that separates (lat A side of the strip direction).
  #
  c = r[0]
  if len(r) == 1: return None
  s = next(d for d in SIDES if nb(c, d) == r[1])
  return c, LATA[s], LATB[s]

seed, trials = int(args[0]), int(args[1])
sizes = [int(x) for x in args[2].split(',')]
rng = random.Random(seed)
st = dict(links=0, ok=0, needs_banned=0)
for t in range(trials):
  W = rng.choice(sizes); Hh = rng.choice(sizes)
  V = E3['grow_shape'](W, Hh, rng)
  Fs = E3['two_factor'](V, rng)
  if Fs is None: continue
  V = set(V); F = {tuple(sorted(e)) for e in Fs}
  G = ph.induced(V); cells = ph.unit_cells(G)
  for _ in range(rng.randint(0, 50)):
    alts = [c for c in cells if is_alt(F, c)]
    if not alts: break
    F = apply(F, [[rng.choice(alts)]])
  F = settle(V, cells, F)
  if ncomp(V, F) < 2: continue
  seq = px_search(V, cells, F)
  if not seq or len(seq) < 3: continue
  for i in range(1, len(seq) - 1):
    nxt = seq[i + 1]
    banned = set()
    for r in seq[:i]:
      for c in (r[0], r[-1]):
        for d in SIDES: banned.add(side(c, d))
    Fa = apply(F, [list(seq[i])])
    if len(nxt) == 1:
      continue
    c, la, lb = sep_side(nxt)
    st['links'] += 1
    D = light_dual(cells, Fa, banned)
    if nonbridge(D, c, la) or nonbridge(D, c, lb):
      st['ok'] += 1
    else:
      st['needs_banned'] += 1
      print('NEEDS', sorted(V), sorted(F), seq, i, flush=True)
  if t % 5000 == 0: print('progress', t, st, flush=True)
print('final', st)
