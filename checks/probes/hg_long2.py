# SPDX-License-Identifier: CC0-1.0
# H-guided sequences (Theorem A2 construction) on long instances: are they static?
# For each instance: H from the ILP, every starting H-edge between two cycles.
#
import sys
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from hguided import *
from parse import split_top
from ham_ilp import ham_cycle
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
ex = []
for fn in sys.argv[1].split(','):
  for line in open(fn):
    if not line.startswith('LONG'): continue
    p = split_top(line); Vs = set(map(tuple, p[4])); F0 = {tuple(map(tuple, e)) for e in p[5]}
    G = P.induced(Vs); cells = P.unit_cells(G)
    Hl = ham_cycle(Vs)
    H = {P.ekey(a, b) for a, b in Hl}
    comp0 = comp_of(G, F0)
    for e in [e for e in H if comp0[e[0]] != comp0[e[1]]]:
      Fc = set(F0); seq = []; comp = comp0
      _, Ech = chain(G, Fc, comp, cells, lohi(e)[1] if lohi(e)[1] in cells else lohi(e)[0])
      try:
        for depth in range(12):
          comp = comp_of(G, Fc)
          r = walk_strip(G, Fc, H, cells, comp, Ech, e)
          Dn = D_field(G, Fc, H, cells)
          vals = sorted({Dn[c] for c in r})
          bump('Dvals_%s' % vals)
          seq.append(r); P.flip_run(Fc, r)
          if len(r) % 2 == 1: break
          comp2 = comp_of(G, Fc)
          chc, Ech = chain(G, Fc, comp2, cells, r[-1])
          t3 = [c for c in cells if type3(G, Fc, comp2, c)]
          if t3:
            on = [c for c in t3 if c in chc]
            seq.append([on[0]]); P.flip(Fc, P.cell_edges(on[0])); break
          Hon = [x for x in H if x in Ech]
          e = Hon[0]
      except Anomaly as a:
        bump('anomaly'); continue
      bump('len_%d' % len(seq))
      ok, why = static_ok(seq)
      bump('static' if ok else 'nonstatic_' + why)
      if not ok and len(ex) < 3: ex.append(seq)
print(st)
for x in ex: print('NONSTATIC', x)
