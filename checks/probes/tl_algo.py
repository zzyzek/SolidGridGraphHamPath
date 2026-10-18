# SPDX-License-Identifier: CC0-1.0
# "TL" search: nodes are strips of F (BEGIN, CHAIN with the shared side toggled, single
# alternating cells). Link a -> b (a even, end u, start y_a): the separating side of b's start
# lies in an even set of sides light in F, plus u's lateral sides, that avoids y_a's sides and
# meets u only at its lateral sides. Sources: strips proper in F. Sinks: odd strips.
#
import sys, heapq
exec(open('/home/z/claude/ulhc-lean/checks/px_algo.py').read())
import networkx as nx

def strip_dir(r):
  return next(d for d in SIDES if nb(r[0], d) == r[1]) if len(r) > 1 else None

def candidates(V, cells, F):
  # (run, toggled side or None)
  out = []
  for c in cells:
    D = dark(F, c)
    if len(D) == 1:
      d = next(iter(D)); s = OPP[d]
      run = strip_from(cells, F, c, s)
      if run: out.append((tuple(run), None))
    if is_alt(F, c): out.append(((c,), None))
    if len(D) == 2 and not is_alt(F, c):
      for d1 in D:
        p = nb(c, d1)
        if p in cells and is_alt(F, p):
          d2 = next(iter(D - {d1})); s = OPP[d2]
          run = strip_from(cells, F, c, s, toggle=frozenset({side(c, d1)}))
          if run: out.append((tuple(run), side(c, d1)))
    if len(D) == 3:
      L = next(d for d in SIDES if d not in D)
      p = nb(c, OPP[L])
      if p in cells and is_alt(F, p):
        out.append(((c,), side(c, OPP[L])))
  return out

def light_graph(cells, F, extra, banned):
  # Dual multigraph of sides light in F plus `extra`, minus `banned`.
  #
  D = nx.MultiGraph()
  D.add_node('OUT')
  for c in cells:
    D.add_node(c)
    for d in SIDES:
      e = side(c, d)
      if (e in F and e not in extra) or e in banned: continue
      n = nb(c, d)
      if n in cells:
        if c < n: D.add_edge(c, n, key=e)
      else:
        D.add_edge(c, 'OUT', key=e)
  return D

def in_cycle(D, c, d):
  e = side(c, d); n = nb(c, d)
  b = n if n in D and n != 'OUT' and n in D.nodes and isinstance(n, tuple) and D.has_node(n) else 'OUT'
  if not D.has_edge(c, b, key=e): return False
  D2 = D.copy(); D2.remove_edge(c, b, key=e)
  return nx.has_path(D2, c, b)

def sep_sides(run, tog):
  # Sides whose crossing separates the start: the two laterals (strip of length >= 2), or
  # for a single cell the two light sides (either works).
  c = run[0]
  if len(run) > 1:
    s = strip_dir(run)
    return [(c, LATA[s]), (c, LATB[s])]
  return [(c, d) for d in SIDES]

def tl_search(V, cells, F):
  cl = classes(V, F)
  cands = candidates(V, cells, F)
  def proper_in_F(run, tog):
    if tog is not None: return False
    return tuple(run) in set(proper(V, cells, F))
  dist = {}; prev = {}; pq = []
  for x in cands:
    if proper_in_F(*x):
      dist[x] = len(x[0]); prev[x] = None; heapq.heappush(pq, (len(x[0]), x))
  memo = {}
  while pq:
    dd, x = heapq.heappop(pq)
    if dd > dist[x]: continue
    run, tog = x
    if len(run) % 2 == 1:
      seq = [x]
      while prev[seq[-1]] is not None: seq.append(prev[seq[-1]])
      return [r for r, _ in seq[::-1]]
    u = run[-1]; s = strip_dir(run); y = run[0]
    if x not in memo:
      extra = {side(u, LATA[s]), side(u, LATB[s])}
      banned = {side(y, d) for d in SIDES} | {side(u, s), side(u, OPP[s])}
      Dg = light_graph(cells, F, extra, banned)
      succ = []
      for z in cands:
        zr, zt = z
        if set(zr) & set(run): continue
        if zt is not None and zt not in extra: continue
        if zt is None and zr[0] in (nb(u, LATA[s]), nb(u, LATB[s])): continue
        if zt is not None:
          succ.append(z); continue
        if len(zr) == 1:
          # a single alternating cell: one of its light sides in a cycle
          ok = any(side(zr[0], d) not in F and in_cycle(Dg, zr[0], d) for d in SIDES)
        else:
          ok = any(in_cycle(Dg, c0, d) for c0, d in sep_sides(zr, zt))
        if ok: succ.append(z)
      memo[x] = succ
    for z in memo[x]:
      nd = dd + len(z[0])
      if nd < dist.get(z, 1 << 30):
        dist[z] = nd; prev[z] = x; heapq.heappush(pq, (nd, z))
  return None
