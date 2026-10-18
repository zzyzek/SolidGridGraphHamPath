#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
#
# Exact brute force for Hamiltonian s-t paths in a grid graph (any point set, solid or not).
# DFS from s with pruning; every pruning rule is a necessary condition for the partial path to
# extend to a Hamiltonian s-t path:
#   * colour balance (checked once): a path alternates colours,
#   * the unvisited points plus the current end stay connected,
#   * an unvisited point other than t needs two usable neighbours (unvisited or the current end),
#     t needs one.
#
import sys

sys.setrecursionlimit(100000)


def nbrs4(p):
  x, y = p
  return ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1))


def colour_ok(V, s, t):
  n = len(V)
  blk = sum(1 for p in V if ((p[0] + p[1]) % 2) == 0)
  wht = n - blk
  cs, ct = ((s[0] + s[1]) % 2), ((t[0] + t[1]) % 2)
  if (n % 2) == 0:
    return ( (cs != ct) and (blk == wht) )
  if cs != ct:
    return False
  return ( (blk == (wht + 1)) if (cs == 0) else (wht == (blk + 1)) )


# Returns a Hamiltonian path s..t (list) or None. `limit` caps DFS nodes (None = no cap);
# exceeding it raises RuntimeError.
#
def brute_hp(V, s, t, limit=None):
  V = frozenset(V)
  if ( (s not in V) or (t not in V) or (s == t) ):
    return None
  if len(V) == 2:
    return ( [s, t] if (t in nbrs4(s)) else None )
  if not colour_ok(V, s, t):
    return None
  adj = {p: [q for q in nbrs4(p) if q in V] for p in V}
  unv = set(V)
  unv.discard(s)
  path = [s]
  count = [0]

  def connected(cur):
    # Unvisited points plus `cur` connected.
    #
    seen = {cur}
    st = [cur]
    while st:
      u = st.pop()
      for v in adj[u]:
        if ( (v in unv) and (v not in seen) ):
          seen.add(v)
          st.append(v)
    return ( len(seen) == (len(unv) + 1) )

  def degree_ok(cur):
    # Each unvisited point other than t has two path neighbours among the unvisited points and
    # `cur`; t has one.
    #
    for u in unv:
      k = 0
      for v in adj[u]:
        if ( (v in unv) or (v == cur) ):
          k += 1
      if k < ( 1 if (u == t) else 2 ):
        return False
    return True

  def dfs(cur):
    count[0] += 1
    if ( (limit is not None) and (count[0] > limit) ):
      raise RuntimeError("brute limit")
    if not unv:
      return ( cur == t )
    if not connected(cur):
      return False
    if not degree_ok(cur):
      return False
    cand = [v for v in adj[cur] if v in unv]
    for v in cand:
      if ( (v == t) and (len(unv) > 1) ):
        continue
      unv.discard(v)
      path.append(v)
      if dfs(v):
        return True
      path.pop()
      unv.add(v)
    return False

  if dfs(s):
    return list(path)
  return None


if __name__ == "__main__":
  import json
  d = json.load(sys.stdin)
  V = [tuple(p) for p in d["points"]]
  P = brute_hp(V, tuple(d["s"]), tuple(d["t"]))
  print("yes" if P else "no")
