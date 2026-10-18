#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
# Sanity check of the Lean algorithm against brute force.
# Generates point sets V (4-connected or not, solid by the Lean definition: every missing
# point escapes left of V by king moves through missing points), decides Hamiltonicity of the
# node-induced grid graph by backtracking, and writes a Lean file that evaluates `ulhc` and
# `T.ulhcT` on each set. Usage: sanity_gen.py mode count seed out.lean truth.json
#   mode = box4  : every solid subset of a 4x4 box with >= 4 points (count, seed ignored)
#   mode = rand  : `count` random solid sets grown by adding neighbours, 4..28 points
#   mode = blocks: `count` random solid unions of 2x2 blocks (often Hamiltonian), up to ~40 points
import sys, json, random, itertools
mode, count, seed, outl, outj = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]

def solid(V):
  if not V: return True
  xs = [p[0] for p in V]; ys = [p[1] for p in V]
  x0, x1, y0, y1 = min(xs) - 1, max(xs) + 1, min(ys) - 1, max(ys) + 1
  # flood missing points from the frame (all frame points escape: the left column is left of V)
  seen = set(); st = []
  for x in range(x0, x1 + 1):
    for y in (y0, y1): st.append((x, y))
  for y in range(y0, y1 + 1):
    for x in (x0, x1): st.append((x, y))
  while st:
    p = st.pop()
    if p in seen or p in V or not (x0 <= p[0] <= x1 and y0 <= p[1] <= y1): continue
    seen.add(p)
    for dx in (-1, 0, 1):
      for dy in (-1, 0, 1): st.append((p[0] + dx, p[1] + dy))
  return all(p in seen or p in V for x in range(x0, x1 + 1) for y in range(y0, y1 + 1) for p in [(x, y)])

def nbrs(V, p):
  return [q for q in ((p[0]+1,p[1]),(p[0]-1,p[1]),(p[0],p[1]+1),(p[0],p[1]-1)) if q in V]

def ham(V):
  V = set(V); n = len(V)
  if n < 4 or n % 2: return False
  start = min(V); adj = {p: nbrs(V, p) for p in V}
  if any(len(a) < 2 for a in adj.values()): return False
  path = [start]; used = {start}
  def go():
    if len(path) == n: return start in adj[path[-1]]
    for q in adj[path[-1]]:
      if q not in used:
        used.add(q); path.append(q)
        if go(): return True
        used.discard(q); path.pop()
    return False
  return go()

shapes = []
def norm(V):
  mx = min(p[0] for p in V); my = min(p[1] for p in V)
  return frozenset((p[0] - mx, p[1] - my) for p in V)
def connected(V):
  st = [min(V)]; seen = set()
  while st:
    p = st.pop()
    if p in seen: continue
    seen.add(p); st.extend(nbrs(V, p))
  return len(seen) == len(V)
if mode == 'box4':
  # every Hamiltonian solid subset of a 4x4 box (up to translation), and up to `count`
  # non-Hamiltonian ones that pass the easy tests (even, connected, minimum degree 2)
  pts = [(x, y) for x in range(4) for y in range(4)]
  seen = set(); hams = []; others = []
  for mask in range(1 << 16):
    V = frozenset(p for i, p in enumerate(pts) if mask >> i & 1)
    if len(V) < 4 or len(V) % 2 or not solid(V): continue
    V = norm(V)
    if V in seen: continue
    seen.add(V)
    if not connected(V) or any(len(nbrs(V, p)) < 2 for p in V): continue
    (hams if ham(V) else others).append(V)
  random.Random(seed).shuffle(others)
  shapes = hams + others[:count]
elif mode == 'blocks':
  rng = random.Random(seed)
  while len(shapes) < count:
    k = rng.randint(1, 9)
    V = {(0, 0), (1, 0), (0, 1), (1, 1)}
    for _ in range(k):
      p = rng.choice(sorted(V))
      dx, dy = rng.choice(((1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (2, 0), (0, 2)))
      for a in (0, 1):
        for b in (0, 1): V.add((p[0] + dx + a, p[1] + dy + b))
    if rng.random() < 0.3:
      V.discard(rng.choice(sorted(V)))
    if solid(V): shapes.append(frozenset(V))
else:
  rng = random.Random(seed)
  while len(shapes) < count:
    target = rng.randint(4, 28)
    V = {(0, 0)}
    while len(V) < target:
      p = rng.choice(sorted(V))
      q = rng.choice(((p[0]+1,p[1]),(p[0]-1,p[1]),(p[0],p[1]+1),(p[0],p[1]-1)))
      V.add(q)
    if solid(V): shapes.append(frozenset(V))
truth = [ham(V) for V in shapes]
with open(outj, 'w') as f: json.dump({'n': len(shapes), 'ham': truth, 'sizes': [len(V) for V in shapes]}, f)
with open(outl, 'w') as f:
  f.write('import ULHC\nopen ULHC\n\ndef shapes : List (Finset Pt) := [\n')
  f.write(',\n'.join('  ([' + ', '.join(f'({x}, {y})' for x, y in sorted(V)) + '] : List Pt).toFinset' for V in shapes))
  f.write('\n]\n\n#eval do\n  for V in shapes do\n    IO.println s!"{ulhc V}"\n' if mode == 'box4' else
          '\n]\n\n#eval do\n  for V in shapes do\n    IO.println s!"({ulhc V}, {(T.ulhcT V).ret})"\n')
print(len(shapes), 'shapes,', sum(truth), 'Hamiltonian')
