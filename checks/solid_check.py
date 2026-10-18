#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
# Cross-check of the Lean definition of `Solid` (every missing lattice point is joined to a
# point left of V by king moves through missing points) against the thesis's Def 2.2 ("all
# interior faces have unit area") for the node-induced grid graph on V.
# Faces: draw V on the doubled grid (points at even coordinates, edges at their midpoints)
# and take 4-connected components of undrawn positions in a box with margin. A bounded face
# is a component not touching the box border; its area is the number of cell centres
# (odd, odd) in it. Usage: solid_check.py  (all subsets of a 4x4 box, then random 6x6 sets)
import random, itertools, sys
sys.setrecursionlimit(10000)
def lean_solid(V):
  if not V: return True
  xs=[p[0] for p in V]; ys=[p[1] for p in V]
  x0,x1,y0,y1=min(xs)-1,max(xs)+1,min(ys)-1,max(ys)+1
  seen=set(); st=[(x0,y) for y in range(y0,y1+1)]
  while st:
    p=st.pop()
    if p in seen or p in V or not (x0<=p[0]<=x1 and y0<=p[1]<=y1): continue
    seen.add(p)
    st.extend((p[0]+a,p[1]+b) for a in (-1,0,1) for b in (-1,0,1))
  # points outside the box escape trivially; inside the box, escape = reach the left column
  return all(p in V or p in seen for p in itertools.product(range(x0,x1+1),range(y0,y1+1)))
def thesis_solid(V):
  if not V: return True
  xs=[p[0] for p in V]; ys=[p[1] for p in V]
  X0,X1,Y0,Y1=2*min(xs)-2,2*max(xs)+2,2*min(ys)-2,2*max(ys)+2
  drawn=set()
  for (x,y) in V:
    drawn.add((2*x,2*y))
    if (x+1,y) in V: drawn.add((2*x+1,2*y))
    if (x,y+1) in V: drawn.add((2*x,2*y+1))
  seen=set()
  for s in itertools.product(range(X0,X1+1),range(Y0,Y1+1)):
    if s in drawn or s in seen: continue
    comp=[]; st=[s]; border=False
    while st:
      p=st.pop()
      if p in seen or p in drawn: continue
      if not (X0<=p[0]<=X1 and Y0<=p[1]<=Y1): continue
      seen.add(p); comp.append(p)
      if p[0] in (X0,X1) or p[1] in (Y0,Y1): border=True
      st.extend(((p[0]+1,p[1]),(p[0]-1,p[1]),(p[0],p[1]+1),(p[0],p[1]-1)))
    if not border:
      area=sum(1 for p in comp if p[0]%2 and p[1]%2)
      if area!=1: return False
  return True
bad=0; n=0
pts=[(x,y) for x in range(4) for y in range(4)]
for mask in range(1<<16):
  V=frozenset(p for i,p in enumerate(pts) if mask>>i&1)
  n+=1
  if lean_solid(V)!=thesis_solid(V): bad+=1; print('MISMATCH',sorted(V)) if bad<5 else None
rng=random.Random(3)
for _ in range(20000):
  V=frozenset(p for p in itertools.product(range(6),range(6)) if rng.random()<rng.choice((0.5,0.7,0.85)))
  n+=1
  if lean_solid(V)!=thesis_solid(V): bad+=1; print('MISMATCH',sorted(V)) if bad<5 else None
print(n,'sets,',bad,'mismatches')
