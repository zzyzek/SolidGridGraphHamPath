# SPDX-License-Identifier: CC0-1.0
# Cross-check of the Lean definition of Solid (king-move escape of missing points)
# against "every bounded face has area 1", over all vertex sets of a W x H grid.
import itertools, sys
from collections import deque

def faces_ok(V, W, H):
    # Plane at doubled resolution, padded by one unit on each side.
    # Open positions: square centres (odd,odd), edge midpoints without an edge,
    # lattice points not in V.
    X0, Y0, X1, Y1 = -2, -2, 2 * W, 2 * H
    def is_open(a, b):
        if a % 2 == 0 and b % 2 == 0:
            return (a // 2, b // 2) not in V
        if a % 2 == 1 and b % 2 == 1:
            return True
        if a % 2 == 1:
            p, q = ((a - 1) // 2, b // 2), ((a + 1) // 2, b // 2)
        else:
            p, q = (a // 2, (b - 1) // 2), (a // 2, (b + 1) // 2)
        return not (p in V and q in V)
    seen = set()
    for a in range(X0, X1 + 1):
        for b in range(Y0, Y1 + 1):
            if (a, b) in seen or not is_open(a, b):
                continue
            comp, bounded, area = [], True, 0
            dq = deque([(a, b)]); seen.add((a, b))
            while dq:
                u, v = dq.popleft()
                if u in (X0, X1) or v in (Y0, Y1):
                    bounded = False
                if u % 2 == 1 and v % 2 == 1:
                    area += 1
                for du, dv in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                    w = (u + du, v + dv)
                    if X0 <= w[0] <= X1 and Y0 <= w[1] <= Y1 and w not in seen and is_open(*w):
                        seen.add(w); dq.append(w)
            if bounded and area > 1:
                return False
    return True

def lean_solid(V, W, H):
    if not V:
        return True
    minx = min(p[0] for p in V)
    # BFS over missing points by king moves, within a padded box.
    box = [(x, y) for x in range(-2, W + 2) for y in range(-2, H + 2)]
    missing = set(p for p in box if p not in V)
    good = set(p for p in missing if p[0] < minx)
    dq = deque(good)
    while dq:
        x, y = dq.popleft()
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                q = (x + dx, y + dy)
                if q in missing and q not in good:
                    good.add(q); dq.append(q)
    return all(p in good for p in missing)

W, H = int(sys.argv[1]), int(sys.argv[2])
pts = [(x, y) for x in range(W) for y in range(H)]
bad = 0
for mask in range(1 << len(pts)):
    V = set(p for i, p in enumerate(pts) if mask >> i & 1)
    if faces_ok(V, W, H) != lean_solid(V, W, H):
        bad += 1
        if bad <= 3:
            print("mismatch", sorted(V))
print(W, H, "subsets", 1 << len(pts), "mismatches", bad)
