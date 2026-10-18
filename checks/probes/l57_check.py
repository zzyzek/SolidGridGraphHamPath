# SPDX-License-Identifier: CC0-1.0
# Probe of thesis Lemmas 5.6 and 5.7 on random 2-factors of rectangles.
# For every even alternating strip that starts on a border cell (Type I, its two
# lateral sides joining different cycles) in a 2-factor F with no Type III cells:
#   L5.6: after flipping, the end cell is a border cell.
#   L5.7: if F' = F xor strip has a Type III cell, one lies on the boundary of the
#         end cell (cells linked through sides that join different cycles).
import random, sys
from collections import deque

def edges_of_cell(x, y):
    # bottom, top, left, right as frozensets of endpoints
    return {'b': frozenset({(x, y), (x+1, y)}), 't': frozenset({(x, y+1), (x+1, y+1)}),
            'l': frozenset({(x, y), (x, y+1)}), 'r': frozenset({(x+1, y), (x+1, y+1)})}

OPP = {'b': 't', 't': 'b', 'l': 'r', 'r': 'l'}
LATS = {'b': ('l', 'r'), 't': ('l', 'r'), 'l': ('b', 't'), 'r': ('b', 't')}
STEP = {'t': (0, 1), 'b': (0, -1), 'r': (1, 0), 'l': (-1, 0)}

def classes(V, F):
    par = {v: v for v in V}
    def f(a):
        while par[a] != a:
            par[a] = par[par[a]]; a = par[a]
        return a
    for e in F:
        a, b = tuple(e); par[f(a)] = f(b)
    return {v: f(v) for v in V}

def is_cell(V, c):
    x, y = c
    return all(p in V for p in [(x, y), (x+1, y), (x, y+1), (x+1, y+1)])

def alt(F, c):
    E = edges_of_cell(*c)
    m = {k: (E[k] in F) for k in E}
    return (m['b'] and m['t'] and not m['l'] and not m['r']) or \
           (m['l'] and m['r'] and not m['b'] and not m['t'])

def type3(V, F, cl, c):
    if not is_cell(V, c) or not alt(F, c):
        return False
    E = edges_of_cell(*c)
    dark = [E[k] for k in E if E[k] in F]
    a = next(iter(dark[0])); b = next(iter(dark[1]))
    return cl[a] != cl[b]

def inter(V, F, cl, e):
    a, b = tuple(e)
    return a in V and b in V and e not in F and cl[a] != cl[b]

def boundary(V, F, cl, c):
    seen = {c}; dq = deque([c])
    while dq:
        x, y = dq.popleft()
        E = edges_of_cell(x, y)
        for k, e in E.items():
            if inter(V, F, cl, e):
                dx, dy = STEP[k]
                n = (x + dx, y + dy)
                if is_cell(V, n) and n not in seen:
                    seen.add(n); dq.append(n)
    return seen

def solid(V, W, H):
    # king-move escape of missing points (the Lean definition)
    box = [(x, y) for x in range(-1, W + 1) for y in range(-1, H + 1)]
    miss = set(p for p in box if p not in V)
    good = set(p for p in miss if p[0] == -1); dq = deque(good)
    while dq:
        x, y = dq.popleft()
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                q = (x + dx, y + dy)
                if q in miss and q not in good:
                    good.add(q); dq.append(q)
    return good == miss

def random_2factor(W, H, steps, rng):
    # Union of random 2x2 blocks on the even lattice, grown connected, kept solid.
    nb = (W // 2) * (H // 2)
    blocks = {(rng.randrange(W // 2), rng.randrange(H // 2))}
    target = rng.randint(max(2, nb // 3), nb)
    while len(blocks) < target:
        bx, by = rng.choice(sorted(blocks))
        dx, dy = rng.choice([(1, 0), (-1, 0), (0, 1), (0, -1)])
        n = (bx + dx, by + dy)
        if 0 <= n[0] < W // 2 and 0 <= n[1] < H // 2 and n not in blocks:
            V2 = {(2*a + i, 2*b + j) for a, b in blocks | {n} for i in (0, 1) for j in (0, 1)}
            if solid(V2, W, H):
                blocks.add(n)
    V = {(2*a + i, 2*b + j) for a, b in blocks for i in (0, 1) for j in (0, 1)}
    F = set()
    for a, b in blocks:
        F |= set(edges_of_cell(2*a, 2*b).values())
    cells = [(x, y) for x in range(W - 1) for y in range(H - 1) if is_cell(V, (x, y))]
    for _ in range(steps):
        c = rng.choice(cells)
        if alt(F, c):
            F ^= set(edges_of_cell(*c).values())
    return V, F

def strips(V, F, cl):
    out = []
    for x in range(-1, 20):
        for y in range(-1, 20):
            c = (x, y)
            if not is_cell(V, c):
                continue
            E = edges_of_cell(x, y)
            dark = [k for k in E if E[k] in F]
            if len(dark) != 1:
                continue
            d = dark[0]; s = OPP[d]
            la, lb = LATS[s]
            if not (inter(V, F, cl, E[la]) and inter(V, F, cl, E[lb])):
                continue
            cells = [c]; cur = c
            while True:
                dx, dy = STEP[s]; cur = (cur[0] + dx, cur[1] + dy)
                if not is_cell(V, cur):
                    cells = None; break
                cells.append(cur)
                if alt(F, cur):
                    break
            if cells:
                out.append((cells, s))
    return out

def run(trials, rng):
    stats = dict(strips=0, even=0, l56_fail=0, t3_after=0, l57_fail=0)
    example = None
    for _ in range(trials):
        W = rng.choice(SIZES); H = rng.choice(SIZES)
        V, F = random_2factor(W, H, rng.randint(10, 400), rng)
        # Merge through Type III cells (in random order) until none is left.
        while True:
            cl = classes(V, F)
            t3 = [(x, y) for x in range(W) for y in range(H) if type3(V, F, cl, (x, y))]
            if not t3:
                break
            F ^= set(edges_of_cell(*rng.choice(t3)).values())
        stats['stuck'] = stats.get('stuck', 0) + (len(set(cl.values())) > 1)
        for cells, s in strips(V, F, cl):
            stats['strips'] += 1
            if len(cells) % 2 == 1:
                continue
            stats['even'] += 1
            F2 = set(F)
            for c in cells:
                F2 ^= set(edges_of_cell(*c).values())
            cl2 = classes(V, F2)
            end = cells[-1]
            E = edges_of_cell(*end)
            if not any(inter(V, F2, cl2, e) for e in E.values()):
                stats['l56_fail'] += 1
            t3 = [(x, y) for x in range(W) for y in range(H) if type3(V, F2, cl2, (x, y))]
            # L5.7': every Type III cell's dark sides lie on the two cycles met by the end
            # cell's inter sides.
            ends = set()
            for e in E.values():
                if inter(V, F2, cl2, e):
                    a, b = tuple(e); ends = {cl2[a], cl2[b]}
            for d in t3:
                Ed = edges_of_cell(*d)
                dk = [Ed[k] for k in Ed if Ed[k] in F2]
                cls_d = {cl2[next(iter(dk[0]))], cl2[next(iter(dk[1]))]}
                if cls_d != ends:
                    stats['l57p_fail'] = stats.get('l57p_fail', 0) + 1
            # Case at the end cell: does a front corner turn sideways (alpha/beta) or do both
            # continue forward (gamma)?
            ex_, ey_ = end; dx_, dy_ = STEP[s]
            if dx_ == 0:
                fc = [(ex_, ey_ + (1 if dy_ > 0 else 0)), (ex_ + 1, ey_ + (1 if dy_ > 0 else 0))]
                fwd = [frozenset({p, (p[0], p[1] + dy_)}) for p in fc]
            else:
                fc = [(ex_ + (1 if dx_ > 0 else 0), ey_), (ex_ + (1 if dx_ > 0 else 0), ey_ + 1)]
                fwd = [frozenset({p, (p[0] + dx_, p[1])}) for p in fc]
            gamma = all(e in F for e in fwd)
            key2 = ('gamma_' if gamma else 'side_') + ('t3' if t3 else 'no_t3')
            stats[key2] = stats.get(key2, 0) + 1
            if t3:
                # Where is the nearest Type III cell? (adjacent to the end cell, or not)
                ex, ey = end
                adj = [(ex+1, ey), (ex-1, ey), (ex, ey+1), (ex, ey-1)]
                key = 'adjacent' if any(d in adj for d in t3) else 'not_adjacent'
                stats[key] = stats.get(key, 0) + 1
                if key == 'not_adjacent' and 'far_example' not in stats:
                    stats['far_example'] = (W, H, sorted(map(sorted, F)), cells, t3)
                stats['t3_after'] += 1
                B = boundary(V, F2, cl2, end)
                if not any(c in B for c in t3):
                    stats['l57_fail'] += 1
                    if example is None:
                        example = (W, H, sorted(map(sorted, F)), cells, t3)
    return stats, example

SIZES = [int(a) for a in (sys.argv[3] if len(sys.argv) > 3 else "6,8,10,12").split(",")]
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
trials = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
st, ex = run(trials, random.Random(seed))
fe = st.pop('far_example', None)
print(st)
if fe:
    print('far_example', fe)
if ex:
    print("example", ex)
