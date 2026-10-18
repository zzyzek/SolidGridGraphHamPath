# SPDX-License-Identifier: CC0-1.0
# Does flipping an even strip (from a 2-factor with no Type III cell, strip starting on a
# Type I border cell) always create a Type III cell?  Broader sampler: random solid shapes
# grown cell by cell, 2-factors from min-cost flow with random costs, then Type III merges.
import random, sys
import networkx as nx
exec(open("checks/l57_check.py").read().split("def run(")[0])

def grow_shape(W, H, rng):
    cells = {(rng.randrange(W - 1), rng.randrange(H - 1))}
    target = rng.randint((W - 1) * (H - 1) // 3, (W - 1) * (H - 1))
    tries = 0
    while len(cells) < target and tries < 20 * target:
        tries += 1
        x, y = rng.choice(sorted(cells))
        dx, dy = rng.choice([(1, 0), (-1, 0), (0, 1), (0, -1)])
        n = (x + dx, y + dy)
        if 0 <= n[0] < W - 1 and 0 <= n[1] < H - 1 and n not in cells:
            V2 = {(a + i, b + j) for a, b in cells | {n} for i in (0, 1) for j in (0, 1)}
            if solid(V2, W, H):
                cells.add(n)
    return {(a + i, b + j) for a, b in cells for i in (0, 1) for j in (0, 1)}

def two_factor(V, rng):
    G = nx.DiGraph()
    for v in V:
        if (v[0] + v[1]) % 2 == 0:
            G.add_edge('s', v, capacity=2, weight=0)
            for w in [(v[0]+1, v[1]), (v[0]-1, v[1]), (v[0], v[1]+1), (v[0], v[1]-1)]:
                if w in V:
                    G.add_edge(v, w, capacity=1, weight=rng.randint(0, 100))
        else:
            G.add_edge(v, 't', capacity=2, weight=0)
    try:
        flow = nx.max_flow_min_cost(G, 's', 't')
    except Exception:
        return None
    F = set()
    for v in V:
        if (v[0] + v[1]) % 2 == 0:
            for w, f in flow[v].items():
                if f:
                    F.add(frozenset({v, w}))
    deg = {v: 0 for v in V}
    for e in F:
        for v in e:
            deg[v] += 1
    return F if all(d == 2 for d in deg.values()) else None

def run(trials, rng, sizes):
    st = dict(stuck=0, even=0, t3_after=0, no_t3=0)
    ex = None
    for _ in range(trials):
        W = rng.choice(sizes); H = rng.choice(sizes)
        V = grow_shape(W, H, rng)
        F = two_factor(V, rng)
        if F is None:
            continue
        while True:
            cl = classes(V, F)
            t3 = [(x, y) for x in range(W) for y in range(H) if type3(V, F, cl, (x, y))]
            if not t3:
                break
            F ^= set(edges_of_cell(*rng.choice(t3)).values())
        if len(set(cl.values())) < 2:
            continue
        st['stuck'] += 1
        for cells, s in strips(V, F, cl):
            if len(cells) % 2:
                continue
            st['even'] += 1
            F2 = set(F)
            for c in cells:
                F2 ^= set(edges_of_cell(*c).values())
            cl2 = classes(V, F2)
            if any(type3(V, F2, cl2, (x, y)) for x in range(W) for y in range(H)):
                st['t3_after'] += 1
            else:
                st['no_t3'] += 1
                if ex is None:
                    ex = (sorted(V), sorted(map(sorted, F)), cells)
    return st, ex

seed, trials = int(sys.argv[1]), int(sys.argv[2])
sizes = [int(a) for a in sys.argv[3].split(',')]
st, ex = run(trials, random.Random(seed), sizes)
print(st)
if ex:
    print('no_t3_example', ex)
