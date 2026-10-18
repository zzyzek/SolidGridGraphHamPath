# SPDX-License-Identifier: CC0-1.0
# H-guided strip sequences (the construction of Theorem A, V2 form) on random solid graphs.
# Checks: chain separation (H crosses the created chain), Lemma 5.7 on chains, the walk's
# local behaviour, and whether the resulting sequences are static (thesis Def 7.1).
import sys, random
from collections import deque
sys.path.insert(0, '/home/z/claude/pathfactor/code')
import pfharness as P

def par(c): return (c[0] + c[1]) % 2 == 1
def horiz(e): return e[0][1] == e[1][1]
def lohi(e):
    (x0, y0), (x1, y1) = e
    if horiz(e): return (x0, y0 - 1), (x0, y0)
    return (x0 - 1, y0), (x0, y0)
def up(F, e):
    inE1 = (e in F) if horiz(e) else (e not in F)
    return par(lohi(e)[0]) == inE1
SIDES = ['b', 't', 'l', 'r']
OPP = {'b': 't', 't': 'b', 'l': 'r', 'r': 'l'}
STEP = {'b': (0, -1), 't': (0, 1), 'l': (-1, 0), 'r': (1, 0)}
def side_edge(c, s):
    bot, top, lef, rig = P.cell_edges(c)
    return {'b': bot, 't': top, 'l': lef, 'r': rig}[s]
def out_arc(F, c, s):
    e = side_edge(c, s); m = e in F
    return (par(c) == m) if s in 'bt' else (not (par(c) == m))
def nb(c, s): return (c[0] + STEP[s][0], c[1] + STEP[s][1])

def D_field(G, F, H, cells):
    xs = [v[0] for v in G.nodes]; ys = [v[1] for v in G.nodes]
    x0, x1, y0, y1 = min(xs) - 2, max(xs) + 1, min(ys) - 2, max(ys) + 1
    S = F ^ H
    D = {(x0, y0): 0}; q = deque([(x0, y0)])
    while q:
        c = q.popleft()
        for s in SIDES:
            n = nb(c, s)
            if not (x0 <= n[0] <= x1 and y0 <= n[1] <= y1) or n in D: continue
            e = side_edge(c, s)
            w = 0
            if e in S: w = 2 if up(F, e) else -2
            lo, hi = lohi(e)
            D[n] = D[c] + (w if c == lo else -w)
            q.append(n)
    return D

def comp_of(G, F):
    comp, _ = P.components(G, F); return comp

def inter(G, F, comp, e):
    return G.has_edge(*e) and e not in F and comp[e[0]] != comp[e[1]]

def chain(G, F, comp, cells, c):
    seen = {c}; q = deque([c])
    while q:
        w = q.popleft()
        for s in SIDES:
            e = side_edge(w, s)
            if inter(G, F, comp, e):
                n = nb(w, s)
                if n in cells and n not in seen:
                    seen.add(n); q.append(n)
    edges = {side_edge(w, s) for w in seen for s in SIDES if inter(G, F, comp, side_edge(w, s))}
    return seen, edges

def type3(G, F, comp, c):
    return P.is_alternating_cell(F, c) and inter(G, F, comp, [e for e in P.cell_edges(c) if e not in F][0])

class Anomaly(Exception): pass

def walk_strip(G, F, H, cells, comp, Echain, e):
    """From H-edge e on the chain: orientation by D, walk along chain edges, Phase II."""
    D = D_field(G, F, H, cells)
    lo, hi = lohi(e)
    a, b = (lo, hi) if up(F, e) else (hi, lo)
    if D[b] != D[a] + 2: raise Anomaly('jump')
    if D[a] >= 0: o, v = True, b
    else: o, v = False, a
    si = [s for s in SIDES if side_edge(v, s) == e][0]
    if v not in cells: raise Anomaly('start not a cell')
    w = v; seen = set()
    while True:
        if (w, si) in seen: raise Anomaly('walk loops')
        seen.add((w, si))
        outs = [s for s in SIDES if s != si and side_edge(w, s) in Echain and out_arc(F, w, s) == o]
        if not outs: break
        if len(outs) > 1: raise Anomaly('branch')
        so = outs[0]; w = nb(w, so); si = OPP[so]
        if w not in cells: raise Anomaly('left the graph')
    dark = [s for s in SIDES if side_edge(w, s) in F]
    if len(dark) != 1: raise Anomaly('stop not Type I')
    d = dark[0]; s = OPP[d]
    run = [w]; cur = w
    while True:
        cur = nb(cur, s)
        if cur not in cells: raise Anomaly('strip left the graph')
        run.append(cur)
        if P.is_alternating_cell(F, cur): return run

def static_ok(seq):
    areas = [set(r) for r in seq]
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            if areas[i] & areas[j]: return False, 'area'
    edges = [set(P.xor_cells(r)) | {e for c in r for e in P.cell_edges(c)} for r in seq]
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            sh = edges[i] & edges[j]
            if sh and (j != i + 1 or len(sh) > 1): return False, 'edge'
    return True, ''

def run(trials, ncells, seed, maxdepth=12):
    rng = random.Random(seed)
    st = {}
    def bump(k): st[k] = st.get(k, 0) + 1
    examples = []
    for _ in range(trials):
        G = P.random_solid(ncells, rng)
        cells = P.unit_cells(G)
        Hpath = None
        for (s0, t0) in rng.sample(list(G.edges), min(4, G.number_of_edges())):
            try:
                Hpath = P.ham_path_oracle(G, s0, t0, limit=200000)
            except TimeoutError:
                Hpath = None
            if Hpath: break
        if not Hpath: continue
        H = {P.ekey(Hpath[i], Hpath[i + 1]) for i in range(len(Hpath) - 1)} | {P.ekey(Hpath[0], Hpath[-1])}
        F = P.degree_factor(G, {v: 2 for v in G.nodes})
        if F is None: continue
        P.random_walk(F, cells, rng.randint(0, 300), rng)
        while True:
            comp = comp_of(G, F)
            t3 = [c for c in cells if type3(G, F, comp, c)]
            if not t3: break
            P.flip(F, P.cell_edges(rng.choice(t3)))
        if len(set(comp.values())) < 2: continue
        bump('stuck')
        # first strip: any H-edge between different cycles
        starts = [e for e in H if comp[e[0]] != comp[e[1]]]
        e = rng.choice(starts)
        Fc = set(F); seq = []
        _, Ech = chain(G, Fc, comp, cells, lohi(e)[1] if lohi(e)[1] in cells else lohi(e)[0])
        try:
            for depth in range(maxdepth):
                comp = comp_of(G, Fc)
                run_ = walk_strip(G, Fc, H, cells, comp, Ech, e)
                seq.append(run_)
                if P.strip_trace(G, Fc, run_) is None and len(run_) > 1: bump('invalid_strip')
                P.flip_run(Fc, run_)
                if len(run_) % 2 == 1: break
                comp2 = comp_of(G, Fc)
                end = run_[-1]
                ch_cells, Ech = chain(G, Fc, comp2, cells, end)
                t3all = [c for c in cells if type3(G, Fc, comp2, c)]
                if t3all:
                    on = [c for c in t3all if c in ch_cells]
                    if on: seq.append([on[0]]); P.flip(Fc, P.cell_edges(on[0])); break
                    bump('L57_fail'); break
                Hon = [x for x in H if x in Ech]
                if not Hon: bump('separation_fail'); break
                e = rng.choice(Hon)
            else:
                bump('too_deep')
        except Anomaly as ex:
            bump('anomaly_' + str(ex)); continue
        bump('len_%d' % len(seq))
        ok, why = static_ok(seq)
        if ok: bump('static')
        else:
            bump('nonstatic_' + why)
            if len(examples) < 2: examples.append((sorted(G.nodes), sorted(F), sorted(H), seq))
        if P.ncomp(G, Fc) != P.ncomp(G, F) - 1: bump('count_wrong')
    return st, examples

if __name__ == '__main__':
    trials, ncells, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    st, ex = run(trials, ncells, seed)
    print(dict(sorted(st.items())))
    for x in ex: print('nonstatic_example', x)
