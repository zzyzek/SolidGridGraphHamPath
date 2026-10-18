# SPDX-License-Identifier: CC0-1.0
# Do sequences of at most two strips always suffice?  For stuck 2-factors (no Type III,
# >= 2 cycles) of Hamiltonian solid graphs: is there an odd strip, or an even strip s such
# that F xor s has a Type III cell or an odd strip?  (Strips start at Type I cells whose two
# lateral sides are inter, as in Theorem A.)
import sys, random
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from hguided import *

def strips_of(G, F, cells):
    comp = comp_of(G, F)
    out = []
    for w in cells:
        dark = [s for s in SIDES if side_edge(w, s) in F]
        if len(dark) != 1: continue
        d = dark[0]; s = OPP[d]
        lats = [x for x in SIDES if x not in (d, s)]
        if not all(inter(G, F, comp, side_edge(w, x)) for x in lats): continue
        run = [w]; cur = w
        while True:
            cur = nb(cur, s)
            if cur not in cells: run = None; break
            run.append(cur)
            if P.is_alternating_cell(F, cur): break
        if run: out.append(run)
    return out

def has_t3(G, F, cells):
    comp = comp_of(G, F)
    return any(type3(G, F, comp, c) for c in cells)

def main(trials, ncells, seed):
    rng = random.Random(seed); st = {}
    def bump(k): st[k] = st.get(k, 0) + 1
    ex = None
    for t in range(trials):
        if t % 200 == 0: print('progress', t, dict(sorted(st.items())), flush=True)
        G = P.random_solid(ncells, rng); cells = P.unit_cells(G)
        Hpath = None
        for (s0, t0) in rng.sample(list(G.edges), min(3, G.number_of_edges())):
            try: Hpath = P.ham_path_oracle(G, s0, t0, limit=100000)
            except TimeoutError: Hpath = None
            if Hpath: break
        if not Hpath: continue
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
        S = strips_of(G, F, cells)
        if any(len(r) % 2 == 1 for r in S): bump('odd_exists'); continue
        ok = False
        for r in S:
            F2 = set(F); P.flip_run(F2, r)
            if has_t3(G, F2, cells) or any(len(r2) % 2 == 1 for r2 in strips_of(G, F2, cells)):
                ok = True; break
        if ok: bump('depth2_ok')
        else:
            bump('depth2_FAIL')
            if ex is None: ex = (sorted(G.nodes), sorted(F), Hpath, S)
    print(dict(sorted(st.items())))
    if ex: print('FAIL_example', ex)

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
