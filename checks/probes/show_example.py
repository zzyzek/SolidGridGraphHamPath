# SPDX-License-Identifier: CC0-1.0
import ast, sys
exec(open("checks/l57_check.py").read().split("def run(")[0])
line = [l for l in open(sys.argv[1]) if l.startswith('no_t3_example')][0]
V, Fl, cells = ast.literal_eval(line[len('no_t3_example '):])
V = set(map(tuple, V)); F = set(frozenset(map(tuple, e)) for e in Fl)
cells = [tuple(c) for c in cells]
W = max(x for x, y in V) + 1; H = max(y for x, y in V) + 1
def draw(F, mark):
    cl = classes(V, F); names = {}
    for v in sorted(V):
        names.setdefault(cl[v], "ABCDEFGHIJ"[len(names)])
    out = []
    for y in range(H - 1, -1, -1):
        row = ""; mid = ""
        for x in range(W):
            row += names[cl[(x, y)]] if (x, y) in V else " "
            row += "-" if frozenset({(x, y), (x+1, y)}) in F else " "
            if y > 0:
                mid += "|" if frozenset({(x, y), (x, y-1)}) in F else " "
                mid += "#" if (x, y - 1) in mark else " "
        out.append(row)
        if y > 0: out.append(mid)
    return "\n".join(out), len(names)
def t3(F):
    cl = classes(V, F)
    return [(x, y) for x in range(W) for y in range(H) if type3(V, F, cl, (x, y))]
pic, k = draw(F, set(cells)); print("F:", k, "cycles; Type III:", t3(F)); print(pic)
F2 = set(F)
for c in cells: F2 ^= set(edges_of_cell(*c).values())
pic, k = draw(F2, set(cells)); print("\nF xor strip:", k, "cycles; Type III:", t3(F2)); print(pic)
print("\nstrip cells (first = start):", cells, "solid:", solid(V, W, H))
