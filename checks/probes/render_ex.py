# SPDX-License-Identifier: CC0-1.0
# Render EX lines from tl_enum: F and the factors along the path, with strip cells marked.
#
import sys, json
ARGS = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/tl_algo.py').read())
def draw(V, F, marks):
  cl = classes(V, F); names = {}
  for v in sorted(V): names.setdefault(cl[v], "ABCDEFGHIJKLMNOP"[len(names) % 16])
  xs = [x for x, y in V]; ys = [y for x, y in V]
  out = []
  for y in range(max(ys), min(ys) - 1, -1):
    row = ""; mid = ""
    for x in range(min(xs), max(xs) + 1):
      row += names[cl[(x, y)]] if (x, y) in V else " "
      row += "-" if ph.ekey((x, y), (x+1, y)) in F else " "
      if y > min(ys):
        mid += "|" if ph.ekey((x, y-1), (x, y)) in F else " "
        mid += marks.get((x, y - 1), " ")
    out.append(row)
    if y > min(ys): out.append(mid)
  return "\n".join(out)
k = int(ARGS[1])
lines = [l for l in open(ARGS[0]) if l.startswith('EX')]
Vl, Fl, runs, i, why, best = json.loads(lines[k][3:])
V = set(map(tuple, Vl)); F = {tuple(map(tuple, e)) for e in Fl}
runs = [list(map(tuple, r)) for r in runs]
print('path', runs, 'fails at', i, why, '\nbest', best)
marks = {}
for n, r in enumerate(runs):
  for c in r: marks[c] = str(n + 1)
Fi = F
for n in range(len(runs) + 1):
  print('--- after', n, 'strips; ncomp', ncomp(V, Fi), 'factor', is_factor(V, Fi))
  print(draw(V, Fi, marks))
  if n < len(runs): Fi = apply(Fi, [list(runs[n])])
