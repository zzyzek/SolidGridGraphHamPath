#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
# Compare Lean `#eval` output (a list of Bools, or of (ulhc, ulhcT.ret) pairs) with brute force.
import sys, json, re
out = open(sys.argv[1]).read(); truth = json.load(open(sys.argv[2]))
vals = re.findall(r'\b(true|false)\b', out)
pairs = '(' in out.split('[', 1)[-1]
vals = [v == 'true' for v in vals]
if pairs: res = list(zip(vals[0::2], vals[1::2]))
else: res = [(v, v) for v in vals]
n = truth['n']; ham = truth['ham']
assert len(res) == n, (len(res), n)
bad = [(i, truth['sizes'][i], ham[i], r) for i, r in enumerate(res) if r[0] != ham[i] or r[1] != r[0]]
print(f"{sys.argv[1]}: {n} shapes, {sum(ham)} Hamiltonian, {len(bad)} mismatches", bad[:10])
sys.exit(1 if bad else 0)
