# SPDX-License-Identifier: CC0-1.0
# Parse space-separated Python literals printed by the probes.
#
import ast
def split_top(s):
  out = []; depth = 0; cur = ''
  for ch in s.strip():
    if ch in '[(': depth += 1
    if ch in '])': depth -= 1
    if ch == ' ' and depth == 0:
      if cur: out.append(cur); cur = ''
      continue
    cur += ch
  if cur: out.append(cur)
  return [ast.literal_eval(x) if x[0] in '[(' or x[0].isdigit() else x for x in out]
