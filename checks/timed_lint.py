#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
# Lint for the counted algorithm (lean/SolidGridHam/Cycle/Timed/*.lean, except TimeM.lean).
# Inside every `def` body, only counted operations (TimeM.lean) and constant-time functions on
# points, edges, sides, strips, nodes, numbers and Booleans may appear. Rejected:
#  * membership, sums, set and list operations that are not counted wrappers;
#  * `decide` (it would decide a membership or a quantifier without counting);
#  * any call to an uncounted algorithm function.
# Exit status 1 and a report on any violation.
import re, sys, glob, os
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'lean', 'SolidGridHam', 'Cycle', 'Timed')
TOKENS = [r'∈', r'∉', r'∑', r'∪', r'∩', r'\\', r'⊆', r'\bdecide\b', r'\bsymmDiff\b', r'\binsert\b',
  r'\.(filter|image|biUnion|card|map|all|any|find\?|sort|toFinset|toList|length|sum|erase|'
  r'foldl|foldr|flatMap|bind|min|max|range|attach|powerset|product|zip|join|reverse|append)\b',
  r'\b(List|Finset|Multiset|Array)\.', r'\+\+']
UNCOUNTED = '''creach ccls connB cncomp fnbr stripScan stripLen allStrips LatOK validB sideOffB midB
  endOffB notEndB cr2B noChainB chainOKB cand candN gsrc gedge findPath decode posList minPath
  minPathL pickSrc amin look layer next B step run ulhc twoFactor augLoop augStep layerAcc walk pred
  nbr pick flip flipCol applyS cellList t3B findT3 deg ind IsCell IsEdge Fwd Bwd Conn cls ncomp
  ValidStrip CR2 StripPat'''.split()
TOP = re.compile(r'^(def|lemma|theorem|@\[|section|end|namespace|open|variable|include|instance|'
                 r'/-|--|private|noncomputable|abbrev|structure|omit|set_option|#)')
def strip_comments(t):
  t = re.sub(r'/-.*?-/', '', t, flags=re.S)
  return re.sub(r'--.*', '', t)
bad = 0
for fn in sorted(glob.glob(os.path.join(ROOT, '*.lean'))):
  if os.path.basename(fn) == 'TimeM.lean': continue
  lines = strip_comments(open(fn).read()).split('\n')
  i = 0
  while i < len(lines):
    if re.match(r'^(private )?def ', lines[i]):
      j = i + 1
      while j < len(lines) and not (lines[j] and TOP.match(lines[j])): j += 1
      body = '\n'.join(lines[i:j])
      # the definition's own name and signature are allowed to mention anything up to `:=`
      cuts = [x for x in (body.find(':='), body.find('\n  |')) if x >= 0]
      code = body[min(cuts):] if cuts else body
      head = re.match(r'^(?:private )?def\s+(\S+)', lines[i]).group(1)
      for k, ln in enumerate(code.split('\n')):
        for tok in TOKENS:
          if re.search(tok, ln):
            print(f'{os.path.basename(fn)}: {head}: uncounted operation /{tok}/ in: {ln.strip()}'); bad += 1
        for nm in UNCOUNTED:
          if re.search(r'(?<![\w\'])' + re.escape(nm) + r'(?![\w\'])', ln):
            print(f'{os.path.basename(fn)}: {head}: uncounted function {nm} in: {ln.strip()}'); bad += 1
      i = j
    else:
      i += 1
print('timed_lint:', 'OK' if bad == 0 else f'{bad} violation(s)')
sys.exit(1 if bad else 0)
