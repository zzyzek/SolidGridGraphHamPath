#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
#
# Command line front end for the Hamiltonian s-t path decision procedure `decideHamPath` (Lean,
# lean/SolidGridHam/Path/HPFinal.lean). Input formats and flags: lib/README.md.
#
# Exit codes: 0 answered (yes or no), 1 --check disagreement or invalid witness,
# 2 bad input (format, missing endpoints, non-solid V).
#
import argparse
import json
import sys
import time

import hpst_fast
import hpst_ref


class InputError(Exception):
  pass


# ASCII grid: one line per row, top row first. `.` point, `#` or space not a point, `s` / `t`
# the endpoints. Lines starting with `;` are comments; blank lines before the first and after the
# last grid line are ignored. x = column (0 = leftmost), y = row counted from the bottom.
#
def parse_ascii(text):
  rows = [ln.rstrip('\n').rstrip('\r') for ln in text.split('\n')]
  rows = [ln for ln in rows if not ln.startswith(';')]
  while ( rows and (rows[0].strip() == '') ):
    rows.pop(0)
  while ( rows and (rows[-1].strip() == '') ):
    rows.pop()
  if not rows:
    raise InputError("empty grid")
  V, s, t = set(), None, None
  h = len(rows)
  for r, ln in enumerate(rows):
    y = h - 1 - r
    for x, ch in enumerate(ln):
      if ch in '.st':
        V.add((x, y))
        if ch == 's':
          if s is not None:
            raise InputError("more than one 's'")
          s = (x, y)
        elif ch == 't':
          if t is not None:
            raise InputError("more than one 't'")
          t = (x, y)
      elif ch not in '# \t':
        raise InputError("unexpected character %r at row %d column %d" % (ch, r + 1, x))
  return (V, s, t)


def parse_json(text):
  try:
    d = json.loads(text)
    V = {(int(p[0]), int(p[1])) for p in d["points"]}
    s = ( tuple(int(c) for c in d["s"]) if (d.get("s") is not None) else None )
    t = ( tuple(int(c) for c in d["t"]) if (d.get("t") is not None) else None )
  except (ValueError, KeyError, TypeError, IndexError) as ex:
    raise InputError("bad JSON input: %s" % ex)
  return (V, s, t)


def parse(text):
  if text.lstrip().startswith('{'):
    return parse_json(text)
  return parse_ascii(text)


# ASCII drawing at double resolution: points on even columns / rows, path edges between them.
#
def draw(V, s, t, P):
  xs = [p[0] for p in V]
  ys = [p[1] for p in V]
  x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
  E = set()
  if P:
    for a, b in zip(P, P[1:]):
      E.add((a, b))
      E.add((b, a))
  out = []
  for y in range(y1, y0 - 1, -1):
    line = ''
    for x in range(x0, x1 + 1):
      p = (x, y)
      if p not in V:
        ch = ' '
      elif p == s:
        ch = 's'
      elif p == t:
        ch = 't'
      elif not P:
        ch = '.'
      else:
        r = ((p, (x + 1, y)) in E)
        l = ((p, (x - 1, y)) in E)
        u = ((p, (x, y + 1)) in E)
        d = ((p, (x, y - 1)) in E)
        ch = { (True, True, False, False): '─', (False, False, True, True): '│',
               (True, False, False, True): '┌', (False, True, False, True): '┐',
               (True, False, True, False): '└', (False, True, True, False): '┘' }.get(
                 (r, l, u, d), '?')
      line += ch
      if x < x1:
        line += ( '─' if ((p, (x + 1, y)) in E) else ' ' )
    out.append(line.rstrip())
    if y > y0:
      line = ''
      for x in range(x0, x1 + 1):
        line += ( '│' if (((x, y), (x, y - 1)) in E) else ' ' )
        if x < x1:
          line += ' '
      out.append(line.rstrip())
  return '\n'.join(out)


def main(argv=None):
  ap = argparse.ArgumentParser(
    description="Decide whether a solid grid graph has a Hamiltonian s-t path (Lean decideHamPath).")
  ap.add_argument('file', nargs='?', help="input file (ASCII grid or JSON); default stdin")
  ap.add_argument('--mode', choices=['ref', 'fast'], default='fast')
  ap.add_argument('--draw', action='store_true', help="draw the path")
  ap.add_argument('--json', action='store_true', help="JSON output")
  ap.add_argument('--check', action='store_true',
                  help="also run the brute force and compare (small inputs only)")
  ap.add_argument('--stats', action='store_true', help="time and counts")
  ap.add_argument('--no-heuristic', action='store_true',
                  help="fast mode: skip the heuristic yes-search (the full algorithm decides)")
  a = ap.parse_args(argv)

  try:
    text = ( open(a.file).read() if a.file else sys.stdin.read() )
    V, s, t = parse(text)
    if ( (s is None) or (t is None) ):
      raise InputError("both endpoints s and t are required")
    if ( (s not in V) or (t not in V) ):
      raise InputError("s and t must be points of V")
    if s == t:
      raise InputError("s and t must differ")
    if not hpst_ref.Solid(frozenset(V)):
      raise InputError("V is not solid (it has a hole: a missing point that cannot reach the "
                       "outside by king moves through missing points)")
  except (InputError, OSError) as ex:
    sys.stderr.write("error: %s\n" % ex)
    return 2

  V = frozenset(V)
  t0 = time.perf_counter()
  if a.mode == 'ref':
    P = hpst_ref.decideHamPath(V, s, t)
    stats = {'counts': dict(hpst_ref.STATS), 'branch': hpst_ref.decideHamPath_branch(V, s, t)}
  else:
    P = hpst_fast.decideHamPath(V, s, t, heuristic=(not a.no_heuristic))
    st = hpst_fast.LAST['stats']
    stats = {'counts': dict(st.c), 'times': {k: round(v, 4) for k, v in st.t.items()},
             'branch': hpst_fast.LAST['branch'], 'decided_by': hpst_fast.LAST['how']}
  dt = time.perf_counter() - t0
  stats['time'] = round(dt, 4)
  stats['points'] = len(V)

  rc = 0
  if ( (P is not None) and (not hpst_ref.verify_path(V, s, t, P)) ):
    sys.stderr.write("internal error: invalid witness path\n")
    rc = 1
  chk = None
  if a.check:
    import brute
    B = brute.brute_hp(V, s, t)
    chk = ( 'agree' if ( (B is not None) == (P is not None) ) else 'DISAGREE' )
    if chk == 'DISAGREE':
      rc = 1

  if a.json:
    out = {'answer': ('yes' if P else 'no'),
           'path': ( [list(p) for p in P] if P else None )}
    if a.check:
      out['check'] = chk
    if a.stats:
      out['stats'] = stats
    if a.draw:
      out['drawing'] = draw(V, s, t, P)
    print(json.dumps(out))
  else:
    print('yes' if P else 'no')
    if P:
      print(' '.join("%d,%d" % p for p in P))
    if a.draw:
      print(draw(V, s, t, P))
    if a.check:
      print("check: %s (brute force)" % chk)
    if a.stats:
      for k, v in stats.items():
        print("stats %s: %s" % (k, v))
  return rc


if __name__ == "__main__":
  sys.exit(main())
