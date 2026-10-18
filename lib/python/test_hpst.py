#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
#
# Tests for hpst_ref.py / hpst_fast.py against the brute force (brute.py).
#
#   python3 test_hpst.py                 all suites with default sizes
#   python3 test_hpst.py hand random     chosen suites
#   python3 test_hpst.py --count 400 --nmax 40 --time 900
#
# Suites:
#   hand     rectangles (all endpoint pairs), L shapes, plus shapes with inner endpoints
#   random   random instances (all shapes and endpoint modes), ref and fast vs brute
#   same     fast mode (Lean class order, no heuristic) returns the same path as ref mode
#   kpot     the shortest-path classPotential equals the faithful classPotential (array relaxation `relaxA`,
#            `kFuel` = |boxSquares| + 1 rounds; random U, F, prescribed values)
#   leaf     every final test (hpSheffC2 / oneHoleFinalTest / twoHoleFinalTest) vs brute on its subproblem,
#            tagged by the king distance of the two out-vertices (2 or >= 3) and by whether the
#            loop ran a phase
#
import argparse
import random
import sys
import time

import brute
import gen
import hpst_fast as FM
import hpst_ref as R

FAILS = []


def report_fail(tag, V, s, t, msg):
  FAILS.append((tag, msg))
  print("FAIL [%s] %s s=%r t=%r" % (tag, msg, s, t))
  print(gen.to_ascii(V, s, t))


def check_one(tag, V, s, t, use_ref, counts, brute_limit=None):
  try:
    B = brute.brute_hp(V, s, t, limit=brute_limit)
  except RuntimeError:
    counts['brute_skipped'] = counts.get('brute_skipped', 0) + 1
    return
  b = (B is not None)
  br = R.decideHamPath_branch(frozenset(V), s, t)
  if use_ref:
    P = R.decideHamPath(V, s, t)
    k = ('ref', br, ('yes' if b else 'no'))
    counts[k] = counts.get(k, 0) + 1
    if ( (P is not None) != b ):
      report_fail(tag, V, s, t, "ref=%s brute=%s" % (P is not None, b))
    elif ( (P is not None) and (not R.verify_path(V, s, t, P)) ):
      report_fail(tag, V, s, t, "ref path invalid")
  Q = FM.decideHamPath(V, s, t)
  how = FM.LAST['how']
  k = ('fast', br, ('yes' if b else 'no'), how)
  counts[k] = counts.get(k, 0) + 1
  if ( (Q is not None) != b ):
    report_fail(tag, V, s, t, "fast=%s brute=%s (%s)" % (Q is not None, b, how))
  elif ( (Q is not None) and (not FM.verify_path(V, s, t, Q)) ):
    report_fail(tag, V, s, t, "fast path invalid")
  # The full algorithm also on yes instances settled by the heuristic.
  #
  if how != 'algorithm':
    Q2 = FM.decideHamPath(V, s, t, heuristic=False)
    if ( (Q2 is not None) != b ):
      report_fail(tag, V, s, t, "fast(no heuristic)=%s brute=%s" % (Q2 is not None, b))
    k = ('fast-noheur', br, ('yes' if b else 'no'), FM.LAST['how'])
    counts[k] = counts.get(k, 0) + 1


def print_counts(counts):
  for k in sorted(counts, key=str):
    print("   %-60s %d" % (k, counts[k]))


def suite_hand(a):
  counts = {}
  shapes = []
  for (w, h) in ((2, 2), (2, 3), (3, 3), (3, 4), (4, 4), (4, 5), (5, 5), (3, 7), (5, 6)):
    shapes.append(("rect%dx%d" % (w, h), {(x, y) for x in range(w) for y in range(h)}))
  L = {(x, y) for x in range(6) for y in range(6) if ( (x < 3) or (y < 3) )}
  shapes.append(("L6", L))
  plus = {(x, y) for x in range(7) for y in range(7) if ( (2 <= x <= 4) or (2 <= y <= 4) )}
  shapes.append(("plus7", plus))
  T0 = time.time()
  for name, V in shapes:
    V = frozenset(V)
    P = sorted(V)
    pairs = [(s, t) for s in P for t in P if s < t]
    use_ref = ( len(V) <= 30 )
    for (s, t) in pairs:
      if not gen.parity_ok(V, s, t):
        continue
      check_one("hand:" + name, V, s, t, use_ref, counts)
      check_one("hand:" + name, V, t, s, False, counts)
  print("hand: %.1fs" % (time.time() - T0))
  print_counts(counts)


def random_instances(a, seed0, count, nmin, nmax):
  shapes = ['hpath', 'hpath', 'blob', 'thin', 'fat', 'rect']
  modes = ['any', 'inner2', 'inner1', 'boundary', 'close', 'adjacent', 'plausible', 'plausible']
  i = 0
  made = 0
  while made < count:
    rng = random.Random(seed0 + i)
    n = rng.randint(nmin, nmax)
    shape = shapes[i % len(shapes)]
    mode = modes[(i // len(shapes)) % len(modes)]
    i += 1
    r = gen.gen(n, shape, mode, seed=seed0 + i)
    if r is None:
      continue
    made += 1
    yield ("%s/%s/n%d/seed%d" % (shape, mode, n, seed0 + i), r)


def suite_random(a):
  counts = {}
  T0 = time.time()
  for tag, (V, s, t) in random_instances(a, 100000, a.count, 10, a.nmax):
    check_one("random:" + tag, V, s, t, ( len(V) <= a.refmax ), counts, brute_limit=2000000)
    if (time.time() - T0) > a.time:
      print("random: time cap reached")
      break
  print("random: %.1fs" % (time.time() - T0))
  print_counts(counts)


def suite_same(a):
  T0 = time.time()
  same = diff = 0
  for tag, (V, s, t) in random_instances(a, 200000, a.count // 2, 10, min(a.nmax, a.refmax)):
    P = R.decideHamPath(V, s, t)
    Q = FM.decideHamPath(V, s, t, heuristic=False, order='lean')
    if ( (P == Q) or ( (P is None) and (Q is None) ) ):
      same += 1
    else:
      diff += 1
      report_fail("same:" + tag, V, s, t, "ref and fast(lean order) paths differ")
    if (time.time() - T0) > a.time:
      break
  print("same: identical %d, different %d, %.1fs" % (same, diff, time.time() - T0))


def suite_kpot(a):
  bad = tot = some = 0
  for i in range(300):
    rng = random.Random(300000 + i)
    r = gen.gen(rng.choice([10, 20, 30, 40]), rng.choice(['blob', 'fat', 'rect', 'hpath']),
                'any', seed=300000 + i, parity=False)
    if r is None:
      continue
    V, s, t = r
    cx = FM.Ctx(V)
    holes = rng.sample(sorted(V), rng.choice([1, 2]))
    U = frozenset(set(V) - set(holes))
    if len(U) < 2:
      continue
    inU = bytearray(cx.N)
    for p in U:
      inU[cx.pid(p)] = 1
    Ul = [cx.pid(p) for p in sorted(U)]
    # A factor-like F: a real path factor when one exists, else random edges.
    #
    E = [e for p in V for e in (R.eR(p), R.eU(p)) if R.IsEdge(V, e)]
    Fr = R.findFactor(frozenset(V), R.dST(s, t))
    F = ( Fr if ( (Fr is not None) and (rng.random() < 0.7) ) else
          frozenset(e for e in E if rng.random() < 0.5) )
    Fb = bytearray(2 * cx.N)
    for (d, x, y) in F:
      Fb[(2 * cx.pid((x, y))) + d] = 1
    kw = R.boxWidth(U)
    for _ in range(3):
      hs = [rng.randint(-kw - 1, kw + 1) for _ in holes]
      L = R.classPotential(U, F, holes, hs)
      f = FM.classPotential_fast(cx, inU, Ul, Fb, [cx.pid(h) for h in holes], hs)
      g1 = R.classSearch(U, F, holes, hs)
      g2 = FM.classSearch_fast(cx, inU, Ul, Fb, [cx.pid(h) for h in holes], hs, FM.Stats())
      g2s = ( None if (g2 is None) else
              frozenset(((e & 1),) + cx.pt(e >> 1) for e in range(len(g2)) if g2[e]) )
      tot += 1
      some += ( g1 is not None )
      if ( (len(R.boxSquares(U)) != len(f)) or any(L(c) != f[cx.pid(c)] for c in R.boxSquares(U)) or
           (g1 != g2s) ):
        bad += 1
        print("FAIL kpot instance %d" % i)
  if bad:
    FAILS.append(('kpot', bad))
  print("kpot: compared %d (classSearch some %d), mismatches %d" % (tot, some, bad))


# Final-test audit: compare every final test with brute force on its subproblem.
#
def leaf_auditor(stats):
  last = {'phases': 0, 'solver': None}

  def hook(solver, s, w, res):
    cx = solver.cx
    # Phases run by this final test (the loop did work beyond the start factor).
    #
    if last['solver'] is not solver:
      last['solver'], last['phases'] = solver, 0
    ph = solver.stats.c.get('phases', 0)
    ran = ( 'loop' if (ph > last['phases']) else 'noloop' )
    last['phases'] = ph
    sx, sy = cx.pt(s)
    wx, wy = cx.pt(w)
    kd = 'kd%d' % max(abs(sx - wx), abs(sy - wy))
    kd = ( kd if (kd == 'kd2') else 'kd>=3' )
    U = [cx.pt(p) for p in solver.Ul()]
    try:
      B = brute.brute_hp(U, cx.pt(s), cx.pt(w), limit=300000)
    except RuntimeError:
      stats['skipped'] = stats.get('skipped', 0) + 1
      return
    k = ('agree' if ( (B is not None) == (res is not None) ) else 'DISAGREE')
    k2 = (k, ('yes' if (B is not None) else 'no'), kd, ran)
    stats[k2] = stats.get(k2, 0) + 1
    if k == 'DISAGREE':
      stats.setdefault('examples', []).append((sorted(U), cx.pt(s), cx.pt(w), res is not None))
  return hook


def suite_leaf(a):
  T0 = time.time()
  st = {}
  overall = {}
  hook = leaf_auditor(st)
  tag0 = "leaf"
  for tag, (V, s, t) in random_instances(a, 400000, a.count, 10, a.nmax):
    try:
      B = brute.brute_hp(V, s, t, limit=2000000)
    except RuntimeError:
      continue
    Q = FM.decideHamPath(V, s, t, heuristic=False, prune=False, memo=False, leaf_hook=hook)
    k = ( 'agree' if ( (Q is not None) == (B is not None) ) else 'DISAGREE' )
    k2 = (k, ('yes' if (B is not None) else 'no'), R.decideHamPath_branch(frozenset(V), s, t))
    overall[k2] = overall.get(k2, 0) + 1
    if ( (Q is not None) and (not FM.verify_path(V, s, t, Q)) ):
      report_fail(tag0 + ":" + tag, V, s, t, "invalid path")
    if k == 'DISAGREE':
      print("%s DISAGREE overall: %s fast=%s brute=%s" % (tag0, tag, Q is not None, B is not None))
      print(gen.to_ascii(V, s, t))
      report_fail("leaf:" + tag, V, s, t, "overall disagreement")
    if (time.time() - T0) > a.time:
      print("%s: time cap reached" % tag0)
      break
  ex = st.pop('examples', [])
  print("%s: %.1fs" % (tag0, time.time() - T0))
  print("  overall answers vs brute:")
  print_counts(overall)
  print("  final tests vs brute on their subproblem:")
  print_counts(st)
  for (U, s, w, res) in ex[:5]:
    print("  %s final-test disagreement: s=%r w=%r result=%s" % (tag0, s, w, res))
    print(gen.to_ascii(frozenset(U), s, w))
  if ex:
    FAILS.append(('leaf', len(ex)))


def main():
  ap = argparse.ArgumentParser()
  ap.add_argument('suites', nargs='*',
                  default=['hand', 'kpot', 'same', 'random', 'leaf'])
  ap.add_argument('--count', type=int, default=300)
  ap.add_argument('--nmax', type=int, default=36)
  ap.add_argument('--refmax', type=int, default=30)
  ap.add_argument('--time', type=float, default=600.0, help="time cap per suite (s)")
  a = ap.parse_args()
  for s in a.suites:
    print("== %s ==" % s)
    sys.stdout.flush()
    if s == 'leaf':
      suite_leaf(a)
    else:
      globals()['suite_' + s](a)
    sys.stdout.flush()
  print("FAILURES: %d" % len(FAILS))
  sys.exit(1 if FAILS else 0)


if __name__ == "__main__":
  main()
