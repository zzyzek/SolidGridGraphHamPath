#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
#
# Timings of the C port vs the Python fast mode on yes instances and hard no instances.
#
#   python3 perf.py [--sizes 100,400,1600] [--search 400] [--keep 3] [--yes 5]
#
# Hard "no" instances: for each size, --search random instances in endpoint mode `plausible`
# (endpoints pass every necessary condition, so the algorithm itself must decide) over all
# shapes are solved by the C binary (no heuristic) on 4 workers; the --keep slowest "no"
# answers are then timed sequentially in both implementations. "Yes" instances: planted paths
# (shape hpath) with all endpoint modes. Times are the algorithm only (no heuristic; C: the
# solver's `total` timer, without process start; Python: hpst_fast.decideHamPath), best of 3 for C.
#
import argparse
import json
import multiprocessing
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'python'))

import gen
import hpst_fast as FM

BIN = os.path.join(HERE, 'hpst')
SHAPES = ['blob', 'thin', 'fat', 'rect', 'hpath']


def run_c(V, s, t, heuristic=False):
  inp = json.dumps({'points': sorted(list(p) for p in V), 's': list(s), 't': list(t)})
  args = [BIN, '--json', '--stats'] + ( [] if heuristic else ['--no-heuristic'] )
  r = subprocess.run(args, input=inp.encode(), capture_output=True)
  d = json.loads(r.stdout.decode())
  return d


def search_one(job):
  n, shape, mode, seed = job
  inst = gen.gen(n, shape, mode, seed)
  if inst is None:
    return None
  V, s, t = inst
  d = run_c(V, s, t)
  st = d['stats']
  c = st['counts']
  w = c.get('classSearch', 0) + c.get('phases', 0) + c.get('final_tests', 0)
  return (w, d['answer'], st['decided_by'], job, len(V),
          st['counts'].get('walk_nodes', 0), st['counts'].get('final_tests', 0))


# Search 2: one shape, many endpoint pairs (colour-feasible; half both inner), solved by C.
#
def search_pairs(job):
  import random
  n, shape, seed, k = job
  rng = random.Random(seed)
  V = gen.make_shape(n, shape, rng)
  P = sorted(V)
  inner = [p for p in P if gen.is_inner(V, p)]
  out = []
  for i in range(k):
    pool = ( inner if ( ((i % 2) == 0) and (len(inner) >= 2) ) else P )
    s, t = rng.sample(pool, 2)
    if not gen.parity_ok(V, s, t):
      continue
    d = run_c(V, s, t)
    st = d['stats']
    if ( (d['answer'] == 'no') and (st['decided_by'] == 'algorithm') ):
      c = st['counts']
      w = c.get('classSearch', 0) + c.get('phases', 0) + c.get('final_tests', 0)
      out.append((w, (n, shape, seed), s, t, len(V)))
  return out


def time_pair(V, s, t, heuristic=False):
  best = None
  for _ in range(3):
    d = run_c(V, s, t, heuristic)
    x = d['stats']['times']['total']
    best = ( x if ( (best is None) or (x < best) ) else best )
  t0 = time.perf_counter()
  P = FM.decideHamPath(V, s, t, heuristic=heuristic)
  tp = time.perf_counter() - t0
  return (best, tp, d['answer'], ( 'yes' if P else 'no' ), dict(d['stats']['counts']),
          FM.LAST['branch'])


def main():
  ap = argparse.ArgumentParser()
  ap.add_argument('--sizes', default='100,400,1600')
  ap.add_argument('--search', type=int, default=400)
  ap.add_argument('--keep', type=int, default=3)
  ap.add_argument('--yes', type=int, default=5)
  ap.add_argument('--seed', type=int, default=7)
  ap.add_argument('--shapes2', type=int, default=0, help="search 2: number of shapes")
  ap.add_argument('--pairs', type=int, default=200, help="search 2: endpoint pairs per shape")
  a = ap.parse_args()
  for n in [int(x) for x in a.sizes.split(',')]:
    jobs = [(n, SHAPES[i % len(SHAPES)], 'plausible', a.seed + (31337 * i) + n)
            for i in range(a.search)]
    T0 = time.perf_counter()
    with multiprocessing.Pool(4) as pool:
      res = [r for r in pool.map(search_one, jobs, chunksize=4) if r is not None]
    if a.shapes2 > 0:
      import random
      jobs2 = [(n, ['blob', 'fat', 'rect', 'thin'][i % 4], a.seed + (7 * i) + n, a.pairs)
               for i in range(a.shapes2)]
      with multiprocessing.Pool(4) as pool:
        r2 = [x for L in pool.map(search_pairs, jobs2, chunksize=1) for x in L]
      r2.sort(key=lambda r: -r[0])
      print("n=%d: search 2: %d shapes x %d pairs: %d no (algorithm)" %
            (n, a.shapes2, a.pairs, len(r2)))
      for r in r2[:a.keep]:
        _, (nn, shape, seed), s, t, nv = r
        import random
        V = gen.make_shape(nn, shape, random.Random(seed))
        tc, tp, ac, ap_, cnt, br = time_pair(V, s, t)
        print("  hard no  |V|=%4d %-9s %-6s C %8.4f s  Python %8.3f s  ratio %6.0f  answers %s/%s"
              "  walk nodes %d, final tests %d, classSearch %d" %
              (nv, br, shape, tc, tp, tp / max(tc, 1e-6), ac, ap_, cnt.get('walk_nodes', 0),
               cnt.get('final_tests', 0), cnt.get('classSearch', 0)))
    nos = sorted((r for r in res if ( (r[1] == 'no') and (r[2] == 'algorithm') )),
                 key=lambda r: -r[0])
    print("n=%d: searched %d plausible instances in %.1f s: %d no (algorithm), %d yes" %
          (n, len(res), time.perf_counter() - T0, len(nos), sum(1 for r in res if r[1] == 'yes')))
    for r in nos[:a.keep]:
      _, _, _, job, nv, wn, ft = r
      V, s, t = gen.gen(*job)
      tc, tp, ac, ap_, cnt, br = time_pair(V, s, t)
      print("  hard no  |V|=%4d %-9s %-6s C %8.4f s  Python %8.3f s  ratio %6.0f  answers %s/%s"
            "  walk nodes %d, final tests %d, classSearch %d" %
            (nv, br, job[1], tc, tp, tp / max(tc, 1e-6), ac, ap_, cnt.get('walk_nodes', 0),
             cnt.get('final_tests', 0), cnt.get('classSearch', 0)))
    k = 0
    for i in range(10 * a.yes):
      if k >= a.yes:
        break
      mode = ['any', 'inner2', 'inner1', 'boundary', 'close', 'adjacent'][i % 6]
      inst = gen.gen(n, 'hpath', mode, a.seed + 99991 * i + n)
      if inst is None:
        continue
      V, s, t = inst
      tc, tp, ac, ap_, cnt, br = time_pair(V, s, t)
      tch, tph, _, _, _, _ = time_pair(V, s, t, heuristic=True)
      print("  yes      |V|=%4d %-9s %-8s C %8.4f s  Python %8.3f s  ratio %6.0f  answers %s/%s"
            "  | with heuristic: C %.4f s, Python %.3f s" %
            (len(V), br, mode, tc, tp, tp / max(tc, 1e-6), ac, ap_, tch, tph))
      k += 1
    sys.stdout.flush()


if __name__ == "__main__":
  main()
