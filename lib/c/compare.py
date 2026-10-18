#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
#
# Compare the C port (lib/c/hpst) with the Python fast mode (lib/python/hpst_fast.py) and, for
# small inputs, the brute force (lib/python/brute.py), on random instances from gen.py.
#
#   python3 compare.py [--sizes 10,20,40,80,160] [--count 20] [--workers 4] [--brute-max 40]
#                      [--seed 1] [--cli]
#
# Per instance (shape x endpoint mode x size x seed):
#   * C without heuristic vs Python fast without heuristic: same answer, same path (both run the
#     same algorithm in the same order), same counters (walk nodes, final tests, classes, ...);
#   * C with the heuristic: same answer;
#   * every C path checked by verify_path;
#   * brute force (|V| <= --brute-max): same answer.
# --cli also compares the command line front ends (output and exit code) on hand-made inputs.
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

import brute
import gen
import hpst_fast as FM

BIN = os.environ.get('HPST_BIN', os.path.join(HERE, 'hpst'))
SHAPES = ['blob', 'thin', 'fat', 'rect', 'hpath']
MODES = ['any', 'inner2', 'inner1', 'boundary', 'close', 'adjacent', 'plausible']


def run_c(V, s, t, heuristic):
  inp = json.dumps({'points': sorted(list(p) for p in V), 's': list(s), 't': list(t)})
  args = [BIN, '--json', '--stats']
  if not heuristic:
    args.append('--no-heuristic')
  t0 = time.perf_counter()
  r = subprocess.run(args, input=inp.encode(), capture_output=True)
  dt = time.perf_counter() - t0
  if r.returncode != 0:
    return (None, r.returncode, r.stderr.decode(), dt)
  d = json.loads(r.stdout.decode())
  return (d, 0, '', dt)


def one(job):
  shape, mode, n, seed, brute_max = job
  inst = None
  for i in range(20):
    inst = gen.gen(n, shape, mode, seed + (1000003 * i))
    if inst is not None:
      break
  if inst is None:
    return {'job': job, 'skip': True}
  V, s, t = inst
  out = {'job': job, 'skip': False, 'n': len(V), 'errs': []}
  errs = out['errs']

  t0 = time.perf_counter()
  Pp = FM.decideHamPath(V, s, t, heuristic=False)
  out['py_time'] = time.perf_counter() - t0
  py_counts = dict(FM.LAST['stats'].c)
  out['branch'] = FM.LAST['branch']
  out['how'] = FM.LAST['how']
  out['ans'] = ( Pp is not None )

  dc, rc, err, dt = run_c(V, s, t, False)
  out['c_time'] = dt
  if dc is None:
    errs.append("C (no heuristic) exit %d: %s" % (rc, err.strip()))
  else:
    Pc = ( [tuple(p) for p in dc['path']] if dc['path'] else None )
    out['c_alg_time'] = dc['stats']['times'].get('total', 0.0)
    if ( (Pc is not None) != (Pp is not None) ):
      errs.append("answer C=%s Python=%s" % (Pc is not None, Pp is not None))
    elif ( (Pc is not None) and (Pc != Pp) ):
      errs.append("paths differ (both valid: %s)" % FM.verify_path(V, s, t, Pc))
    if ( (Pc is not None) and (not FM.verify_path(V, s, t, Pc)) ):
      errs.append("C path invalid")
    if dc['stats']['counts'] != py_counts:
      errs.append("counts differ: C=%s Python=%s" % (dc['stats']['counts'], py_counts))
    if dc['stats']['branch'] != out['branch']:
      errs.append("branch differs")

  dh, rc, err, dt = run_c(V, s, t, True)
  if dh is None:
    errs.append("C (heuristic) exit %d: %s" % (rc, err.strip()))
  else:
    Ph = ( [tuple(p) for p in dh['path']] if dh['path'] else None )
    out['c_how'] = dh['stats']['decided_by']
    if ( (Ph is not None) != (Pp is not None) ):
      errs.append("answer C(heuristic)=%s Python=%s" % (Ph is not None, Pp is not None))
    if ( (Ph is not None) and (not FM.verify_path(V, s, t, Ph)) ):
      errs.append("C(heuristic) path invalid")

  if len(V) <= brute_max:
    try:
      B = brute.brute_hp(V, s, t, limit=2000000)
      out['brute'] = ( B is not None )
      if ( (B is not None) != (Pp is not None) ):
        errs.append("brute=%s, C/Python=%s" % (B is not None, Pp is not None))
    except RuntimeError:
      out['brute'] = 'skipped'
  if errs:
    out['ascii'] = gen.to_ascii(V, s, t)
  return out


# Command line front ends on hand-made inputs: same stdout (without timings) and exit code.
#
CLI_CASES = [
  ("4x3", "; a 4x3 block\n....\n....\ns..t\n", []),
  ("4x3 draw", "....\n....\ns..t\n", ['--draw']),
  ("4x3 json draw check", "....\n....\ns..t\n", ['--json', '--draw', '--check']),
  ("no", "s.\n.t\n", ['--draw', '--check']),
  ("no json", "s.\n.t\n", ['--json', '--draw']),
  ("json input", '{"points": [[0,0],[1,0],[0,1],[1,1]], "s": [0,0], "t": [1,0]}', ['--draw']),
  ("hole", "...\n.#.\ns.t\n", []),
  ("missing t", "...\n...\ns..\n", []),
  ("two s", "s..\n...\ns.t\n", []),
  ("bad char", "s.x\n..t\n", []),
  ("empty", "\n\n", []),
  ("bad json", '{"points": [[0,0]], "s": [0,0', []),
  ("t not in V", '{"points": [[0,0],[1,0]], "s": [0,0], "t": [5,5]}', []),
  ("s == t", '{"points": [[0,0],[1,0]], "s": [0,0], "t": [0,0]}', []),
  ("spaces", "  ;c\n\n s...\n .##.\n ...t\n\n", ['--no-heuristic', '--draw']),
  ("L", "s.\n..\n..\n.....\n....t\n", ['--no-heuristic', '--draw', '--check']),
]


def cli_compare():
  bad = 0
  for name, text, flags in CLI_CASES:
    rp = subprocess.run([sys.executable, os.path.join(HERE, '..', 'python', 'hpst_cli.py')] +
                        flags, input=text.encode(), capture_output=True)
    rc = subprocess.run([BIN] + flags, input=text.encode(), capture_output=True)
    same = ( (rp.returncode == rc.returncode) and (rp.stdout == rc.stdout) )
    print("  cli %-22s exit py=%d c=%d stdout %s" %
          (name, rp.returncode, rc.returncode, ('same' if (rp.stdout == rc.stdout) else 'DIFF')))
    if rp.returncode == 2:
      print("      py: %s      c:  %s" % (rp.stderr.decode().strip()[:100] + '\n',
                                          rc.stderr.decode().strip()[:100]))
    if not same:
      bad += 1
      print(rp.stdout.decode())
      print(rc.stdout.decode())
  return bad


def main():
  ap = argparse.ArgumentParser()
  ap.add_argument('--sizes', default='10,20,40,80,160')
  ap.add_argument('--count', type=int, default=10)
  ap.add_argument('--workers', type=int, default=4)
  ap.add_argument('--brute-max', type=int, default=40)
  ap.add_argument('--seed', type=int, default=1)
  ap.add_argument('--shapes', default=','.join(SHAPES))
  ap.add_argument('--modes', default=','.join(MODES))
  ap.add_argument('--cli', action='store_true')
  a = ap.parse_args()

  if a.cli:
    b = cli_compare()
    print("cli cases with a difference: %d / %d" % (b, len(CLI_CASES)))

  sizes = [int(x) for x in a.sizes.split(',') if x]
  jobs = []
  for n in sizes:
    for shape in a.shapes.split(','):
      for mode in a.modes.split(','):
        for k in range(a.count):
          jobs.append((shape, mode, n, a.seed + (7919 * k) + (104729 * n), a.brute_max))
  T0 = time.perf_counter()
  tally = {}
  nerr = 0
  ninst = 0
  nbrute = 0
  pyt = 0.0
  ct = 0.0
  with multiprocessing.Pool(a.workers) as pool:
    for r in pool.imap_unordered(one, jobs, chunksize=2):
      if r['skip']:
        tally['skipped'] = tally.get('skipped', 0) + 1
        continue
      ninst += 1
      shape, mode, n, seed, _ = r['job']
      k = (n, r['branch'], ('yes' if r['ans'] else 'no'), r['how'])
      tally[k] = tally.get(k, 0) + 1
      if r.get('brute') in (True, False):
        nbrute += 1
      pyt += r['py_time']
      ct += r.get('c_alg_time', 0.0)
      if r['errs']:
        nerr += 1
        print("DISAGREE %s seed=%d n=%d: %s" % ((shape, mode), seed, r['n'], r['errs']))
        print(r['ascii'])
  print("instances: %d, with a disagreement: %d, brute-force checked: %d, %.1f s" %
        (ninst, nerr, nbrute, time.perf_counter() - T0))
  print("total algorithm time (no heuristic): Python %.2f s, C %.2f s" % (pyt, ct))
  for k in sorted(tally, key=str):
    print("   %-40s %d" % (k, tally[k]))
  return ( 1 if nerr else 0 )


if __name__ == "__main__":
  sys.exit(main())
