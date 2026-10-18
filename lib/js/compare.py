#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
#
# Compare the JavaScript port (lib/js) with the Python fast mode (lib/python/hpst_fast.py) and,
# for small inputs, the brute force (lib/python/brute.py), on random instances of
# lib/python/gen.py across shapes, endpoint modes and sizes.
#
#   python3 lib/js/compare.py --sizes 10,20,30 --count 4 --brute-max 30
#
# Per instance: Python fast mode without the heuristic (answer, path, time); brute force when
# |V| <= --brute-max; the JS port through batch.js with and without the heuristic; every
# --cli-every-th instance also through `node cli.js --json` (end to end, both heuristic
# settings). Checks: equal answers, every JS path valid (Python verify_path), and with the
# heuristic off the JS path equal to the Python path (same algorithm, same orders).
#
# Output: counts, every disagreement (with the instance as ASCII), timing summary.
#
import argparse
import json
import multiprocessing
import os
import resource
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
PY = os.path.join(os.path.dirname(HERE), 'python')
sys.path.insert(0, PY)

import brute
import gen
import hpst_fast as FM

NODE = os.environ.get('NODE', '/home/z/.config/nvm/versions/node/v24.21.0/bin/node')
SHAPES = ['blob', 'thin', 'fat', 'rect', 'hpath']
CRASHES = []
MODES = ['any', 'inner2', 'inner1', 'boundary', 'close', 'adjacent', 'plausible']


def cap_memory(gb):
  b = int(gb * (1 << 30))
  resource.setrlimit(resource.RLIMIT_AS, (b, b))


def make(job):
  n, shape, mode, seed = job
  r = None
  for i in range(20):
    r = gen.gen(n, shape, mode, seed + (1000003 * i))
    if r is not None:
      break
  if r is None:
    return None
  V, s, t = r
  return {'n': n, 'shape': shape, 'mode': mode, 'seed': seed,
          'points': sorted([list(p) for p in V]), 's': list(s), 't': list(t)}


def run_py(inst, brute_max, brute_limit):
  V = frozenset(tuple(p) for p in inst['points'])
  s, t = tuple(inst['s']), tuple(inst['t'])
  t0 = time.perf_counter()
  P = FM.decideHamPath(V, s, t, heuristic=False)
  dt = time.perf_counter() - t0
  out = {'py_answer': ('yes' if P else 'no'), 'py_path': ([list(p) for p in P] if P else None),
         'py_time': dt, 'branch': FM.LAST['branch'], 'py_how': FM.LAST['how'],
         'py_valid': ( (P is None) or FM.verify_path(V, s, t, P) )}
  if len(V) <= brute_max:
    try:
      B = brute.brute_hp(V, s, t, limit=brute_limit)
      out['brute'] = ('yes' if B else 'no')
    except RuntimeError:
      out['brute'] = None
  return out


def py_worker(args):
  inst, brute_max, brute_limit = args
  return run_py(inst, brute_max, brute_limit)


def run_node_batch(insts, heuristic, nproc):
  chunks = [insts[i::nproc] for i in range(nproc)]
  procs = []
  for ch in chunks:
    data = ''.join(json.dumps({'id': x['id'], 'points': x['points'], 's': x['s'], 't': x['t'],
                               'heuristic': heuristic}) + '\n' for x in ch)
    p = subprocess.Popen([NODE, '--max-old-space-size=3000', os.path.join(HERE, 'batch.js')],
                         stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True)
    procs.append((p, data))
  res = {}
  for (p, data), ch in zip(procs, chunks):
    out, err = p.communicate(data)
    if p.returncode != 0:
      # A crashed chunk (seen once: SIGSEGV, not reproducible) is counted and run again once.
      #
      CRASHES.append((heuristic, p.returncode, err[-2000:]))
      sys.stderr.write("batch.js failed (rc %d), retrying the chunk: %s\n" %
                       (p.returncode, err[-2000:]))
      p2 = subprocess.run([NODE, '--max-old-space-size=3000', os.path.join(HERE, 'batch.js')],
                          input=data, capture_output=True, text=True)
      out = p2.stdout
      if p2.returncode != 0:
        CRASHES.append((heuristic, p2.returncode, p2.stderr[-2000:]))
    for ln in out.splitlines():
      d = json.loads(ln)
      res[d['id']] = d
  return res


def run_cli(inst, heuristic):
  data = json.dumps({'points': inst['points'], 's': inst['s'], 't': inst['t']})
  cmd = [NODE, os.path.join(HERE, 'cli.js'), '--json']
  if not heuristic:
    cmd.append('--no-heuristic')
  p = subprocess.run(cmd, input=data, capture_output=True, text=True)
  if p.returncode != 0:
    return {'rc': p.returncode, 'err': p.stderr}
  d = json.loads(p.stdout)
  d['rc'] = 0
  return d


def main():
  ap = argparse.ArgumentParser()
  ap.add_argument('--sizes', default='10,20,30')
  ap.add_argument('--count', type=int, default=3, help="instances per (shape, mode, size)")
  ap.add_argument('--seed', type=int, default=1)
  ap.add_argument('--shapes', default=','.join(SHAPES))
  ap.add_argument('--modes', default=','.join(MODES))
  ap.add_argument('--brute-max', type=int, default=30)
  ap.add_argument('--brute-limit', type=int, default=2000000)
  ap.add_argument('--cli-every', type=int, default=10)
  ap.add_argument('--jobs', type=int, default=3)
  ap.add_argument('--mem-gb', type=float, default=5.0, help="RLIMIT_AS per process")
  ap.add_argument('--dump', default=None, help="write per-instance results (JSON lines)")
  a = ap.parse_args()
  cap_memory(a.mem_gb)

  sizes = [int(x) for x in a.sizes.split(',')]
  jobs = []
  k = 0
  for n in sizes:
    for shape in a.shapes.split(','):
      for mode in a.modes.split(','):
        for c in range(a.count):
          jobs.append((n, shape, mode, (a.seed * 7919) + (k * 104729)))
          k += 1
  T0 = time.time()
  with multiprocessing.Pool(a.jobs) as pool:
    insts = [x for x in pool.map(make, jobs) if x is not None]
    for i, x in enumerate(insts):
      x['id'] = i
    print("instances: %d (of %d jobs; the rest: mode impossible for the shape)  [%.1fs]" %
          (len(insts), len(jobs), time.time() - T0))
    sys.stdout.flush()
    pres = pool.map(py_worker, [(x, a.brute_max, a.brute_limit) for x in insts], chunksize=1)
  for x, r in zip(insts, pres):
    x.update(r)
  print("python fast done  [%.1fs]" % (time.time() - T0))
  sys.stdout.flush()
  jn = run_node_batch(insts, False, a.jobs)
  jh = run_node_batch(insts, True, a.jobs)
  print("js batch done  [%.1fs]" % (time.time() - T0))
  sys.stdout.flush()

  counts = {}
  bad = []

  def cnt(key):
    counts[key] = counts.get(key, 0) + 1

  ncli = 0
  for x in insts:
    V = frozenset(tuple(p) for p in x['points'])
    s, t = tuple(x['s']), tuple(x['t'])
    tag = "n=%d %s/%s seed=%d" % (x['n'], x['shape'], x['mode'], x['seed'])
    truth = x['py_answer']
    if not x['py_valid']:
      bad.append((tag, "python path invalid", x))
    if x.get('brute') is not None:
      cnt('brute compared')
      if x['brute'] != truth:
        bad.append((tag, "python=%s brute=%s" % (truth, x['brute']), x))
    elif 'brute' in x:
      cnt('brute over limit')
    for lbl, J in (('js-noheur', jn.get(x['id'])), ('js-heur', jh.get(x['id']))):
      if J is None:
        bad.append((tag, "%s: no result (crash?)" % lbl, x))
        continue
      cnt((lbl, x['branch'], J['answer'], J['how']))
      if J['answer'] != truth:
        bad.append((tag, "%s=%s python=%s" % (lbl, J['answer'], truth), x))
      if J['path'] is not None:
        P = [tuple(p) for p in J['path']]
        if not FM.verify_path(V, s, t, P):
          bad.append((tag, "%s path invalid" % lbl, x))
      if lbl == 'js-noheur':
        x['js_time'] = J['time']
        if J['path'] == x['py_path']:
          cnt('js-noheur path == python path')
        else:
          cnt('js-noheur path != python path')
          bad.append((tag, "js-noheur path differs from python path", x))
      else:
        x['js_time_heur'] = J['time']
    if (x['id'] % a.cli_every) == 0:
      ncli += 1
      for h in (False, True):
        C = run_cli(x, h)
        if C['rc'] != 0:
          bad.append((tag, "cli (heuristic=%s) rc=%d %s" % (h, C['rc'], C.get('err')), x))
          continue
        if C['answer'] != truth:
          bad.append((tag, "cli(heuristic=%s)=%s python=%s" % (h, C['answer'], truth), x))
        if ( (not h) and (C['path'] != x['py_path']) ):
          bad.append((tag, "cli path differs from python path", x))
        if C['path'] is not None:
          if not FM.verify_path(V, s, t, [tuple(p) for p in C['path']]):
            bad.append((tag, "cli path invalid", x))
  counts['cli runs (each x2)'] = ncli
  counts['batch.js crashed chunks (retried)'] = len(CRASHES)

  print("\ncounts:")
  for key in sorted(counts, key=str):
    print("  %-70s %d" % (key, counts[key]))
  print("\ntimes by size (seconds; python fast and js, both without heuristic):")
  for n in sizes:
    xs = [x for x in insts if x['n'] == n]
    if not xs:
      continue
    pt = sorted(x['py_time'] for x in xs)
    jt = sorted(x['js_time'] for x in xs if 'js_time' in x)
    print("  n=%-5d #%-5d py median %.4f max %.4f sum %.2f | js median %.4f max %.4f sum %.2f" %
          (n, len(xs), pt[len(pt) // 2], pt[-1], sum(pt), jt[len(jt) // 2], jt[-1], sum(jt)))
  print("\ndisagreements: %d" % len(bad))
  for tag, msg, x in bad[:30]:
    print("  %s: %s" % (tag, msg))
    V = frozenset(tuple(p) for p in x['points'])
    print(gen.to_ascii(V, tuple(x['s']), tuple(x['t'])))
  if a.dump:
    with open(a.dump, 'w') as f:
      for x in insts:
        f.write(json.dumps(x) + '\n')
  print("total %.1fs" % (time.time() - T0))
  return ( 1 if bad else 0 )


if __name__ == "__main__":
  sys.exit(main())
