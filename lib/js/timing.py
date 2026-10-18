#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
#
# Timings: JavaScript port (batch.js, in-process `solve` time) vs Python fast mode
# (hpst_fast.decideHamPath, in-process time), both without the heuristic, on
#   yes : planted-path instances (gen.py shape hpath, endpoint modes any / inner2 / boundary),
#   pl  : hard-"no" candidates: --pl-search instances (shapes hpath / rect / fat, endpoint modes
#         plausible, and inner2 / close on rect / fat, which reach twoHoleCase) are classified by the JS
#         port; the --pl slowest "no" answers decided by the algorithm (not by the global
#         necessary conditions) and --pl-yes "yes" answers are kept.
# Also checks equal answers and equal paths (heuristic off).
#
#   python3 lib/js/timing.py -n 400 --yes 20 --pl-search 600 --pl 40 --py-timeout 120
#
import argparse
import json
import os
import resource
import subprocess
import sys
import time
import multiprocessing
from multiprocessing.pool import ThreadPool

HERE = os.path.dirname(os.path.abspath(__file__))
PYDIR = os.path.join(os.path.dirname(HERE), 'python')
sys.path.insert(0, PYDIR)

import gen

NODE = os.environ.get('NODE', '/home/z/.config/nvm/versions/node/v24.21.0/bin/node')

PYONE = r'''
import json, sys, time
sys.path.insert(0, %r)
import hpst_fast as FM
d = json.loads(sys.stdin.read())
V = frozenset(tuple(p) for p in d['points'])
t0 = time.perf_counter()
P = FM.decideHamPath(V, tuple(d['s']), tuple(d['t']), heuristic=False)
dt = time.perf_counter() - t0
print(json.dumps({'answer': ('yes' if P else 'no'), 'path': ([list(p) for p in P] if P else None),
                  'time': dt, 'branch': FM.LAST['branch'], 'how': FM.LAST['how'],
                  'counts': FM.LAST['stats'].c}))
''' % PYDIR


def limit_mem():
  b = 6 * (1 << 30)
  resource.setrlimit(resource.RLIMIT_AS, (b, b))


def run_py(inst, tmo):
  try:
    p = subprocess.run([sys.executable, '-c', PYONE], input=json.dumps(inst), capture_output=True,
                       text=True, timeout=tmo, preexec_fn=limit_mem)
  except subprocess.TimeoutExpired:
    return {'answer': None, 'time': None}
  if p.returncode != 0:
    return {'answer': 'ERR', 'time': None, 'err': p.stderr[-1000:]}
  return json.loads(p.stdout)


def run_js(insts, tmo):
  data = ''.join(json.dumps({'id': i, 'points': x['points'], 's': x['s'], 't': x['t'],
                             'heuristic': False}) + '\n' for i, x in enumerate(insts))
  p = subprocess.run([NODE, '--max-old-space-size=4000', os.path.join(HERE, 'batch.js')],
                     input=data, capture_output=True, text=True, timeout=tmo,
                     preexec_fn=limit_mem)
  if p.returncode != 0:
    sys.stderr.write("batch.js rc %d: %s\n" % (p.returncode, p.stderr[-2000:]))
  res = {}
  for ln in p.stdout.splitlines():
    d = json.loads(ln)
    res[d['id']] = d
  return res


def gen_one(job):
  n, kind, shape, mode, seed = job
  r = gen.gen(n, shape, mode, seed)
  if r is None:
    return None
  V, s, t = r
  return {'kind': kind, 'shape': shape, 'mode': mode, 'n': len(V),
          'points': sorted([list(p) for p in V]), 's': list(s), 't': list(t)}


PL_PLAN = ('hpath:plausible,rect:plausible,fat:plausible,rect:inner2,fat:inner2,rect:close,'
           'fat:close')


def generate(n, kind, count, seed, jobs, pl_plan=PL_PLAN):
  if kind == 'yes':
    plan = [('hpath', m) for m in ('any', 'inner2', 'boundary')]
  else:
    plan = [tuple(x.split(':')) for x in pl_plan.split(',')]
  js = [(n, kind, plan[i % len(plan)][0], plan[i % len(plan)][1], seed + (7919 * i))
        for i in range(count)]
  with multiprocessing.Pool(jobs) as pool:
    return [x for x in pool.map(gen_one, js, chunksize=1) if x is not None]


def q(xs, f):
  xs = sorted(xs)
  return ( xs[min(len(xs) - 1, int(f * len(xs)))] if xs else float('nan') )


def main():
  ap = argparse.ArgumentParser()
  ap.add_argument('-n', type=int, default=100)
  ap.add_argument('--yes', type=int, default=20)
  ap.add_argument('--pl', type=int, default=40)
  ap.add_argument('--seed', type=int, default=3)
  ap.add_argument('--pl-search', type=int, default=200, help="plausible candidates")
  ap.add_argument('--pl-yes', type=int, default=10)
  ap.add_argument('--pl-plan', default=PL_PLAN, help="shape:mode list for the no-search")
  ap.add_argument('--py-timeout', type=float, default=120.0)
  ap.add_argument('--jobs', type=int, default=3)
  ap.add_argument('--save', default=None, help="write instances and results (JSON lines)")
  a = ap.parse_args()

  T0 = time.time()
  yes = generate(a.n, 'yes', a.yes, a.seed, a.jobs)
  cand = generate(a.n, 'pl', a.pl_search, a.seed + 1, a.jobs, a.pl_plan)
  print("n=%d: %d yes-candidates, %d plausible candidates  [gen %.1fs]" %
        (a.n, len(yes), len(cand), time.time() - T0))

  # Hard "no" search: classify the plausible candidates with the JS port, keep up to --pl
  # "no" and --pl-yes "yes" (both re-decided by Python below).
  #
  jc = run_js(cand, 1200)
  nos = [(jc[i]['time'], x) for i, x in enumerate(cand)
         if ( (i in jc) and (jc[i]['answer'] == 'no') and (jc[i]['how'] == 'algorithm') )]
  nos = [x for _, x in sorted(nos, key=lambda y: -y[0])]
  yss = [x for i, x in enumerate(cand) if ( (i in jc) and (jc[i]['answer'] == 'yes') )]
  print("candidates: %d no (not globally rejected), %d yes (js)  [%.1fs]" %
        (len(nos), len(yss), time.time() - T0))
  insts = yes + nos[:a.pl] + yss[:a.pl_yes]
  sys.stdout.flush()
  with ThreadPool(a.jobs) as pool:
    pr = pool.map(lambda x: run_py(x, a.py_timeout), insts, chunksize=1)
  print("python done [%.1fs]" % (time.time() - T0))
  sys.stdout.flush()
  jr = run_js(insts, 1200)
  print("js done [%.1fs]" % (time.time() - T0))

  bad = []
  groups = {}
  for i, (x, p) in enumerate(zip(insts, pr)):
    j = jr.get(i)
    x['py'] = p
    x['js'] = j
    if j is None:
      bad.append((i, "js missing"))
      continue
    if p['answer'] is None:
      g = (x['kind'], 'py-timeout')
    else:
      if p['answer'] != j['answer']:
        bad.append((i, "answer js=%s py=%s" % (j['answer'], p['answer'])))
      elif p.get('path') != j['path']:
        bad.append((i, "path differs"))
      g = (x['kind'], j['answer'])
    groups.setdefault(g, []).append(x)

  print("\n%-22s %5s %8s | %-26s | %-26s | %s" %
        ("group", "#", "|V| med", "python  median / max (s)", "js  median / max (s)",
         "max ratio py/js"))
  for g in sorted(groups):
    xs = groups[g]
    pt = [x['py']['time'] for x in xs if x['py']['time'] is not None]
    jt = [x['js']['time'] for x in xs]
    rat = [x['py']['time'] / max(x['js']['time'], 1e-6) for x in xs if x['py']['time']]
    print("%-22s %5d %8d | %10.4f / %10.4f   | %10.4f / %10.4f   | med %.1f" %
          ("%s/%s" % g, len(xs), q([x['n'] for x in xs], 0.5), q(pt, 0.5), (max(pt) if pt else 0),
           q(jt, 0.5), max(jt), q(rat, 0.5)))
  print("\nslowest 5 (python time) among answered:")
  ans = [x for x in insts if ( (x.get('js') is not None) and (x['py']['time'] is not None) )]
  ans.sort(key=lambda x: -x['py']['time'])
  for x in ans[:5]:
    c = x['py'].get('counts', {})
    print("  %s %s/%s |V|=%d %s branch=%s py %.3fs js %.3fs walk_nodes=%s final_tests=%s classSearch=%s" %
          (x['kind'], x['shape'], x['mode'], x['n'], x['js']['answer'], x['py'].get('branch'),
           x['py']['time'], x['js']['time'], c.get('walk_nodes'), c.get('final_tests'),
           c.get('classSearch')))
  tos = [x for x in insts if ( (x['py']['answer'] is None) and (x.get('js') is not None) )]
  if tos:
    print("\npython timeouts (> %.0fs): %d; js on them: %s" %
          (a.py_timeout, len(tos), ', '.join("%s %.3fs" % (x['js']['answer'], x['js']['time'])
                                               for x in tos)))
  print("\ndisagreements: %d" % len(bad))
  for i, msg in bad[:20]:
    x = insts[i]
    print("  #%d %s/%s |V|=%d: %s" % (i, x['shape'], x['mode'], x['n'], msg))
    if x['n'] <= 200:
      print(gen.to_ascii(frozenset(tuple(p) for p in x['points']), tuple(x['s']), tuple(x['t'])))
  if a.save:
    with open(a.save, 'w') as f:
      for x in insts:
        f.write(json.dumps(x) + '\n')
  print("total %.1fs" % (time.time() - T0))


if __name__ == "__main__":
  main()
