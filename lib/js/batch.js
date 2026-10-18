#!/usr/bin/env node
// SPDX-License-Identifier: CC0-1.0
//
// Batch runner for testing and timing (used by compare.py): reads JSON lines
// {"id": ..., "points": [[x, y], ...], "s": [x, y], "t": [x, y], "heuristic": bool} from stdin
// and writes one JSON line per instance: {"id", "answer", "path", "how", "time"} (time in
// seconds, `solve` only, no process start-up or parsing).
//

import fs from 'node:fs';
import { solve } from './hpst.js';

const lines = fs.readFileSync(0, 'utf8').split('\n');
for (const ln of lines) {
  if (ln.trim() === '') { continue; }
  const d = JSON.parse(ln);
  const t0 = performance.now();
  const R = solve(d.points, d.s, d.t, { heuristic: ( (d.heuristic === undefined) ? true : d.heuristic ) });
  const dt = (performance.now() - t0) / 1000;
  process.stdout.write(JSON.stringify({ id: d.id, answer: R.answer, path: R.path,
                                        how: R.stats.decided_by, time: dt,
                                        counts: R.stats.counts }) + '\n');
}
