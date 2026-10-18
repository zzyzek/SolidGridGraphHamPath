#!/usr/bin/env node
// SPDX-License-Identifier: CC0-1.0
//
// Command line front end for the JavaScript port of `decideHamPath` fast mode (hpst.js); the same
// input formats, flags, output and exit codes as lib/python/hpst_cli.py in fast mode.
//
//   node lib/js/cli.js [FILE] [--draw] [--json] [--stats] [--no-heuristic] [--mode fast]
//
// Exit codes: 0 answered (yes or no), 1 invalid witness (internal error), 2 bad input (format,
// missing or equal endpoints, endpoint not in V, V not solid) or bad arguments.
//

import fs from 'node:fs';
import { solve, parseInput, checkInput, verifyPath, draw, InputError } from './hpst.js';

const USAGE = "usage: cli.js [-h] [--mode {fast}] [--draw] [--json] [--stats] [--no-heuristic] [file]";

const HELP = USAGE + `

Decide whether a solid grid graph has a Hamiltonian s-t path (Lean decideHamPath, fast mode).

positional arguments:
  file            input file (ASCII grid or JSON); default stdin

options:
  -h, --help      show this help message and exit
  --mode {fast}   only fast mode is ported (ref mode: lib/python/hpst_cli.py)
  --draw          draw the path
  --json          JSON output
  --stats         time and counts
  --no-heuristic  skip the heuristic yes-search (the full algorithm decides)
`;

// Floats are boxed so that the output prints them as Python does (`0.0`, `0.0123`).
//
class PyFloat {
  constructor(v) { this.v = v; }
}

function round4(v) { return new PyFloat(Math.round(v * 10000) / 10000); }

function floatStr(v) { return ( Number.isInteger(v) ? v.toFixed(1) : String(v) ); }

// Python `json.dumps` (default separators, ensure_ascii).
//
function pyJsonStr(s) {
  let out = '"';
  for (const ch of s) {
    const c = ch.codePointAt(0);
    if      (ch === '"')  { out += '\\"'; }
    else if (ch === '\\') { out += '\\\\'; }
    else if (ch === '\n') { out += '\\n'; }
    else if (ch === '\r') { out += '\\r'; }
    else if (ch === '\t') { out += '\\t'; }
    else if (ch === '\b') { out += '\\b'; }
    else if (ch === '\f') { out += '\\f'; }
    else if ( (c < 0x20) || (c > 0x7e) ) {
      const hex = (u) => ('\\u' + u.toString(16).padStart(4, '0'));
      if (c > 0xffff) {
        const d = c - 0x10000;
        out += hex(0xd800 + (d >> 10)) + hex(0xdc00 + (d & 0x3ff));
      }
      else {
        out += hex(c);
      }
    }
    else {
      out += ch;
    }
  }
  return out + '"';
}

function pyJson(v) {
  if (v === null)                { return 'null'; }
  if (v instanceof PyFloat)      { return floatStr(v.v); }
  if (typeof v === 'boolean')    { return ( v ? 'true' : 'false' ); }
  if (typeof v === 'number')     { return String(v); }
  if (typeof v === 'string')     { return pyJsonStr(v); }
  if (Array.isArray(v))          { return '[' + v.map(pyJson).join(', ') + ']'; }
  return '{' + Object.keys(v).map((k) => (pyJsonStr(k) + ': ' + pyJson(v[k]))).join(', ') + '}';
}

// Python `str` of a stats value (dicts printed by repr).
//
function pyRepr(v) {
  if (v === null)           { return 'None'; }
  if (v instanceof PyFloat) { return floatStr(v.v); }
  if (typeof v === 'string') { return "'" + v + "'"; }
  if (typeof v === 'number') { return String(v); }
  return '{' + Object.keys(v).map((k) => ("'" + k + "': " + pyRepr(v[k]))).join(', ') + '}';
}

function pyStr(v) { return ( (typeof v === 'string') ? v : pyRepr(v) ); }

function argError(msg) {
  process.stderr.write(USAGE + "\ncli.js: error: " + msg + "\n");
  return 2;
}

function osError(ex, file) {
  const m = { ENOENT: [2, 'No such file or directory'], EACCES: [13, 'Permission denied'],
              EISDIR: [21, 'Is a directory'] }[ex.code];
  return ( m ? ("[Errno " + m[0] + "] " + m[1] + ": '" + file + "'") : ex.message );
}

function main(argv) {
  const a = { file: null, mode: 'fast', draw: false, json: false, stats: false, noHeur: false };
  const extra = [];
  for (let i = 0; i < argv.length; i++) {
    const x = argv[i];
    if      ( (x === '-h') || (x === '--help') ) { process.stdout.write(HELP); return 0; }
    else if (x === '--draw')         { a.draw = true; }
    else if (x === '--json')         { a.json = true; }
    else if (x === '--stats')        { a.stats = true; }
    else if (x === '--no-heuristic') { a.noHeur = true; }
    else if ( (x === '--mode') || x.startsWith('--mode=') ) {
      let m;
      if (x === '--mode') {
        if ((i + 1) >= argv.length) { return argError("argument --mode: expected one argument"); }
        m = argv[++i];
      }
      else {
        m = x.slice(7);
      }
      if (m !== 'fast') {
        return argError("argument --mode: invalid choice: '" + m + "' (choose from 'fast'; " +
                        "ref mode and --check: lib/python/hpst_cli.py)");
      }
      a.mode = m;
    }
    else if ( x.startsWith('-') && (x !== '-') ) { extra.push(x); }
    else if (a.file === null) { a.file = x; }
    else                      { extra.push(x); }
  }
  if (extra.length > 0) { return argError("unrecognized arguments: " + extra.join(' ')); }

  let V, s, t;
  try {
    let text;
    try {
      text = ( (a.file !== null) ? fs.readFileSync(a.file, 'utf8') : fs.readFileSync(0, 'utf8') );
    }
    catch (ex) {
      throw new InputError(osError(ex, a.file));
    }
    const r = parseInput(text);
    V = r.V;
    s = r.s;
    t = r.t;
    checkInput(V, s, t);
  }
  catch (ex) {
    if (ex instanceof InputError) {
      process.stderr.write("error: " + ex.message + "\n");
      return 2;
    }
    throw ex;
  }

  const t0 = performance.now();
  const R = solve(V, s, t, { heuristic: !a.noHeur });
  const dt = (performance.now() - t0) / 1000;
  const P = R.path;
  const times = {};
  for (const k of Object.keys(R.stats.times)) { times[k] = round4(R.stats.times[k]); }
  const stats = { counts: R.stats.counts, times: times, branch: R.stats.branch,
                  decided_by: R.stats.decided_by, time: round4(dt), points: V.length };

  let rc = 0;
  if ( (P !== null) && (!verifyPath(V, s, t, P)) ) {
    process.stderr.write("internal error: invalid witness path\n");
    rc = 1;
  }

  let out;
  if (a.json) {
    const o = { answer: ( P ? 'yes' : 'no' ), path: ( P ? P : null ) };
    if (a.stats) { o.stats = stats; }
    if (a.draw)  { o.drawing = draw(V, s, t, P); }
    out = pyJson(o) + '\n';
  }
  else {
    out = ( P ? 'yes' : 'no' ) + '\n';
    if (P) { out += P.map((p) => (p[0] + ',' + p[1])).join(' ') + '\n'; }
    if (a.draw) { out += draw(V, s, t, P) + '\n'; }
    if (a.stats) {
      for (const k of Object.keys(stats)) { out += "stats " + k + ": " + pyStr(stats[k]) + "\n"; }
    }
  }
  process.stdout.write(out);
  return rc;
}

process.exitCode = main(process.argv.slice(2));
