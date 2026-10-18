// SPDX-License-Identifier: CC0-1.0
//
// Interactive demo of the solid-grid-graph Hamiltonian s-t path decider (the JavaScript port
// in lib/js/hpst.js of the Lean-verified `decideHamPath`, fast mode).
//
// Click a lattice point to add or remove it (mode "edit"), or to place s or t (modes "s", "t").
// "random" makes a random solid shape with endpoints whose colours allow a path, "solve" runs
// the decider, and "show path" toggles the drawn path.
//

// demo/js/hpst.js is a copy of lib/js/hpst.js, so that the demo works when served on its own.
import { solve, isSolid, parseAscii, InputError } from './hpst.js';
import { stamp, pickEndpoints } from './gen.js';

const CELL = 22, MARGIN = 30;

const st = {
  V: new Set(),
  s: null,
  t: null,
  path: null,
  showPath: true,
  mode: 'edit',
  nx: 30, ny: 22,
};

const key = (p) => (p[0] + ',' + p[1]);
const unkey = (k) => k.split(',').map(Number);
const two = new Two({ type: Two.Types.svg, width: (st.nx * CELL) + (2 * MARGIN),
                      height: (st.ny * CELL) + (2 * MARGIN) });

// Lattice point (x, y) to canvas coordinates, y up.
//
const cx = (x) => (MARGIN + (x * CELL));
const cy = (y) => (MARGIN + ((st.ny - 1 - y) * CELL));

function ramp(u) {
  const stops = [[13, 71, 161], [123, 31, 162], [211, 47, 47], [245, 124, 0]];
  const v = u * (stops.length - 1);
  const j = Math.min(Math.floor(v), stops.length - 2), f = v - j;
  const c = [0, 1, 2].map((i) => Math.round(stops[j][i] + (f * (stops[j + 1][i] - stops[j][i]))));
  return 'rgb(' + c.join(',') + ')';
}

function msg(text, bad = false) {
  const e = document.getElementById('ui_msg');
  e.textContent = text;
  e.style.color = ( bad ? 'rgb(197,40,61)' : 'rgb(47,55,55)' );
}

function draw() {
  two.clear();
  // the lattice
  for (let x = 0; x < st.nx; x++) {
    for (let y = 0; y < st.ny; y++) {
      const d = two.makeCircle(cx(x), cy(y), 1.2);
      d.fill = 'rgb(210,210,210)';
      d.noStroke();
    }
  }
  // cells and edges of V
  for (const k of st.V) {
    const [x, y] = unkey(k);
    if ( st.V.has(key([x + 1, y])) && st.V.has(key([x, y + 1])) && st.V.has(key([x + 1, y + 1])) ) {
      const r = two.makeRectangle(cx(x) + (CELL / 2), cy(y) - (CELL / 2), CELL, CELL);
      r.fill = 'rgb(240,240,236)';
      r.noStroke();
    }
  }
  for (const k of st.V) {
    const [x, y] = unkey(k);
    for (const q of [[x + 1, y], [x, y + 1]]) {
      if (st.V.has(key(q))) {
        const l = two.makeLine(cx(x), cy(y), cx(q[0]), cy(q[1]));
        l.stroke = 'rgb(190,190,190)';
        l.linewidth = 1;
      }
    }
  }
  // the path, coloured from s (blue) to t (orange)
  if ( st.showPath && (st.path !== null) ) {
    const n = st.path.length - 1;
    for (let i = 0; i < n; i++) {
      const a = st.path[i], b = st.path[i + 1];
      const l = two.makeLine(cx(a[0]), cy(a[1]), cx(b[0]), cy(b[1]));
      l.stroke = ramp(i / n);
      l.linewidth = 5;
      l.cap = 'round';
    }
  }
  // points, black or white by the parity of x + y
  for (const k of st.V) {
    const [x, y] = unkey(k);
    const c = two.makeCircle(cx(x), cy(y), 3.5);
    c.fill = ( (((x + y) % 2) === 0) ? 'rgb(30,30,30)' : 'rgb(255,255,255)' );
    c.stroke = 'rgb(30,30,30)';
    c.linewidth = 1;
  }
  for (const [p, name, col] of [[st.s, 's', ramp(0)], [st.t, 't', ramp(1)]]) {
    if (p === null) { continue; }
    const c = two.makeCircle(cx(p[0]), cy(p[1]), 7);
    c.fill = col;
    c.stroke = 'white';
    c.linewidth = 2;
    const tx = two.makeText(name, cx(p[0]) + 11, cy(p[1]) - 11);
    tx.size = 16;
    tx.weight = 700;
    tx.fill = col;
  }
  two.update();
  document.getElementById('ui_info').textContent =
    '|V| = ' + st.V.size + ( (st.s && st.t) ? ('   s = (' + st.s + ')   t = (' + st.t + ')') : '' );
}

function pointsArray() { return [...st.V].map(unkey); }

function setPath(P) {
  st.path = P;
  draw();
}

function randomInstance() {
  const n = Math.max(8, Math.min(400, parseInt(document.getElementById('ui_n').value, 10) || 80));
  const wmin = parseInt(document.getElementById('ui_wmin').value, 10) || 2;
  let V = null;
  for (let i = 0; (i < 20) && (V === null); i++) { V = stamp(n, Math.random, wmin); }
  if (V === null) { msg('no shape found, try again', true); return; }
  const w = Math.max(...V.map((p) => p[0])) + 1, h = Math.max(...V.map((p) => p[1])) + 1;
  resize(Math.max(w + 2, 12), Math.max(h + 2, 10));
  V = V.map((p) => [p[0] + 1, p[1] + 1]);
  st.V = new Set(V.map(key));
  const e = pickEndpoints(V);
  st.s = ( e ? e[0] : null );
  st.t = ( e ? e[1] : null );
  st.path = null;
  msg('random shape with ' + V.length + ' points; press "solve"');
  draw();
}

function randomEndpoints() {
  const V = pointsArray();
  const e = pickEndpoints(V);
  if (e === null) { msg('no endpoints with matching colours (the colour counts differ by more than 1)', true); return; }
  [st.s, st.t] = e;
  st.path = null;
  msg('new endpoints; press "solve"');
  draw();
}

function runSolve() {
  if ( (st.s === null) || (st.t === null) ) { msg('place s and t first', true); return; }
  const V = pointsArray();
  if (!isSolid(V)) { msg('V is not solid (it has a hole); the algorithm assumes a solid grid graph', true); return; }
  const heuristic = document.getElementById('ui_heur').checked;
  const t0 = performance.now();
  let r = null;
  try {
    r = solve(V, st.s, st.t, { heuristic: heuristic });
  }
  catch (err) {
    msg( ((err instanceof InputError) ? err.message : String(err)), true );
    return;
  }
  const ms = (performance.now() - t0).toFixed(1);
  const how = r.stats.decided_by + ', case ' + r.stats.branch;
  if (r.answer === 'yes') {
    msg('Hamiltonian s-t path found (' + ms + ' ms; ' + how + ')');
    setPath(r.path);
  }
  else {
    msg('no Hamiltonian s-t path (' + ms + ' ms; ' + how + ')', true);
    setPath(null);
  }
}

function resize(nx, ny) {
  st.nx = nx;
  st.ny = ny;
  two.width = (st.nx * CELL) + (2 * MARGIN);
  two.height = (st.ny * CELL) + (2 * MARGIN);
  two.renderer.setSize(two.width, two.height);
}

function onClick(ev) {
  const rect = two.renderer.domElement.getBoundingClientRect();
  const x = Math.round(((ev.clientX - rect.left) - MARGIN) / CELL);
  const y = (st.ny - 1) - Math.round(((ev.clientY - rect.top) - MARGIN) / CELL);
  if ( (x < 0) || (y < 0) || (x >= st.nx) || (y >= st.ny) ) { return; }
  const k = key([x, y]);
  if (st.mode === 'edit') {
    if (st.V.has(k)) {
      st.V.delete(k);
      if ( st.s && (key(st.s) === k) ) { st.s = null; }
      if ( st.t && (key(st.t) === k) ) { st.t = null; }
    }
    else { st.V.add(k); }
  }
  else {
    if (!st.V.has(k)) { st.V.add(k); }
    if (st.mode === 's') { st.s = [x, y]; } else { st.t = [x, y]; }
  }
  st.path = null;
  msg('');
  draw();
}

// ASCII format of lib/README.md: '.' point, '#' or space not a point, 's' / 't' endpoints.
//
function toAscii() {
  const V = pointsArray();
  if (V.length === 0) { return ''; }
  const x0 = Math.min(...V.map((p) => p[0])), x1 = Math.max(...V.map((p) => p[0]));
  const y0 = Math.min(...V.map((p) => p[1])), y1 = Math.max(...V.map((p) => p[1]));
  const rows = [];
  for (let y = y1; y >= y0; y--) {
    let r = '';
    for (let x = x0; x <= x1; x++) {
      const k = key([x, y]);
      r += ( (st.s && (key(st.s) === k)) ? 's' : ( (st.t && (key(st.t) === k)) ? 't' : (st.V.has(k) ? '.' : '#') ) );
    }
    rows.push(r);
  }
  return rows.join('\n');
}

function fromAscii() {
  try {
    const r = parseAscii(document.getElementById('ui_ascii').value);
    const w = Math.max(...r.V.map((p) => p[0])) + 1, h = Math.max(...r.V.map((p) => p[1])) + 1;
    if ( (w > st.nx) || (h > st.ny) ) { resize(Math.max(w, st.nx), Math.max(h, st.ny)); }
    st.V = new Set(r.V.map(key));
    st.s = r.s;
    st.t = r.t;
    st.path = null;
    msg('loaded ' + r.V.length + ' points');
    draw();
  }
  catch (err) { msg(err.message, true); }
}

function init() {
  two.appendTo(document.getElementById('ui_canvas'));
  two.renderer.domElement.addEventListener('click', onClick);
  document.getElementById('ui_btn_random').onclick = randomInstance;
  document.getElementById('ui_btn_st').onclick = randomEndpoints;
  document.getElementById('ui_btn_solve').onclick = runSolve;
  document.getElementById('ui_btn_clear').onclick = () => { st.V = new Set(); st.s = null; st.t = null; st.path = null; msg(''); draw(); };
  document.getElementById('ui_show').onchange = (e) => { st.showPath = e.target.checked; draw(); };
  document.getElementById('ui_btn_export').onclick = () => { document.getElementById('ui_ascii').value = toAscii(); };
  document.getElementById('ui_btn_import').onclick = fromAscii;
  for (const m of ['edit', 's', 't']) {
    document.getElementById('ui_mode_' + m).onchange = () => { st.mode = m; };
  }
  randomInstance();
}

init();
