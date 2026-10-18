// SPDX-License-Identifier: CC0-1.0
//
// Random solid grid graphs for the demo: a JavaScript port of the `stamp` shapes of
// lib/python/gen.py. A union of template shapes (rectangles, L, T, plus, U, staircase bands,
// discs), each rotated or reflected at random and placed to overlap the shape in a 2x2 block.
// Then only points that lie in some 2x2 cell are kept, holes are filled, and the colour counts
// are repaired by removing convex corner points of the majority colour.
//
// Points are [x, y]; sets of points are JS Sets of "x,y" keys.
//

const key = (x, y) => (x + ',' + y);
const unkey = (k) => k.split(',').map(Number);

function box(w, h, x0 = 0, y0 = 0) {
  const S = new Set();
  for (let x = x0; x < (x0 + w); x++) {
    for (let y = y0; y < (y0 + h); y++) { S.add(key(x, y)); }
  }
  return S;
}

function union(...sets) {
  const S = new Set();
  for (const T of sets) { for (const k of T) { S.add(k); } }
  return S;
}

function randint(rng, a, b) { return a + Math.floor(rng() * ((b - a) + 1)); }

// Template shapes, each at least `wmin` points wide; `m` bounds the longest side.
//
function template(rng, m, wmin) {
  m = Math.max((2 * wmin) + 1, m);
  const kinds = ['rect', 'rect', 'L', 'T', 'plus', 'U', 'stair', 'disc'];
  const k = kinds[Math.floor(rng() * kinds.length)];
  const a = randint(rng, wmin, Math.max(wmin, Math.min(4, Math.floor((m - 1) / 2))));
  if (k === 'rect') { return box(randint(rng, Math.max(3, wmin), m), randint(rng, Math.max(3, wmin), m)); }
  if (k === 'L') { return union(box(randint(rng, a + 2, m), a), box(a, randint(rng, a + 2, m))); }
  if (k === 'T') {
    const w = randint(rng, a + 2, m), h = randint(rng, a + 2, m), c = Math.floor((w - a) / 2);
    return union(box(w, a, 0, h - a), box(a, h, c, 0));
  }
  if (k === 'plus') {
    const mm = randint(rng, a + 2, m), c = Math.floor((mm - a) / 2);
    return union(box(mm, a, 0, c), box(a, mm, c, 0));
  }
  if (k === 'U') {
    const w = randint(rng, (2 * a) + 1, Math.max((2 * a) + 1, m)), h = randint(rng, a + 2, m);
    return union(box(w, a), box(a, h), box(a, h, w - a, 0));
  }
  if (k === 'stair') {
    const n = randint(rng, 2, Math.max(2, Math.floor(m / a)));
    let S = new Set();
    for (let i = 0; i < n; i++) { S = union(S, box(a + 1, a + 1, i * (a - 1), i * (a - 1))); }
    return S;
  }
  const r = randint(rng, 2, Math.max(2, Math.min(4, Math.floor(m / 2))));
  const S = new Set();
  for (let x = -r; x <= r; x++) {
    for (let y = -r; y <= r; y++) {
      if (((x * x) + (y * y)) <= ((r * r) + r)) { S.add(key(x, y)); }
    }
  }
  return S;
}

function orient(S, rng) {
  const k = Math.floor(rng() * 4), refl = (rng() < 0.5);
  const pts = [];
  for (const kk of S) {
    let [x, y] = unkey(kk);
    if (refl) { x = -x; }
    for (let i = 0; i < k; i++) { [x, y] = [-y, x]; }
    pts.push([x, y]);
  }
  const mx = Math.min(...pts.map((p) => p[0])), my = Math.min(...pts.map((p) => p[1]));
  return new Set(pts.map(([x, y]) => key(x - mx, y - my)));
}

// The 2x2 cells of S, named by their lower-left point.
//
function cellsIn(S) {
  const out = [];
  for (const kk of S) {
    const [x, y] = unkey(kk);
    if ( S.has(key(x + 1, y)) && S.has(key(x, y + 1)) && S.has(key(x + 1, y + 1)) ) { out.push([x, y]); }
  }
  return out;
}

function place(S, piece, rng) {
  if (S.size === 0) { return new Set(piece); }
  const cs = cellsIn(S), cp = cellsIn(piece);
  if ( (cs.length === 0) || (cp.length === 0) ) { return S; }
  for (let i = 0; i < 60; i++) {
    const a = cs[Math.floor(rng() * cs.length)], b = cp[Math.floor(rng() * cp.length)];
    const dx = a[0] - b[0], dy = a[1] - b[1];
    const moved = new Set();
    let fresh = 0;
    for (const kk of piece) {
      const [x, y] = unkey(kk);
      const q = key(x + dx, y + dy);
      moved.add(q);
      if (!S.has(q)) { fresh++; }
    }
    if (fresh > 0) { return union(S, moved); }
  }
  return S;
}

// Keep only the points that lie in some 2x2 cell.
//
function open2(S) {
  const keep = new Set();
  for (const [x, y] of cellsIn(S)) {
    keep.add(key(x, y)); keep.add(key(x + 1, y)); keep.add(key(x, y + 1)); keep.add(key(x + 1, y + 1));
  }
  return keep;
}

function connected(S) {
  if (S.size === 0) { return true; }
  const start = S.values().next().value, seen = new Set([start]), st = [start];
  while (st.length > 0) {
    const [x, y] = unkey(st.pop());
    for (const q of [key(x + 1, y), key(x - 1, y), key(x, y + 1), key(x, y - 1)]) {
      if ( S.has(q) && (!seen.has(q)) ) { seen.add(q); st.push(q); }
    }
  }
  return (seen.size === S.size);
}

// Add every missing box point that cannot escape by king moves (the holes).
//
function fillHoles(S) {
  const P = [...S].map(unkey);
  const x0 = Math.min(...P.map((p) => p[0])) - 1, x1 = Math.max(...P.map((p) => p[0])) + 1;
  const y0 = Math.min(...P.map((p) => p[1])) - 1, y1 = Math.max(...P.map((p) => p[1])) + 1;
  const seen = new Set(), st = [];
  for (let y = y0; y <= y1; y++) { st.push([x0, y]); }
  while (st.length > 0) {
    const [x, y] = st.pop();
    const k = key(x, y);
    if ( seen.has(k) || S.has(k) || (x < x0) || (x > x1) || (y < y0) || (y > y1) ) { continue; }
    seen.add(k);
    for (let a = -1; a <= 1; a++) { for (let b = -1; b <= 1; b++) { st.push([x + a, y + b]); } }
  }
  const out = new Set(S);
  for (let x = x0; x <= x1; x++) {
    for (let y = y0; y <= y1; y++) {
      const k = key(x, y);
      if ( (!S.has(k)) && (!seen.has(k)) ) { out.add(k); }
    }
  }
  return out;
}

const colour = (x, y) => (((x + y) % 2) + 2) % 2;

function convexCorner(S, x, y) {
  const n = [[x + 1, y], [x - 1, y], [x, y + 1], [x, y - 1]].filter(([a, b]) => S.has(key(a, b)));
  if (n.length !== 2) { return false; }
  const [[ax, ay], [bx, by]] = n;
  if ( (ax === bx) || (ay === by) ) { return false; }
  return S.has(key(ax + bx - x, ay + by - y));
}

function sameSet(A, B) {
  if (A.size !== B.size) { return false; }
  for (const k of A) { if (!B.has(k)) { return false; } }
  return true;
}

function balance(S, rng) {
  S = new Set(S);
  for (let it = 0; it < 40; it++) {
    let blk = 0;
    for (const kk of S) { const [x, y] = unkey(kk); if (colour(x, y) === 0) { blk++; } }
    const wht = S.size - blk;
    if (Math.abs(blk - wht) <= 1) { return S; }
    const maj = ( (blk > wht) ? 0 : 1 );
    const cand = [...S].filter((kk) => { const [x, y] = unkey(kk); return (colour(x, y) === maj) && convexCorner(S, x, y); });
    for (let i = cand.length - 1; i > 0; i--) { const j = Math.floor(rng() * (i + 1)); [cand[i], cand[j]] = [cand[j], cand[i]]; }
    let done = false;
    for (const kk of cand) {
      const S2 = new Set(S);
      S2.delete(kk);
      if ( sameSet(open2(S2), S2) && connected(S2) ) { S = S2; done = true; break; }
    }
    if (!done) { return null; }
  }
  return null;
}

// A random solid shape of about n points (arms at least `wmin` wide), as an array of [x, y].
//
export function stamp(n, rng = Math.random, wmin = 2, tries = 200) {
  const m = Math.round(1.2 * Math.sqrt(n)) + 1;
  for (let t = 0; t < tries; t++) {
    let S = new Set();
    while (S.size < n) {
      const S2 = place(S, orient(template(rng, m, wmin), rng), rng);
      if (S2.size === S.size) { break; }
      S = S2;
    }
    S = fillHoles(open2(S));
    if (!connected(S)) { continue; }
    S = balance(S, rng);
    if (S === null) { continue; }
    S = fillHoles(S);
    if ( sameSet(open2(S), S) && connected(S) && (S.size <= (1.25 * n)) ) {
      const P = [...S].map(unkey);
      const mx = Math.min(...P.map((p) => p[0])), my = Math.min(...P.map((p) => p[1]));
      return P.map(([x, y]) => [x - mx, y - my]);
    }
  }
  return null;
}

// Endpoints whose colours allow a Hamiltonian path (Lean `dST` colour condition), uniform at
// random. With |V| even the two colours must have equal counts, s is any point and t any point
// of the other colour. With |V| odd both endpoints have the colour that has one point more, and
// (s, t) is a uniform pair of distinct points of that colour. Returns null when the counts allow
// no Hamiltonian path.
//
export function pickEndpoints(V, rng = Math.random) {
  const black = V.filter(([x, y]) => (colour(x, y) === 0));
  const white = V.filter(([x, y]) => (colour(x, y) === 1));
  const pick = (A) => A[Math.floor(rng() * A.length)];
  if ((V.length % 2) === 0) {
    if ( (black.length !== white.length) || (black.length === 0) ) { return null; }
    const s = pick(V);
    const t = pick( (colour(...s) === 0) ? white : black );
    return [s, t];
  }
  const maj = ( (black.length === (white.length + 1)) ? black :
                ( (white.length === (black.length + 1)) ? white : null ) );
  if ( (maj === null) || (maj.length < 2) ) { return null; }
  const i = Math.floor(rng() * maj.length);
  let j = Math.floor(rng() * (maj.length - 1));
  if (j >= i) { j++; }
  return [maj[i], maj[j]];
}
