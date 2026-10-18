// SPDX-License-Identifier: CC0-1.0
//
// JavaScript port of the fast mode of `decideHamPath` (lib/python/hpst_fast.py; Lean
// lean/ULHC/HP/Sheffield/HPFinal.lean). Same algorithm, same answer-preserving speedups
// (S1-S8, justified in hpst_fast.py), same iteration orders, so with the heuristic off this
// port returns the same path as the Python fast mode.
//
// ES module, no dependencies. Node: `import { solve } from './hpst.js'` (or `require` on
// Node >= 22.12, which loads ES modules). Browser: `<script type="module">`.
//
//   solve(points, s, t, options) -> { answer: 'yes' | 'no', path: [[x, y], ...] | null, stats }
//
// points: array of [x, y]; s, t: [x, y]. options: { heuristic (true), order ('abs' | 'lean'),
// prune (true), memo (true), timeBox (seconds, default min(2, 0.05 + 0.002 |V|)) }.
// `solve` does not test solidity (`decideHamPath_main` assumes `Solid V`); call `isSolid` first.
//
// Python dicts and sets of points are typed arrays indexed by point id here (S1); small sets
// of cells (pairSq, brSq) and the memo are JS Sets.
//

// Sides: b, t, l, r (Algorithm.lean `sidesL` order).
//
const SB = 0, ST = 1, SL = 2, SR = 3;
const OPP = [ST, SB, SR, SL];

const now = ( ((typeof performance !== 'undefined') && performance.now) ?
              (() => performance.now() / 1000) :
              (() => Date.now() / 1000) );

class Stats {
  constructor() {
    this.c = new Map();
    this.t = new Map();
  }

  inc(k, n = 1) { this.c.set(k, (this.c.get(k) || 0) + n); }

  addTime(k, dt) { this.t.set(k, (this.t.get(k) || 0) + dt); }
}

// ---------------------------------------------------------------------------------------------
// The grid context: point id = (x - x0) + (y - y0) * Wd over V's box with margin 3. Edge id =
// 2 * p + d (d = 0: `.h`, to p + 1; d = 1: `.v`, to p + Wd). Cell id = id of its lower-left
// corner.
// ---------------------------------------------------------------------------------------------

class Ctx {
  constructor(V) {
    let xmin = Infinity, xmax = -Infinity, ymin = Infinity, ymax = -Infinity;
    for (const p of V) {
      if (p[0] < xmin) { xmin = p[0]; }
      if (p[0] > xmax) { xmax = p[0]; }
      if (p[1] < ymin) { ymin = p[1]; }
      if (p[1] > ymax) { ymax = p[1]; }
    }
    const m = 3;
    this.x0 = xmin - m;
    this.y0 = ymin - m;
    this.Wd = xmax - xmin + 1 + (2 * m);
    this.Hd = ymax - ymin + 1 + (2 * m);
    this.N  = this.Wd * this.Hd;
    const Wd = this.Wd, N = this.N;
    this.par    = new Uint8Array(N);
    this.lexkey = new Int32Array(N);
    for (let i = 0; i < N; i++) {
      const x = (i % Wd), y = Math.floor(i / Wd);
      this.par[i]    = ( (x + this.x0 + y + this.y0) & 1 );
      this.lexkey[i] = (x * this.Hd) + y;
    }
    this.step = [-Wd, Wd, -1, 1];
    const ids = [];
    for (const p of V) { ids.push(this.pid(p)); }
    ids.sort((a, b) => (this.lexkey[a] - this.lexkey[b]));
    this.Vids = ids;

    // Scratch stamp array for BFS "seen" marks (generation counter, no clearing).
    //
    this.mark = new Int32Array(N);
    this.gen  = 0;
  }

  newGen() {
    this.gen++;
    if (this.gen > 2000000000) {
      this.mark.fill(0);
      this.gen = 1;
    }
    return this.gen;
  }

  pid(p) { return (p[0] - this.x0) + ((p[1] - this.y0) * this.Wd); }

  pt(i) { return [(i % this.Wd) + this.x0, Math.floor(i / this.Wd) + this.y0]; }

  eR(p) { return 2 * p; }
  eL(p) { return 2 * (p - 1); }
  eU(p) { return (2 * p) + 1; }
  eD(p) { return (2 * (p - this.Wd)) + 1; }

  inc4(p) { return [2 * p, 2 * (p - 1), (2 * p) + 1, (2 * (p - this.Wd)) + 1]; }

  nbrs4(p) { return [p + 1, p - 1, p + this.Wd, p - this.Wd]; }

  eq(e) {
    const p = e >> 1;
    return ( ((e & 1) === 0) ? (p + 1) : (p + this.Wd) );
  }

  other(e, y) {
    const p = e >> 1;
    return ( (p === y) ? this.eq(e) : p );
  }

  lo(e) {
    const p = e >> 1;
    return ( ((e & 1) === 0) ? (p - this.Wd) : (p - 1) );
  }

  sideEdge(c, s) {
    if      (s === SB) { return 2 * c; }
    else if (s === ST) { return 2 * (c + this.Wd); }
    else if (s === SL) { return (2 * c) + 1; }
    else               { return (2 * (c + 1)) + 1; }
  }

  cellE(c) {
    const Wd = this.Wd;
    return [2 * c, 2 * (c + Wd), (2 * c) + 1, (2 * (c + 1)) + 1];
  }

  back1(c, s) {
    if      (s === ST) { return c; }
    else if (s === SB) { return c + this.Wd; }
    else if (s === SR) { return c; }
    else               { return c + 1; }
  }

  back2(c, s) {
    if      (s === ST) { return c + 1; }
    else if (s === SB) { return c + this.Wd + 1; }
    else if (s === SR) { return c + this.Wd; }
    else               { return c + this.Wd + 1; }
  }

  front1(c, s) {
    if      (s === ST) { return c + this.Wd; }
    else if (s === SB) { return c; }
    else if (s === SR) { return c + 1; }
    else               { return c; }
  }

  front2(c, s) {
    if      (s === ST) { return c + this.Wd + 1; }
    else if (s === SB) { return c + 1; }
    else if (s === SR) { return c + this.Wd + 1; }
    else               { return c + this.Wd; }
  }

  isCell(inU, c) {
    const Wd = this.Wd;
    return ( (inU[c] === 1) && (inU[c + 1] === 1) && (inU[c + Wd] === 1) &&
             (inU[c + Wd + 1] === 1) );
  }
}

// ---------------------------------------------------------------------------------------------
// Arcs (Arcs.lean) on edge arrays.
// ---------------------------------------------------------------------------------------------

function up(cx, H, e) {
  const ine1 = ( ((e & 1) === 0) ? (H[e] === 1) : (H[e] !== 1) );
  return ( (cx.par[cx.lo(e)] === 1) === ine1 );
}

function outArc(cx, H, c, s) {
  const e = cx.sideEdge(c, s);
  if ( (s === SB) || (s === SL) ) { return !up(cx, H, e); }
  return up(cx, H, e);
}

function alt(cx, H, c) {
  const Wd = cx.Wd;
  const b = H[2 * c], t = H[2 * (c + Wd)], l = H[(2 * c) + 1], r = H[(2 * (c + 1)) + 1];
  return ( ( (b === 1) && (t === 1) && (l !== 1) && (r !== 1) ) ||
           ( (b !== 1) && (t !== 1) && (l === 1) && (r === 1) ) );
}

function flip(cx, H, c) {
  const Wd = cx.Wd;
  H[2 * c]             ^= 1;
  H[2 * (c + Wd)]      ^= 1;
  H[(2 * c) + 1]       ^= 1;
  H[(2 * (c + 1)) + 1] ^= 1;
}

// ---------------------------------------------------------------------------------------------
// S6: necessary conditions for a Hamiltonian a-b path in the grid graph on U (see
// hpst_fast.py `nec` for the justification).
// ---------------------------------------------------------------------------------------------

function nec(cx, inU, Ul, a, b) {
  const n = Ul.length;
  if ( (inU[a] !== 1) || (inU[b] !== 1) || (a === b) ) { return false; }
  if (n === 2) { return cx.nbrs4(a).includes(b); }
  let blk = 0;
  for (const p of Ul) {
    if (cx.par[p] === 0) { blk++; }
  }
  const wht = n - blk;
  const ca = cx.par[a], cb = cx.par[b];
  if ((n % 2) === 0) {
    if ( (ca === cb) || (blk !== wht) ) { return false; }
  }
  else {
    if (ca !== cb) { return false; }
    if ( (ca === 0) && (blk !== (wht + 1)) ) { return false; }
    if ( (ca === 1) && (wht !== (blk + 1)) ) { return false; }
  }
  const Wd = cx.Wd;
  for (const p of Ul) {
    const k = inU[p + 1] + inU[p - 1] + inU[p + Wd] + inU[p - Wd];
    if (k < ( ((p === a) || (p === b)) ? 1 : 2 )) { return false; }
  }
  return biconnectedPlus(cx, inU, Ul, a, b);
}

// Tarjan (iterative): is the graph on U plus the edge a-b 2-connected?
//
function biconnectedPlus(cx, inU, Ul, a, b) {
  const disc = new Int32Array(cx.N).fill(-1);
  const low  = new Int32Array(cx.N);
  const root = Ul[0];

  const nb = (u) => {
    const out = [];
    for (const v of cx.nbrs4(u)) {
      if (inU[v] === 1) { out.push(v); }
    }
    if      ( (u === a) && (!out.includes(b)) ) { out.push(b); }
    else if ( (u === b) && (!out.includes(a)) ) { out.push(a); }
    return out;
  };

  disc[root] = 0;
  low[root]  = 0;
  let cnt = 1, rootkids = 0;

  // Stack frames: vertex, parent, neighbour list, next index.
  //
  const sU = [root], sP = [-1], sL = [nb(root)], sI = [0];
  while (sU.length > 0) {
    const top = sU.length - 1;
    const u = sU[top], par = sP[top], L = sL[top];
    let adv = false;
    while (sI[top] < L.length) {
      const v = L[sI[top]];
      sI[top]++;
      if (disc[v] < 0) {
        disc[v] = cnt;
        low[v]  = cnt;
        cnt++;
        sU.push(v);
        sP.push(u);
        sL.push(nb(v));
        sI.push(0);
        adv = true;
        break;
      }
      else if (v !== par) {
        if (disc[v] < low[u]) { low[u] = disc[v]; }
      }
    }
    if (adv) { continue; }
    sU.pop();
    sP.pop();
    sL.pop();
    sI.pop();
    if (par >= 0) {
      if (low[u] < low[par]) { low[par] = low[u]; }
      if      (par === root)          { rootkids++; }
      else if (low[u] >= disc[par])   { return false; }
    }
  }
  if (cnt !== Ul.length) { return false; }
  return ( rootkids <= 1 );
}

// ---------------------------------------------------------------------------------------------
// S3: findFactor (DFactor.lean) with the layers as BFS distances; S3b warm start when `warm`.
// Justifications: hpst_fast.py `findFactor`.
// ---------------------------------------------------------------------------------------------

function findFactor(cx, inU, Ul, s, t, stats, warm) {
  stats.inc('findFactor');
  const N = cx.N;
  const F    = new Uint8Array(2 * N);
  const degA = new Int32Array(N);
  const dist = new Int32Array(N).fill(-1);
  const n = Ul.length;

  const dd     = (z) => ( ((z === s) || (z === t)) ? 1 : 2 );
  const isEdge = (e) => ( (inU[e >> 1] === 1) && (inU[cx.eq(e)] === 1) );

  if (warm) {
    for (const z of Ul) {
      for (const e of [cx.eR(z), cx.eU(z)]) {
        if (isEdge(e)) {
          const q = cx.eq(e);
          if ( (degA[z] < dd(z)) && (degA[q] < dd(q)) ) {
            F[e] = 1;
            degA[z]++;
            degA[q]++;
          }
        }
      }
    }
  }

  let reached = [];
  for (let it = 0; it < (n + 1); it++) {
    for (const z of reached) { dist[z] = -1; }
    reached = [];
    let fr = [];
    for (const z of Ul) {
      if ( (cx.par[z] === 0) && (degA[z] < dd(z)) ) {
        fr.push(z);
        dist[z] = 0;
        reached.push(z);
      }
    }
    let k = 0;
    while ( (fr.length > 0) && (k < n) ) {
      const nf = [];
      for (const u of fr) {
        const blk = (cx.par[u] === 0);
        for (const e of cx.inc4(u)) {
          if ( isEdge(e) && ( blk ? (F[e] === 0) : (F[e] === 1) ) ) {
            const v = cx.other(e, u);
            if (dist[v] < 0) {
              dist[v] = k + 1;
              nf.push(v);
              reached.push(v);
            }
          }
        }
      }
      fr = nf;
      k++;
    }
    let w = -1;
    for (const z of reached) {
      if ( (cx.par[z] === 1) && (degA[z] < dd(z)) ) {
        if ( (w < 0) || (cx.lexkey[z] < cx.lexkey[w]) ) { w = z; }
      }
    }
    if (w < 0) { break; }
    const F0 = F.slice();
    let v = w;
    k = n - 1;
    while (k >= 0) {
      const dv = dist[v];
      if (dv <= k) {
        k = dv - 1;
        continue;
      }
      const blk = (cx.par[v] === 0);
      let ee = -1;
      for (const e of cx.inc4(v)) {
        if (isEdge(e)) {
          const o = cx.other(e, v);
          const dO = dist[o];
          if ( (dO >= 0) && (dO <= k) && ( blk ? (F0[e] === 1) : (F0[e] !== 1) ) ) {
            ee = e;
            break;
          }
        }
      }
      if (ee < 0) { break; }
      const want = ( blk ? 0 : 1 );
      if (F[ee] !== want) {
        F[ee] = want;
        const dlt = ( want ? 1 : -1 );
        degA[ee >> 1]   += dlt;
        degA[cx.eq(ee)] += dlt;
      }
      v = cx.other(ee, v);
      k--;
    }
  }
  for (const z of Ul) {
    if (degA[z] !== dd(z)) { return null; }
  }
  return F;
}

// ---------------------------------------------------------------------------------------------
// The phase and the loop (SAlg.lean, SPhaseAlg.lean, SheffComp.lean, TwoPhS4.lean), with S2:
// one component labelling per factor state. A bridge is [q, a, len]; a phase outcome is
// { kind: 'fuel' | 'stuck' | 'merge' | 'odd' | 'twist', c, b }.
// ---------------------------------------------------------------------------------------------

class Run {
  constructor(cx, inU, Ul, p, q, stats) {
    this.cx  = cx;
    this.inU = inU;
    this.Wl  = Ul.concat([p, q]);
    this.nU  = Ul.length;
    this.cells   = [];
    this.cellset = new Uint8Array(cx.N);
    for (const c of Ul) {
      if (cx.isCell(inU, c)) {
        this.cells.push(c);
        this.cellset[c] = 1;
      }
    }
    this.stats   = stats;
    this.lab     = new Int32Array(cx.N).fill(-1);
    this.labeled = [];
  }

  labels(H) {
    const cx = this.cx, lab = this.lab;
    for (const x of this.labeled) { lab[x] = -1; }
    const labeled = [];
    let k = 0;
    for (const x of this.Wl) {
      if (lab[x] >= 0) { continue; }
      lab[x] = k;
      labeled.push(x);
      const st = [x];
      while (st.length > 0) {
        const u = st.pop();
        for (const e of cx.inc4(u)) {
          if (H[e] === 1) {
            const v = cx.other(e, u);
            if (lab[v] < 0) {
              lab[v] = k;
              labeled.push(v);
              st.push(v);
            }
          }
        }
      }
      k++;
    }
    this.labeled = labeled;
    return k;
  }

  conn(x, y) {
    if (x === y) { return true; }
    const a = this.lab[x];
    return ( (a >= 0) && (a === this.lab[y]) );
  }

  cut(c) {
    const Wd = this.cx.Wd;
    return !( this.conn(c, c + 1) && this.conn(c, c + Wd + 1) && this.conn(c, c + Wd) );
  }

  critB(H, q, a) {
    const cx = this.cx;
    const b1 = cx.back1(q, a), b2 = cx.back2(q, a), f1 = cx.front1(q, a), f2 = cx.front2(q, a);
    return ( this.conn(b1, b2) && this.conn(f1, f2) && (!this.conn(b1, f1)) &&
             (H[cx.sideEdge(q, OPP[a])] === 1) && (H[cx.sideEdge(q, a)] !== 1) );
  }

  // Connectivity in a modified state (no labelling): DFS with early exit.
  //
  bfsConn(H, x, y) {
    if (x === y) { return true; }
    const cx = this.cx, mark = cx.mark, g = cx.newGen();
    mark[x] = g;
    const st = [x];
    while (st.length > 0) {
      const u = st.pop();
      for (const e of cx.inc4(u)) {
        if (H[e] === 1) {
          const v = cx.other(e, u);
          if (v === y) { return true; }
          if (mark[v] !== g) {
            mark[v] = g;
            st.push(v);
          }
        }
      }
    }
    return false;
  }

  // SAlg.lean `scan`: returns j > 0 for ('row', j), -j for ('stuck', j), 0 for none.
  //
  scan(H, q, a) {
    const cx = this.cx;
    const o  = outArc(cx, H, q, a);
    const st = cx.step[a];
    let j = 1, fuel = this.nU + 1;
    while (fuel > 0) {
      if (outArc(cx, H, q + ((j - 1) * st), a) !== o) { return j; }
      const c = q + (j * st);
      if ( (this.cellset[c] !== 1) || this.cut(c) ) { return -j; }
      fuel--;
      j++;
    }
    return 0;
  }

  bcell(b, j) { return b[0] + (j * this.cx.step[b[1]]); }

  bE(b) { return this.bcell(b, b[2] - 1); }

  // SPhaseAlg.lean `phase`. H is modified in place; returns [BS, out].
  //
  phase(n, H) {
    const cx = this.cx;
    this.stats.inc('phases');
    const BS = [];
    const pairSq = new Set(), brSq = new Set();
    this.labels(H);
    for (;;) {
      if (n === 0) { return [BS, { kind: 'fuel' }]; }
      let mc = -1;
      for (const c of this.cells) {
        if ( alt(cx, H, c) && this.cut(c) && (!pairSq.has(c)) ) {
          mc = c;
          break;
        }
      }
      if (mc >= 0) { return [BS, { kind: 'merge', c: mc }]; }
      let b = null;
      for (const q of this.cells) {
        if (brSq.has(q)) { continue; }
        for (const a of [SB, ST, SL, SR]) {
          if (this.critB(H, q, a)) {
            const e = this.scan(H, q, a);
            if (e > 0) {
              b = [q, a, e];
              break;
            }
          }
        }
        if (b !== null) { break; }
      }
      if (b === null) { return [BS, { kind: 'stuck' }]; }
      if ((b[2] % 2) === 1) { return [BS, { kind: 'odd', b: b }]; }
      const E = this.bE(b);
      flip(cx, H, E);
      if (!this.bfsConn(H, cx.back1(E, b[1]), cx.front1(E, b[1]))) {
        this.stats.inc('bridges');
        BS.unshift(b);
        pairSq.add(this.bcell(b, b[2] - 2));
        pairSq.add(E);
        for (let j = 0; j < b[2]; j++) { brSq.add(this.bcell(b, j)); }
        this.labels(H);
        n--;
      }
      else {
        flip(cx, H, E);
        return [BS, { kind: 'twist', b: b }];
      }
    }
  }

  // SheffComp.lean `planAB` on a copy of H.
  //
  planAB(H, BS, uv) {
    const cx = this.cx;
    const Hc = H.slice();
    const out = [];
    for (const b of BS) {
      flip(cx, Hc, this.bE(b));
      if (this.bfsConn(Hc, uv[0], uv[1])) {
        out.push(true);
        uv = [cx.back1(b[0], b[1]), cx.front1(b[0], b[1])];
      }
      else {
        out.push(false);
      }
    }
    return out;
  }

  mergePair(H, X) {
    const a = ( (H[2 * X] === 1) ? ST : SR );
    return [a, [this.cx.back1(X, a), this.cx.front1(X, a)]];
  }

  // SheffComp.lean `goodB`; the plan is computed only when some bridge needs it (same value).
  //
  goodB(H, BS, pairSq, X) {
    const cx = this.cx;
    if (!( alt(cx, H, X) && this.cut(X) && (!pairSq.has(X)) )) { return false; }
    const need = [];
    for (let i = 0; i < BS.length; i++) {
      const b = BS[i];
      if (X === (this.bE(b) + cx.step[b[1]])) { need.push(i); }
    }
    if (need.length === 0) { return true; }
    const plan = this.planAB(H, BS, this.mergePair(H, X)[1]);
    return need.every((i) => plan[i]);
  }

  // SheffComp.lean `reduceOutC`; H is consumed.
  //
  reduceOutC(H, BS, out) {
    const cx = this.cx;
    this.stats.inc('reductions');
    let uv, first;
    if (out.kind === 'merge') {
      const pairSq = new Set();
      for (const b of BS) {
        pairSq.add(this.bcell(b, b[2] - 2));
        pairSq.add(this.bE(b));
      }
      let X = out.c;
      for (const Y of this.cells) {
        if (this.goodB(H, BS, pairSq, Y)) {
          X = Y;
          break;
        }
      }
      uv    = this.mergePair(H, X)[1];
      first = [X, 0, 1];
    }
    else {
      const b = out.b;
      uv    = [cx.back1(b[0], b[1]), cx.front1(b[0], b[1])];
      first = [b[0], b[1], b[2]];
    }
    const plan = this.planAB(H, BS, uv);
    const ops = [first];
    for (let i = 0; i < BS.length; i++) {
      const b = BS[i];
      ops.push( plan[i] ? [b[0], b[1], b[2] - 1] : [this.bE(b), b[1], 1] );
    }
    for (const op of ops) {
      const st = cx.step[op[1]];
      for (let j = 0; j < op[2]; j++) { flip(cx, H, op[0] + (j * st)); }
    }
    return H;
  }

  // TwoPhS4.lean `runSC2`. Returns the final factor or null.
  //
  runSC2(n, G) {
    this.stats.inc('runSC2');
    let H = G;
    const nW = this.Wl.length;
    for (;;) {
      if (this.labels(H) === 1) { return H; }
      if (n === 0) { return null; }
      const r = this.phase(nW + 1, H);
      const BS = r[0], out = r[1];
      if ( (out.kind === 'stuck') || (out.kind === 'fuel') ) {
        this.stats.inc('runs_stuck');
        return null;
      }
      H = this.reduceOutC(H, BS, out);
      n--;
    }
  }
}

function factorPath(cx, F, s, t, drop) {
  for (const e of drop) { F[e] = 0; }
  const path = [s];
  let prev = -1, cur = s;
  while (cur !== t) {
    let nxt = -1, cnt = 0;
    for (const e of cx.inc4(cur)) {
      if (F[e] === 1) {
        const v = cx.other(e, cur);
        if (v !== prev) {
          nxt = v;
          cnt++;
        }
      }
    }
    if (cnt !== 1) { throw new Error("factorPath: not a path"); }
    prev = cur;
    cur  = nxt;
    path.push(cur);
  }
  for (const e of drop) { F[e] = 1; }
  return path;
}

// ---------------------------------------------------------------------------------------------
// S4: class search (HoleRelax.lean / HoleTry.lean); `classPotential` by a bucket longest-path
// computation (Dial's algorithm, weights 0 / -1). Justification: hpst_fast.py S4.
// The potential f is an Int32Array over all ids, 0 outside boxSquares (Lean: cells outside boxSquares are 0).
// ---------------------------------------------------------------------------------------------

function box(cx, Ul) {
  const Wd = cx.Wd;
  let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
  for (const p of Ul) {
    const x = p % Wd, y = Math.floor(p / Wd);
    if (x < x0) { x0 = x; }
    if (x > x1) { x1 = x; }
    if (y < y0) { y0 = y; }
    if (y > y1) { y1 = y; }
  }
  return [x0, x1, y0, y1];
}

// `boxSquares`, x-major; with a membership mask.
//
function boxSquares(cx, Ul) {
  const bx = box(cx, Ul);
  const S = [];
  const inS = new Uint8Array(cx.N);
  for (let i = 0; i < (bx[1] - bx[0]); i++) {
    for (let j = 0; j < (bx[3] - bx[2]); j++) {
      const c = (bx[0] + i) + ((bx[2] + j) * cx.Wd);
      S.push(c);
      inS[c] = 1;
    }
  }
  return { S: S, inS: inS, W: (bx[1] - bx[0]) };
}

function sv(cx, F, e) { return ( up(cx, F, e) ? 1 : -1 ); }

// Weight of the lowerBound term of cell s whose source cell is s - Wd (k = 0, edge 2s), s - 1
// (k = 1, edge 2s + 1), s + Wd (k = 2, edge 2(s + Wd)), s + 1 (k = 3, edge 2(s + 1) + 1).
//
function termW(cx, inU, F, e, below) {
  if ( (inU[e >> 1] === 1) && (inU[cx.eq(e)] === 1) ) {
    const v = sv(cx, F, e);
    return ( below ? Math.min(0, v) : -Math.max(0, v) );
  }
  return 0;
}

function kPotFast(cx, inU, K, F, as, hs) {
  const S = K.S, inS = K.inS, W = K.W, Wd = cx.Wd;
  const f = new Int32Array(cx.N);
  const look = new Map();
  for (let i = 0; i < as.length; i++) {
    if (!look.has(as[i])) { look.set(as[i], hs[i]); }
  }
  for (const s of S) { f[s] = ( look.has(s) ? look.get(s) : -W ); }

  // The four terms of s: [source cell, edge, below].
  //
  const terms = (s) => [ [s - Wd, 2 * s, true], [s - 1, (2 * s) + 1, true],
                         [s + Wd, 2 * (s + Wd), false], [s + 1, (2 * (s + 1)) + 1, false] ];

  // Cells outside S are fixed at 0 and act as sources.
  //
  for (const s of S) {
    for (const tm of terms(s)) {
      if (inS[tm[0]] !== 1) {
        const w = termW(cx, inU, F, tm[1], tm[2]);
        if (w > f[s]) { f[s] = w; }
      }
    }
  }

  // Dial's algorithm, largest value first. Values stay in [lo, hi]: they only increase from
  // the initial values, and a pushed value v + w (w <= 0) is pushed only when above f.
  //
  let lo = Infinity, hi = -Infinity;
  for (const s of S) {
    if (f[s] < lo) { lo = f[s]; }
    if (f[s] > hi) { hi = f[s]; }
  }
  if (S.length === 0) { return f; }
  const buckets = [];
  for (let v = lo; v <= hi; v++) { buckets.push([]); }
  for (const s of S) { buckets[f[s] - lo].push(s); }
  const done = new Uint8Array(cx.N);
  for (let v = hi; v >= lo; v--) {
    const lst = buckets[v - lo];
    for (let i = 0; i < lst.length; i++) {
      const s = lst[i];
      if ( (done[s] === 1) || (f[s] !== v) ) { continue; }
      done[s] = 1;

      // Terms (s, w) of the cells s2 next to s: s2 = s + Wd has source s by its edge 2 s2
      // (below), s2 = s + 1 by 2 s2 + 1 (below), s2 = s - Wd by 2 s (above), s2 = s - 1 by
      // 2 s + 1 (above).
      //
      const nb = [ [s + Wd, 2 * (s + Wd), true], [s + 1, (2 * (s + 1)) + 1, true],
                   [s - Wd, 2 * s, false], [s - 1, (2 * s) + 1, false] ];
      for (const x of nb) {
        const s2 = x[0];
        if ( (inS[s2] !== 1) || (done[s2] === 1) ) { continue; }
        const w = termW(cx, inU, F, x[1], x[2]);
        if ((v + w) > f[s2]) {
          f[s2] = v + w;
          buckets[(v + w) - lo].push(s2);
        }
      }
    }
  }
  return f;
}

function kCheckFast(cx, inU, S, F, f, as, hs) {
  const Wd = cx.Wd;
  for (const s of S) {
    for (const e of [2 * s, (2 * s) + 1, 2 * (s + Wd), (2 * (s + 1)) + 1]) {
      const dlt = f[e >> 1] - f[cx.lo(e)];
      if (dlt !== 0) {
        if (!( (inU[e >> 1] === 1) && (inU[cx.eq(e)] === 1) && (dlt === sv(cx, F, e)) )) {
          return false;
        }
      }
    }
  }
  for (let i = 0; i < as.length; i++) {
    if (f[as[i]] !== hs[i]) { return false; }
  }
  return true;
}

function kFindFast(cx, inU, K, F, as, hs, stats) {
  stats.inc('classSearch');
  const f = kPotFast(cx, inU, K, F, as, hs);
  const S = K.S;
  if (!kCheckFast(cx, inU, S, F, f, as, hs)) { return null; }
  stats.inc('classSearch_some');
  const G = F.slice();
  const Wd = cx.Wd;
  const seen = new Uint8Array(2 * cx.N);
  for (const s of S) {
    for (const e of [2 * s, (2 * s) + 1, 2 * (s + Wd), (2 * (s + 1)) + 1]) {
      if (seen[e] === 1) { continue; }
      seen[e] = 1;
      const p = e >> 1;
      if ( (inU[p] === 1) && (inU[cx.eq(e)] === 1) && (f[p] !== f[cx.lo(e)]) ) { G[e] ^= 1; }
    }
  }
  return G;
}

// ---------------------------------------------------------------------------------------------
// The solver: walks (TwoPhWalk.lean, HoleWalk.lean) and final tests, on a mutable set U.
// A walk returns a path (array of ids) or null.
// ---------------------------------------------------------------------------------------------

class Solver {
  constructor(V, order = 'abs', prune = true, memo = true) {
    this.cx = new Ctx(V);
    const cx = this.cx;
    this.inU = new Uint8Array(cx.N);
    for (const p of cx.Vids) { this.inU[p] = 1; }
    this.cnt     = cx.Vids.length;
    this.deleted = [];
    this.order   = order;

    // Lean fuels: `boundaryEndpoints` calls `boundaryEndpointsWalk` with 12, `holeCase` calls `holeCaseWalk` with 10.
    //
    this.fuelA = 12;
    this.fuelG = 10;
    this.prune = prune;
    this.memo  = memo;
    this.fail  = new Set();
    this.stats = new Stats();
  }

  Ul() {
    const inU = this.inU, out = [];
    for (const p of this.cx.Vids) {
      if (inU[p] === 1) { out.push(p); }
    }
    return out;
  }

  del(p) {
    this.inU[p] = 0;
    this.cnt--;
    this.deleted.push(p);
  }

  restore(p) {
    this.inU[p] = 1;
    this.cnt++;
    this.deleted.pop();
  }

  key(a, b) {
    const d = this.deleted.slice().sort((x, y) => (x - y));
    return d.join(',') + '|' + Math.min(a, b) + ',' + Math.max(a, b);
  }

  // S6 + S7: may the subproblem (current U, a, b) have a Hamiltonian path?
  //
  viable(a, b) {
    if ( this.memo && this.fail.has(this.key(a, b)) ) {
      this.stats.inc('memo_hits');
      return false;
    }
    if (this.prune) {
      const t0 = now();
      const ok = nec(this.cx, this.inU, this.Ul(), a, b);
      this.stats.addTime('prune', now() - t0);
      if (!ok) {
        this.stats.inc('pruned');
        return false;
      }
    }
    return true;
  }

  failed(a, b) {
    if (this.memo) { this.fail.add(this.key(a, b)); }
  }

  // TwoPhWalk.lean `isFar`: equal or king distance >= 2.
  //
  isFar(t, s) {
    const Wd = this.cx.Wd;
    const dx = Math.abs((t % Wd) - (s % Wd));
    const dy = Math.abs(Math.floor(t / Wd) - Math.floor(s / Wd));
    return ( (t === s) || (!( (dx <= 1) && (dy <= 1) )) );
  }

  // TwoPhWalk.lean `phantomsOpposed` (StuckL4.lean `Opp`) on ids.
  //
  phantomsOpposed(a, ma, b, mb) {
    const Wd = this.cx.Wd;
    const dx = (b % Wd) - (a % Wd);
    const dy = Math.floor(b / Wd) - Math.floor(a / Wd);
    return ( ( (dx === 2)  && (Math.abs(dy) <= 2) && (ma === (a - 1))  && (mb === (b + 1)) ) ||
             ( (dx === -2) && (Math.abs(dy) <= 2) && (ma === (a + 1))  && (mb === (b - 1)) ) ||
             ( (dy === 2)  && (Math.abs(dx) <= 2) && (ma === (a - Wd)) && (mb === (b + Wd)) ) ||
             ( (dy === -2) && (Math.abs(dx) <= 2) && (ma === (a + Wd)) && (mb === (b - Wd)) ) );
  }

  // TwoPhWalk.lean `isUsablePhantom`.
  //
  isUsablePhantom(s, q, t, x) {
    return ( (this.inU[x[0]] !== 1) && (x[0] !== q) && (!this.phantomsOpposed(t, x[0], s, q)) );
  }

  nbrsL(t) {
    const cx = this.cx;
    return [ [t + 1, cx.eR(t)], [t - 1, cx.eL(t)], [t + cx.Wd, cx.eU(t)], [t - cx.Wd, cx.eD(t)] ];
  }

  two(t, s) {
    for (const x of this.nbrsL(t)) {
      if (x[0] === s) { return [s, t]; }
    }
    return null;
  }

  // TwoPhS4.lean `hpSheffC2` (final test of boundaryEndpoints).
  //
  hpSheffC2(s, t, p, q, e0, e1) {
    const st = this.stats;
    st.inc('final_tests');
    const Ul = this.Ul();
    let t0 = now();
    const R = findFactor(this.cx, this.inU, Ul, s, t, st, (this.order !== 'lean'));
    st.addTime('findFactor', now() - t0);
    let res = null;
    if (R !== null) {
      R[e0] = 1;
      R[e1] = 1;
      t0 = now();
      const G = (new Run(this.cx, this.inU, Ul, p, q, st)).runSC2(Ul.length + 2, R);
      st.addTime('loop', now() - t0);
      if (G !== null) { res = factorPath(this.cx, G, s, t, [e0, e1]); }
    }
    return res;
  }

  // S5: classes |h| <= boxWidth, by |h| ascending (order 'abs') or Lean's -|V| .. |V|.
  //
  classes(Ul) {
    const n = Ul.length;
    const bx = box(this.cx, Ul);
    const kw = bx[1] - bx[0];
    const hs = [];
    for (let i = 0; i < ((2 * n) + 1); i++) {
      const h = i - n;
      if (Math.abs(h) <= kw) { hs.push(h); }
    }
    if (this.order === 'abs') {
      hs.sort((a, b) => ( (Math.abs(a) !== Math.abs(b)) ? (Math.abs(a) - Math.abs(b)) : (a - b) ));
    }
    return hs;
  }

  // HoleWalk.lean `oneHoleFinalTest` / HoleTwoV.lean `twoHoleFinalTest` (r = null for one hole).
  //
  oneHoleFinalTest(s, w, t, r, q, e0, e1) {
    const cx = this.cx, st = this.stats;
    st.inc('final_tests');
    const Ul = this.Ul();
    let res = null;
    const bx = box(cx, Ul);
    const narrow = ( ((bx[1] - bx[0]) < Ul.length) && ((bx[3] - bx[2]) < Ul.length) );
    if (narrow) {
      let t0 = now();
      const R = findFactor(cx, this.inU, Ul, s, w, st, (this.order !== 'lean'));
      st.addTime('findFactor', now() - t0);
      if (R !== null) {
        R[e0] = 1;
        R[e1] = 1;
        const hs = this.classes(Ul);
        const cl = [];
        if (r === null) {
          for (const h of hs) { cl.push([[t], [h]]); }
        }
        else {
          for (const h1 of hs) {
            for (const h2 of hs) { cl.push([[t, r], [h1, h2]]); }
          }
          if (this.order === 'abs') {
            const key = (x) => (Math.abs(x[1][0]) + Math.abs(x[1][1]));
            cl.sort((a, b) => ( (key(a) !== key(b)) ? (key(a) - key(b)) :
                                ( (a[1][0] !== b[1][0]) ? (a[1][0] - b[1][0]) :
                                  (a[1][1] - b[1][1]) ) ));
          }
        }
        const K = boxSquares(cx, Ul);
        for (const c of cl) {
          t0 = now();
          const G = kFindFast(cx, this.inU, K, R, c[0], c[1], st);
          st.addTime('classes', now() - t0);
          if (G === null) { continue; }
          t0 = now();
          const G2 = (new Run(cx, this.inU, Ul, t, q, st)).runSC2(Ul.length + 2, G);
          st.addTime('loop', now() - t0);
          if (G2 !== null) {
            res = factorPath(cx, G2, s, w, [e0, e1]);
            break;
          }
        }
      }
    }
    return res;
  }

  // TwoPhWalk.lean `boundaryEndpointsWalk`.
  //
  boundaryEndpointsWalk(s, q, e1, n, t) {
    this.stats.inc('walk_nodes');
    if (n === 0) { return null; }
    if (this.cnt <= 2) { return this.two(t, s); }
    let x = null;
    for (const y of this.nbrsL(t)) {
      if (this.isUsablePhantom(s, q, t, y)) {
        x = y;
        break;
      }
    }
    if ( (x !== null) && this.isFar(t, s) ) { return this.hpSheffC2(s, t, x[0], q, x[1], e1); }
    for (const y of this.nbrsL(t)) {
      if ( (this.inU[y[0]] === 1) && (y[0] !== s) ) {
        this.del(t);
        let P = null;
        if (this.viable(s, y[0])) {
          P = this.boundaryEndpointsWalk(s, q, e1, n - 1, y[0]);
          if (P === null) { this.failed(s, y[0]); }
        }
        this.restore(t);
        if (P !== null) {
          P.push(t);
          return P;
        }
      }
    }
    return null;
  }

  // TwoPhWalk.lean `boundaryEndpoints`.
  //
  boundaryEndpoints(s, t) {
    if (this.cnt <= 2) { return this.two(t, s); }
    let x = null;
    for (const y of this.nbrsL(s)) {
      if (this.inU[y[0]] !== 1) {
        x = y;
        break;
      }
    }
    if (x !== null) { return this.boundaryEndpointsWalk(s, x[0], x[1], this.fuelA, t); }
    for (const y of this.nbrsL(s)) {
      if ( (this.inU[y[0]] === 1) && (y[0] !== t) ) {
        this.del(s);
        let P = null;
        if (this.viable(y[0], t)) {
          P = this.boundaryEndpointsWalk(y[0], s, y[1], this.fuelA, t);
          if (P === null) { this.failed(y[0], t); }
        }
        this.restore(s);
        if (P !== null) { return [s].concat(P); }
      }
    }
    return null;
  }

  // HoleWalk.lean `holeCaseWalk` (fin = [t, r, e0]; w's phantom pw = t).
  //
  holeCaseWalk(fin, w, pw, n, s, q, e1) {
    this.stats.inc('walk_nodes');
    if (n === 0) { return null; }
    if (this.cnt <= 2) {
      for (const x of this.nbrsL(w)) {
        if (x[0] === s) { return [s, w]; }
      }
      return null;
    }
    if ( this.isFar(w, s) && (!this.phantomsOpposed(w, pw, s, q)) ) {
      return this.oneHoleFinalTest(s, w, fin[0], fin[1], q, fin[2], e1);
    }
    for (const x of this.nbrsL(s)) {
      if ( (this.inU[x[0]] === 1) && (x[0] !== w) ) {
        this.del(s);
        let P = null;
        if (this.viable(x[0], w)) {
          P = this.holeCaseWalk(fin, w, pw, n - 1, x[0], s, x[1]);
          if (P === null) { this.failed(x[0], w); }
        }
        this.restore(s);
        if (P !== null) { return [s].concat(P); }
      }
    }
    return null;
  }

  // HoleWalk.lean `holeCase` with the final test oneHoleFinalTest (r = null) or twoHoleFinalTest (r = original s).
  //
  holeCase(s, t, r) {
    if (this.cnt <= 2) { return this.two(t, s); }
    for (const y of this.nbrsL(t)) {
      if ( (this.inU[y[0]] === 1) && (y[0] !== s) ) {
        this.del(t);
        let P = null;
        if (this.viable(s, y[0])) {
          if (this.cnt <= 2) {
            for (const x of this.nbrsL(y[0])) {
              if (x[0] === s) {
                P = [s, y[0]];
                break;
              }
            }
          }
          else {
            for (const x of this.nbrsL(s)) {
              if ( (this.inU[x[0]] === 1) && (x[0] !== y[0]) ) {
                this.del(s);
                let P2 = null;
                if (this.viable(x[0], y[0])) {
                  P2 = this.holeCaseWalk([t, r, y[1]], y[0], t, this.fuelG, x[0], s, x[1]);
                  if (P2 === null) { this.failed(x[0], y[0]); }
                }
                this.restore(s);
                if (P2 !== null) {
                  P = [s].concat(P2);
                  break;
                }
              }
            }
          }
          if (P === null) { this.failed(s, y[0]); }
        }
        this.restore(t);
        if (P !== null) {
          P.push(t);
          return P;
        }
      }
    }
    return null;
  }

  isInner(p) {
    const cx = this.cx, Wd = cx.Wd;
    return ( cx.isCell(this.inU, p - Wd - 1) && cx.isCell(this.inU, p - Wd) &&
             cx.isCell(this.inU, p - 1) && cx.isCell(this.inU, p) );
  }

  // HPFinal.lean `decideHamPath` on ids.
  //
  decideHamPath(s, t) {
    if (this.isInner(s)) {
      if (this.isInner(t)) { return this.holeCase(s, t, s); }
      const P = this.holeCase(t, s, null);
      return ( (P === null) ? null : P.reverse() );
    }
    if (this.isInner(t)) { return this.holeCase(s, t, null); }
    return this.boundaryEndpoints(s, t);
  }
}

// ---------------------------------------------------------------------------------------------
// S8: heuristic yes-first (hpst_fast.py `heuristic_path`), with an explicit stack instead of
// recursion. DFS from s, Warnsdorff order (fewest free neighbours, then Manhattan distance to
// t), the degree rule, a connectivity check every fourth depth, within a node budget and a
// time box. Returns a path of ids or null.
// ---------------------------------------------------------------------------------------------

function heuristicPath(cx, inU, Ul, s, t, timeBox, nodeBox) {
  const n = Ul.length, Wd = cx.Wd;
  const vis  = new Uint8Array(cx.N);
  const free = new Int32Array(cx.N);
  let nvis = 1;
  vis[s] = 1;
  for (const p of Ul) { free[p] = inU[p + 1] + inU[p - 1] + inU[p + Wd] + inU[p - Wd]; }
  for (const v of cx.nbrs4(s)) {
    if (inU[v] === 1) { free[v]--; }
  }
  const path = [s];
  const tEnd = now() + timeBox;
  let nodes = 0;
  const tx = (t % Wd), ty = Math.floor(t / Wd);
  const mark = cx.mark;

  const connected = (cur) => {
    const g = cx.newGen();
    mark[cur] = g;
    let cnt = 1;
    const st = [cur];
    while (st.length > 0) {
      const u = st.pop();
      for (const v of cx.nbrs4(u)) {
        if ( (inU[v] === 1) && (vis[v] !== 1) && (mark[v] !== g) ) {
          mark[v] = g;
          cnt++;
          st.push(v);
        }
      }
    }
    return ( cnt === ((n - nvis) + 1) );
  };

  // Entering a node: true / false for a decided node, else the sorted candidate list. Throws
  // 'budget' when the node or time budget is exceeded.
  //
  const enter = (cur) => {
    nodes++;
    if ( (nodes > nodeBox) || ( ((nodes & 255) === 0) && (now() > tEnd) ) ) { throw 'budget'; }
    if (nvis === n) { return ( cur === t ); }
    if ( ((nvis & 3) === 0) && (!connected(cur)) ) { return false; }
    let cand = [];
    let must = -1;
    for (const v of cx.nbrs4(cur)) {
      if ( (inU[v] === 1) && (vis[v] !== 1) ) {
        if ( (v === t) && (nvis < (n - 1)) ) { continue; }
        if ( (v !== t) && (free[v] <= 1) ) {
          if (must >= 0) { return false; }
          must = v;
        }
        cand.push(v);
      }
    }
    if (must >= 0) { cand = [must]; }
    const md = (v) => (Math.abs((v % Wd) - tx) + Math.abs(Math.floor(v / Wd) - ty));
    cand.sort((a, b) => ( (free[a] !== free[b]) ? (free[a] - free[b]) : (md(a) - md(b)) ));
    return cand;
  };

  const apply = (v) => {
    vis[v] = 1;
    nvis++;
    path.push(v);
    for (const u of cx.nbrs4(v)) {
      if (inU[u] === 1) { free[u]--; }
    }

    // A neighbour other than t left with no free neighbour after this step is dead.
    //
    for (const u of cx.nbrs4(v)) {
      if ( (inU[u] === 1) && (vis[u] !== 1) && (u !== t) && (free[u] < 1) ) { return false; }
    }
    return true;
  };

  const undo = (v) => {
    for (const u of cx.nbrs4(v)) {
      if (inU[u] === 1) { free[u]++; }
    }
    path.pop();
    vis[v] = 0;
    nvis--;
  };

  try {
    const r0 = enter(s);
    if (r0 === true)  { return path.slice(); }
    if (r0 === false) { return null; }

    // Frames: candidate list and index of the candidate currently applied (-1: none yet).
    //
    const fC = [r0], fI = [-1];
    while (fC.length > 0) {
      const top = fC.length - 1;
      const C = fC[top];
      if (fI[top] >= 0) { undo(C[fI[top]]); }
      fI[top]++;
      if (fI[top] >= C.length) {
        fC.pop();
        fI.pop();
        continue;
      }
      const v = C[fI[top]];
      if (!apply(v)) { continue; }
      const r = enter(v);
      if (r === true) { return path.slice(); }
      if (r === false) { continue; }
      fC.push(r);
      fI.push(-1);
    }
  }
  catch (ex) {
    if (ex === 'budget') { return null; }
    throw ex;
  }
  return null;
}

// ---------------------------------------------------------------------------------------------
// Input checks, verification, parsing and drawing (shared by cli.js and browser use).
// ---------------------------------------------------------------------------------------------

const keyOf = (p) => (p[0] + ',' + p[1]);

// Basics.lean `Solid`: every missing point of the box (margin 1) reaches the outside by king
// moves through missing points.
//
export function isSolid(V) {
  if (V.length === 0) { return true; }
  let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
  for (const p of V) {
    if (p[0] < x0) { x0 = p[0]; }
    if (p[0] > x1) { x1 = p[0]; }
    if (p[1] < y0) { y0 = p[1]; }
    if (p[1] > y1) { y1 = p[1]; }
  }
  x0--; x1++; y0--; y1++;
  const W = x1 - x0 + 1, H = y1 - y0 + 1;
  const inV = new Uint8Array(W * H), seen = new Uint8Array(W * H);
  for (const p of V) { inV[(p[0] - x0) + ((p[1] - y0) * W)] = 1; }
  const st = [];
  for (let y = 0; y < H; y++) { st.push(y * W); }
  while (st.length > 0) {
    const i = st.pop();
    if ( (seen[i] === 1) || (inV[i] === 1) ) { continue; }
    seen[i] = 1;
    const x = i % W, y = Math.floor(i / W);
    for (let a = -1; a <= 1; a++) {
      for (let b = -1; b <= 1; b++) {
        const xx = x + a, yy = y + b;
        if ( (xx >= 0) && (xx < W) && (yy >= 0) && (yy < H) ) { st.push(xx + (yy * W)); }
      }
    }
  }
  for (let i = 0; i < (W * H); i++) {
    if ( (inV[i] !== 1) && (seen[i] !== 1) ) { return false; }
  }
  return true;
}

export function verifyPath(V, s, t, P) {
  const set = new Set(V.map(keyOf));
  if ( (!P) || (P.length === 0) || (keyOf(P[0]) !== keyOf(s)) ||
       (keyOf(P[P.length - 1]) !== keyOf(t)) || (P.length !== set.size) ) {
    return false;
  }
  const got = new Set(P.map(keyOf));
  if (got.size !== set.size) { return false; }
  for (const k of got) {
    if (!set.has(k)) { return false; }
  }
  for (let i = 0; (i + 1) < P.length; i++) {
    const a = P[i], b = P[i + 1];
    if ((Math.abs(a[0] - b[0]) + Math.abs(a[1] - b[1])) !== 1) { return false; }
  }
  return true;
}

export class InputError extends Error {}

// ASCII grid (lib/README.md): `.` point, `#` / space / tab not a point, `s` / `t` endpoints;
// `;` comment lines; x = column, y = row counted from the bottom.
//
function pyRepr(ch) { return ( (ch === "'") ? '"\'"' : ("'" + ch + "'") ); }

export function parseAscii(text) {
  let rows = text.split('\n').map((ln) => ln.replace(/\r+$/, ''));
  rows = rows.filter((ln) => !ln.startsWith(';'));
  while ( (rows.length > 0) && (rows[0].trim() === '') ) { rows.shift(); }
  while ( (rows.length > 0) && (rows[rows.length - 1].trim() === '') ) { rows.pop(); }
  if (rows.length === 0) { throw new InputError("empty grid"); }
  const V = [], seen = new Set();
  let s = null, t = null;
  const h = rows.length;
  for (let r = 0; r < h; r++) {
    const ln = Array.from(rows[r]);
    const y = h - 1 - r;
    for (let x = 0; x < ln.length; x++) {
      const ch = ln[x];
      if ( (ch === '.') || (ch === 's') || (ch === 't') ) {
        if (!seen.has(x + ',' + y)) {
          seen.add(x + ',' + y);
          V.push([x, y]);
        }
        if (ch === 's') {
          if (s !== null) { throw new InputError("more than one 's'"); }
          s = [x, y];
        }
        else if (ch === 't') {
          if (t !== null) { throw new InputError("more than one 't'"); }
          t = [x, y];
        }
      }
      else if (!( (ch === '#') || (ch === ' ') || (ch === '\t') )) {
        throw new InputError("unexpected character " + pyRepr(ch) + " at row " + (r + 1) +
                             " column " + x);
      }
    }
  }
  return { V: V, s: s, t: t };
}

function toInt(v) {
  if ( (typeof v === 'number') && Number.isFinite(v) ) { return Math.trunc(v); }
  if ( (typeof v === 'string') && /^\s*[+-]?\d+\s*$/.test(v) ) { return parseInt(v, 10); }
  if (typeof v === 'boolean') { return ( v ? 1 : 0 ); }
  throw new InputError("bad JSON input: invalid coordinate " + JSON.stringify(v));
}

function toPt(p) {
  if ( (!Array.isArray(p)) || (p.length < 2) ) {
    throw new InputError("bad JSON input: a point must be [x, y]");
  }
  return [toInt(p[0]), toInt(p[1])];
}

export function parseJson(text) {
  let d;
  try {
    d = JSON.parse(text);
  }
  catch (ex) {
    throw new InputError("bad JSON input: " + ex.message);
  }
  if ( (d === null) || (typeof d !== 'object') || (!Array.isArray(d.points)) ) {
    throw new InputError("bad JSON input: 'points' (a list of [x, y]) is required");
  }
  const V = [], seen = new Set();
  for (const p of d.points) {
    const q = toPt(p);
    if (!seen.has(keyOf(q))) {
      seen.add(keyOf(q));
      V.push(q);
    }
  }
  const s = ( ((d.s !== undefined) && (d.s !== null)) ? toPt(d.s) : null );
  const t = ( ((d.t !== undefined) && (d.t !== null)) ? toPt(d.t) : null );
  return { V: V, s: s, t: t };
}

export function parseInput(text) {
  if (text.trimStart().startsWith('{')) { return parseJson(text); }
  return parseAscii(text);
}

// Checks the input as the CLI does; throws InputError (CLI exit code 2).
//
export function checkInput(V, s, t) {
  if ( (s === null) || (t === null) ) {
    throw new InputError("both endpoints s and t are required");
  }
  const set = new Set(V.map(keyOf));
  if ( (!set.has(keyOf(s))) || (!set.has(keyOf(t))) ) {
    throw new InputError("s and t must be points of V");
  }
  if (keyOf(s) === keyOf(t)) { throw new InputError("s and t must differ"); }
  if (!isSolid(V)) {
    throw new InputError("V is not solid (it has a hole: a missing point that cannot reach the " +
                         "outside by king moves through missing points)");
  }
}

// ASCII drawing at double resolution: points on even columns / rows, path edges between them.
//
export function draw(V, s, t, P) {
  let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
  for (const p of V) {
    if (p[0] < x0) { x0 = p[0]; }
    if (p[0] > x1) { x1 = p[0]; }
    if (p[1] < y0) { y0 = p[1]; }
    if (p[1] > y1) { y1 = p[1]; }
  }
  const inV = new Set(V.map(keyOf));
  const E = new Set();
  const ek = (a, b) => (keyOf(a) + ';' + keyOf(b));
  const hasP = ( (P !== null) && (P !== undefined) && (P.length > 0) );
  if (hasP) {
    for (let i = 0; (i + 1) < P.length; i++) {
      E.add(ek(P[i], P[i + 1]));
      E.add(ek(P[i + 1], P[i]));
    }
  }
  const glyph = { 'RL': '─', 'UD': '│', 'RD': '┌', 'LD': '┐', 'RU': '└', 'LU': '┘' };
  const out = [];
  for (let y = y1; y >= y0; y--) {
    let line = '';
    for (let x = x0; x <= x1; x++) {
      const p = [x, y];
      let ch;
      if      (!inV.has(keyOf(p)))   { ch = ' '; }
      else if (keyOf(p) === keyOf(s)) { ch = 's'; }
      else if (keyOf(p) === keyOf(t)) { ch = 't'; }
      else if (!hasP)                 { ch = '.'; }
      else {
        const k = ( (E.has(ek(p, [x + 1, y])) ? 'R' : '') + (E.has(ek(p, [x - 1, y])) ? 'L' : '') +
                    (E.has(ek(p, [x, y + 1])) ? 'U' : '') + (E.has(ek(p, [x, y - 1])) ? 'D' : '') );
        ch = ( (k in glyph) ? glyph[k] : '?' );
      }
      line += ch;
      if (x < x1) { line += ( E.has(ek(p, [x + 1, y])) ? '─' : ' ' ); }
    }
    out.push(line.replace(/\s+$/, ''));
    if (y > y0) {
      line = '';
      for (let x = x0; x <= x1; x++) {
        line += ( E.has(ek([x, y], [x, y - 1])) ? '│' : ' ' );
        if (x < x1) { line += ' '; }
      }
      out.push(line.replace(/\s+$/, ''));
    }
  }
  return out.join('\n');
}

// ---------------------------------------------------------------------------------------------
// Entry point (hpst_fast.py `decideHamPath`). Returns { answer, path, stats }; stats = { counts,
// times (seconds), branch, decided_by }, keys in the order Python's dicts would have them.
// ---------------------------------------------------------------------------------------------

export function solve(points, s, t, options = {}) {
  const heuristic = ( (options.heuristic === undefined) ? true : options.heuristic );
  const order = ( options.order || 'abs' );
  const prune = ( (options.prune === undefined) ? true : options.prune );
  const memo  = ( (options.memo === undefined) ? true : options.memo );

  const set = new Set();
  const V = [];
  for (const p of points) {
    if (!set.has(keyOf(p))) {
      set.add(keyOf(p));
      V.push([p[0], p[1]]);
    }
  }
  if ( (!set.has(keyOf(s))) || (!set.has(keyOf(t))) || (keyOf(s) === keyOf(t)) ) {
    throw new InputError("s and t must be distinct points of V");
  }

  const T0 = now();
  const sv_ = new Solver(V, order, prune, memo);
  const cx = sv_.cx, st = sv_.stats;
  const si = cx.pid(s), ti = cx.pid(t);
  const branch = ( sv_.isInner(si) ? (sv_.isInner(ti) ? 'twoHoleCase' : 'oneHoleCase-swap') :
                                    (sv_.isInner(ti) ? 'oneHoleCase' : 'boundaryEndpoints') );
  let how = null, res = null;

  const finish = () => {
    st.addTime('total', now() - T0);
    return { answer: ( (res !== null) ? 'yes' : 'no' ), path: res,
             stats: { counts: Object.fromEntries(st.c), times: Object.fromEntries(st.t),
                      branch: branch, decided_by: how } };
  };

  if (prune) {
    const t0 = now();
    const ok = nec(cx, sv_.inU, sv_.Ul(), si, ti);
    st.addTime('global', now() - t0);
    if (!ok) {
      how = 'global-reject';
      return finish();
    }
  }
  if (heuristic) {
    const n = V.length;
    const tb = ( (options.timeBox !== undefined) ? options.timeBox :
                 Math.min(2.0, 0.05 + (0.002 * n)) );
    const t0 = now();
    const P = heuristicPath(cx, sv_.inU, sv_.Ul(), si, ti, tb, 2000 + (200 * n));
    st.addTime('heuristic', now() - t0);
    if (P !== null) {
      const Pp = P.map((i) => cx.pt(i));
      if (verifyPath(V, s, t, Pp)) {
        how = 'heuristic';
        res = Pp;
        return finish();
      }
    }
  }
  how = 'algorithm';
  const t0 = now();
  const P = sv_.decideHamPath(si, ti);
  st.addTime('algorithm', now() - t0);
  res = ( (P === null) ? null : P.map((i) => cx.pt(i)) );
  return finish();
}
