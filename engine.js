"use strict";
// LIA-fast: a logical inductor (Garrabrant et al. 2016, Sec. 5) with the speedups described above.
// Port of lia.py. Pure JS, no dependencies.

// ---------------------------------------------------------------- sentences
const SENT = new Map();
function intern(key, op, a, b, i) {
  let s = SENT.get(key);
  if (!s) { s = { key, op, a, b, i, at: null }; SENT.set(key, s); }
  return s;
}
const atom = i => intern("a" + i, "a", null, null, i);
const neg = s => intern("¬" + s.key, "~", s, null);
const conj = (s, t) => intern("(" + s.key + "∧" + t.key + ")", "&", s, t);
const disj = (s, t) => intern("(" + s.key + "∨" + t.key + ")", "|", s, t);

function atomsOf(s) {
  if (!s.at) {
    if (s.op === "a") s.at = [s.i];
    else if (s.op === "~") s.at = atomsOf(s.a);
    else s.at = [...new Set([...atomsOf(s.a), ...atomsOf(s.b)])];
  }
  return s.at;
}
function holds(s, asg) {
  switch (s.op) {
    case "a": return asg.get(s.i);
    case "~": return !holds(s.a, asg);
    case "&": return holds(s.a, asg) && holds(s.b, asg);
    default: return holds(s.a, asg) || holds(s.b, asg);
  }
}

// ---------------------------------------------------------------- PC(D)
// Worlds propositionally consistent with D, queried on finite sets of sentences.  Atoms are
// linked when they share a query sentence or a sentence of D; a linear objective over PC(D)
// then splits exactly into independent per-component minima.
const COUNT = { oracle: 0 };
class WorldSpace {
  constructor(D) {
    this.fixed = new Map(); this.cons = []; this.byAtom = new Map(); this.cache = new Map();
    this.add(D || []);
  }
  add(D) {
    for (const s of D) {
      if (s.op === "a") this.fix(s.i, true);
      else if (s.op === "~" && s.a.op === "a") this.fix(s.a.i, false);
      else {
        this.cons.push(s);
        for (const a of atomsOf(s)) {
          if (!this.byAtom.has(a)) this.byAtom.set(a, []);
          this.byAtom.get(a).push(s);
        }
      }
    }
    this.cache.clear();
  }
  fix(a, v) {
    if (this.fixed.has(a) && this.fixed.get(a) !== v) throw new Error("deductive process is inconsistent");
    this.fixed.set(a, v);
  }
  components(sentences) {
    const uniq = [...new Set(sentences)];
    const key = uniq.map(s => s.key).sort().join("|");
    const hit = this.cache.get(key);
    if (hit) return hit;
    const parent = new Map();
    const find = x => { while (parent.get(x) !== x) { parent.set(x, parent.get(parent.get(x))); x = parent.get(x); } return x; };
    const union = (x, y) => {
      if (!parent.has(x)) parent.set(x, x);
      if (!parent.has(y)) parent.set(y, y);
      const rx = find(x), ry = find(y);
      if (rx !== ry) parent.set(rx, ry);
    };
    const frontier = [];
    for (const s of uniq) {
      const at = atomsOf(s);
      for (const a of at) { if (!parent.has(a)) parent.set(a, a); frontier.push(a); }
      for (const a of at) union(at[0], a);
    }
    const seen = new Set(), used = [], visited = new Set();
    while (frontier.length) {
      const a = frontier.pop();
      if (visited.has(a)) continue;
      visited.add(a);
      for (const c of this.byAtom.get(a) || []) {
        if (seen.has(c)) continue;
        seen.add(c); used.push(c);
        const ca = atomsOf(c);
        for (const b of ca) { union(ca[0], b); if (!visited.has(b)) frontier.push(b); }
      }
    }
    const groups = new Map();
    const g = r => { if (!groups.has(r)) groups.set(r, { atoms: [], sents: [], cons: [] }); return groups.get(r); };
    for (const a of parent.keys()) g(find(a)).atoms.push(a);
    for (const s of uniq) g(find(atomsOf(s)[0])).sents.push(s);
    for (const c of used) g(find(atomsOf(c)[0])).cons.push(c);
    const comps = [];
    for (const { atoms, sents, cons } of groups.values()) {
      if (!sents.length) continue;
      const free = atoms.filter(a => !this.fixed.has(a));
      if (free.length > 22) throw new Error("component with " + free.length + " free atoms");
      const asg = new Map();
      for (const a of atoms) if (this.fixed.has(a)) asg.set(a, this.fixed.get(a));
      const vecs = new Map();
      for (let m = 0; m < (1 << free.length); m++) {
        for (let i = 0; i < free.length; i++) asg.set(free[i], ((m >> i) & 1) === 1);
        if (cons.every(c => holds(c, asg))) {
          const v = sents.map(s => (holds(s, asg) ? 1 : 0));
          vecs.set(v.join(""), v);
        }
      }
      if (!vecs.size) throw new Error("PC(D) is empty");
      comps.push({ sents, vecs: [...vecs.values()] });
    }
    this.cache.set(key, comps);
    return comps;
  }
  // min over W in PC(D) of  cash + sum_phi coef(phi) W(phi)
  minLinear(cash, coef /* Map sentence -> number */) {
    COUNT.oracle++;
    let tot = cash;
    for (const { sents, vecs } of this.components([...coef.keys()])) {
      const c = sents.map(s => coef.get(s));
      let best = Infinity;
      for (const v of vecs) { let x = 0; for (let i = 0; i < v.length; i++) if (v[i]) x += c[i]; if (x < best) best = x; }
      tot += best;
    }
    return tot;
  }
}

class DeductiveProcess {
  // D_n = sentences revealed on days <= n; reveal(n, history) may look at P_1..P_{n-1}.
  constructor(reveal) { this.reveal = reveal; this.D = new Set(); this.day = 0; this.ws = new WorldSpace([]); }
  advance(n, history) {
    const add = this.reveal(n, history);
    for (const s of add) this.D.add(s);
    this.day = n;
    this.ws.add(add);
    return this.ws;
  }
}

// ---------------------------------------------------------------- expressible features
// Rationals, price features, +, *, max and safe reciprocation 1/max(1,x)  (paper, Def. 3.4.4).
const lift = x => (typeof x === "number" ? { t: "c", q: x } : x);
const Price = (s, day) => ({ t: "p", s, day });
const add = (a, b) => ({ t: "+", a: lift(a), b: lift(b) });
const mul = (a, b) => ({ t: "*", a: lift(a), b: lift(b) });
const sub = (a, b) => add(a, mul(-1, b));
const fmax = (a, b) => ({ t: "max", a: lift(a), b: lift(b) });
const fmin = (a, b) => mul(-1, fmax(mul(-1, a), mul(-1, b)));
const clip = (x, lo, hi) => fmin(fmax(x, lo), hi);
const safeRecip = a => ({ t: "rcp", a: lift(a) });

// Compile an n-strategy {sentence: feature} into a register program.  Past prices fold to
// constants; interval bounds and l_inf-Lipschitz constants (in today's prices) come from
// structural induction, exactly as the paper bounds C_n.
class Strategy {
  constructor(coeffs /* Map sentence -> feature */, n, history) {
    this.sents = [...coeffs.keys()];
    const prog = [], lo = [], hi = [], lip = [], memo = new Map();
    const reg = node => {
      if (memo.has(node)) return memo.get(node);
      let r, b0, b1, L;
      if (node.t === "c") { r = prog.length; prog.push([0, node.q]); b0 = b1 = node.q; L = 0; }
      else if (node.t === "p") {
        if (node.day < n) {
          const v = node.day >= 1 ? (history[node.day - 1].get(node.s) ?? 0) : 0;
          r = prog.length; prog.push([0, v]); b0 = b1 = v; L = 0;
        } else if (node.day === n) { r = prog.length; prog.push([1, node.s]); b0 = 0; b1 = 1; L = 1; }
        else throw new Error("feature refers to a future price");
      } else if (node.t === "rcp") {
        const a = reg(node.a);
        r = prog.length; prog.push([5, a]);
        b0 = 1 / Math.max(1, hi[a]); b1 = 1 / Math.max(1, lo[a]); L = lip[a];
      } else {
        const a = reg(node.a), b = reg(node.b);
        r = prog.length;
        if (node.t === "+") { prog.push([2, a, b]); b0 = lo[a] + lo[b]; b1 = hi[a] + hi[b]; L = lip[a] + lip[b]; }
        else if (node.t === "*") {
          prog.push([3, a, b]);
          const pr = [lo[a] * lo[b], lo[a] * hi[b], hi[a] * lo[b], hi[a] * hi[b]];
          b0 = Math.min(...pr); b1 = Math.max(...pr);
          L = lip[a] * Math.max(Math.abs(lo[b]), Math.abs(hi[b])) + lip[b] * Math.max(Math.abs(lo[a]), Math.abs(hi[a]));
        } else { prog.push([4, a, b]); b0 = Math.max(lo[a], lo[b]); b1 = Math.max(hi[a], hi[b]); L = Math.max(lip[a], lip[b]); }
      }
      lo[r] = b0; hi[r] = b1; lip[r] = L; memo.set(node, r);
      return r;
    };
    this.outs = this.sents.map(s => reg(lift(coeffs.get(s))));
    this.prog = prog;
    this.R = new Float64Array(prog.length);
    this.bounds = this.outs.map(o => Math.max(Math.abs(lo[o]), Math.abs(hi[o])));
    this.lips = this.outs.map(o => lip[o]);
    this.valueLip = this.bounds.reduce((acc, B, i) => acc + B + this.lips[i], 0);
  }
  eval(P /* Map sentence -> today's price */) {
    const R = this.R, prog = this.prog;
    for (let i = 0; i < prog.length; i++) {
      const ins = prog[i];
      switch (ins[0]) {
        case 0: R[i] = ins[1]; break;
        case 1: R[i] = P.get(ins[1]) ?? 0; break;
        case 2: R[i] = R[ins[1]] + R[ins[2]]; break;
        case 3: R[i] = R[ins[1]] * R[ins[2]]; break;
        case 4: R[i] = R[ins[1]] > R[ins[2]] ? R[ins[1]] : R[ins[2]]; break;
        default: { const x = R[ins[1]]; R[i] = 1 / (x > 1 ? x : 1); }
      }
    }
    return this.outs.map(o => R[o]);
  }
}

// ---------------------------------------------------------------- Lemma 1: the world-free check
// max over ALL worlds W of W(T(p)) = sum_phi T_phi^+ (1 - p_phi) + T_phi^- p_phi
function gap(t, p) {
  let g = 0;
  for (let i = 0; i < t.length; i++) g += t[i] > 0 ? t[i] * (1 - p[i]) : -t[i] * p[i];
  return g;
}
// the paper's check, literally: enumerate all 2^d worlds
function maxOverAllWorlds(t, p) {
  let cash = 0;
  for (let i = 0; i < t.length; i++) cash -= t[i] * p[i];
  let best = -Infinity;
  for (let m = 0; m < (1 << t.length); m++) {
    let v = cash;
    for (let i = 0; i < t.length; i++) if ((m >> i) & 1) v += t[i];
    if (v > best) best = v;
  }
  return best;
}

// ---------------------------------------------------------------- weights and budgets
// fast : trader weight 1/(k(k+1)); budget 2^j with weight u_j = a_j - a_{j+1}, a_j = 2^-j/(j+1)^2
//        (telescoping: every tail sum is the rational a_J); alive while M <= b/2.
// paper: trader weight 2^-k; integer budget b with weight 2^-b; alive while M < b.
const FastSchedule = {
  name: "fast",
  traderWeight: k => 1 / (k * (k + 1)),
  budget: j => 2 ** j,
  a: j => 2 ** -j / ((j + 1) * (j + 1)),
  levelWeight(j) { return this.a(j) - this.a(j + 1); },
  firstAlive: M => (M <= 0.5 ? 0 : Math.max(0, Math.ceil(Math.log2(2 * M) - 1e-12))),
  firstSaturated: L => (L <= 1 ? 0 : Math.max(0, Math.ceil(Math.log2(L) - 1e-12))),
  tail(j) { return j < 1000 ? this.a(j) : 0; },
};
const PaperSchedule = {
  name: "paper",
  traderWeight: k => 2 ** -k,
  budget: j => j,
  levelWeight: j => 2 ** -j,
  firstAlive: M => Math.max(1, Math.floor(M) + 1),
  firstSaturated: L => Math.max(1, Math.ceil(L)),
  tail: j => 2 ** (1 - j),
};

// ---------------------------------------------------------------- one trader inside the firm, one day
class DayTrader {
  constructor(st, strat, ws, sched) {
    this.st = st; this.strat = strat; this.sched = sched;
    this.w = sched.traderWeight(st.k);
    this.jlo = sched.firstAlive(st.M);
    const spos = new Map(strat.sents.map((s, i) => [s, i]));
    this.comps = ws.components([...st.H.keys(), ...strat.sents]).map(({ sents, vecs }) => ({
      vecs,
      hv: vecs.map(v => sents.reduce((acc, s, i) => acc + (st.H.get(s) ?? 0) * v[i], 0)),
      cols: sents.map((s, i) => [spos.get(s), i]).filter(([si]) => si !== undefined),
    }));
  }
  // argmin over W in PC(D_n) of W(H) + alpha W(S); returns [W(H), W(S)] at the minimiser
  argmin(s, sCash, alpha) {
    COUNT.oracle++;
    let h = this.st.Hcash, x = sCash;
    for (const { vecs, hv, cols } of this.comps) {
      let bv = Infinity, bh = 0, bx = 0;
      for (let k = 0; k < vecs.length; k++) {
        const v = vecs[k];
        let xv = 0;
        for (const [si, ci] of cols) if (v[ci]) xv += s[si];
        const val = hv[k] + alpha * xv;
        if (val < bv) { bv = val; bh = hv[k]; bx = xv; }
      }
      h += bh; x += bx;
    }
    return [h, x];
  }
  // sum over alive budget levels j of u_j * alpha_j(p): finitely many unsaturated levels
  // plus a closed-form tail (Lemma 5)
  factor(s, prices) {
    const sch = this.sched;
    let sCash = 0;
    for (let i = 0; i < s.length; i++) sCash -= s[i] * prices[i];
    const [h1, x1] = this.argmin(s, sCash, 1);
    const L = -(h1 + x1);
    const jsat = Math.max(this.jlo, sch.firstSaturated(L));
    let tot = sch.tail(jsat);
    for (let j = this.jlo; j < jsat; j++) tot += sch.levelWeight(j) * this.newton(sch.budget(j), s, sCash, h1, x1);
    return tot;
  }
  // largest alpha in [0,1] with min_W [b + W(H) + alpha W(S)] >= 0  (Newton-Dinkelbach, Lemma 4)
  newton(b, s, sCash, h, x) {
    let alpha = 1;
    for (let it = 0; it < 10000; it++) {
      if (b + h + alpha * x >= -1e-12 * (1 + b)) return alpha;
      alpha = (b + h) / -x;
      [h, x] = this.argmin(s, sCash, alpha);
    }
    throw new Error("Newton did not terminate");
  }
}

// TF_n(p) = sum_k w_k [sum_j u_j alpha_{k,j}(p)] S^k_n(p)
class TradingFirm {
  constructor(dts, sched) {
    this.dts = dts; this.sched = sched; this.evals = 0;
    const supp = [], index = new Map();
    for (const dt of dts) for (const s of dt.strat.sents) if (!index.has(s)) { index.set(s, supp.length); supp.push(s); }
    this.supp = supp;
    this.maps = dts.map(dt => dt.strat.sents.map(s => index.get(s)));
  }
  eval(p) {
    this.evals++;
    const P = new Map(this.supp.map((s, i) => [s, p[i]]));
    const out = new Array(this.supp.length).fill(0);
    for (let k = 0; k < this.dts.length; k++) {
      const dt = this.dts[k], mp = this.maps[k];
      const s = dt.strat.eval(P);
      if (s.every(x => x === 0)) continue;
      const c = dt.w * dt.factor(s, mp.map(i => p[i]));
      if (c === 0) continue;
      for (let i = 0; i < mp.length; i++) out[mp[i]] += c * s[i];
    }
    return out;
  }
  // l_inf-Lipschitz bound for p -> gap(TF(p), p)  (needs the margin; fast schedule only)
  lipschitzOfGap() {
    const sch = this.sched, B = new Array(this.supp.length).fill(0), L = B.slice();
    this.dts.forEach((dt, k) => {
      const mass = sch.tail(dt.jlo);
      let inv = 0;
      for (let j = dt.jlo; j < dt.jlo + 200; j++) inv += sch.levelWeight(j) / sch.budget(j);
      const la = 2 * dt.strat.valueLip * inv;
      this.maps[k].forEach((i, q) => {
        B[i] += dt.w * mass * dt.strat.bounds[q];
        L[i] += dt.w * (la * dt.strat.bounds[q] + mass * dt.strat.lips[q]);
      });
    });
    return B.reduce((acc, b, i) => acc + b + L[i], 0);
  }
}

// ---------------------------------------------------------------- MarketMaker
// Find p in [0,1]^d with gap(TF(p), p) <= eps.  Heuristics are verified by the exact O(d) gap;
// the Lipschitz subdivision fallback is complete (Prop. 3).
const proj = x => (x < 0 ? 0 : x > 1 ? 1 : x);
const norm = v => Math.sqrt(v.reduce((acc, x) => acc + x * x, 0));

function mmBisect1d(T, eps) {
  if (T([1])[0] >= 0) return [1];
  if (T([0])[0] <= 0) return [0];
  let lo = 0, hi = 1;
  for (let i = 0; i < 200; i++) {
    const mid = (lo + hi) / 2, t = T([mid])[0];
    if (gap([t], [mid]) <= eps) return [mid];
    if (t > 0) lo = mid; else hi = mid;
  }
  return [(lo + hi) / 2];
}

function solveLinear(A, b) {
  const n = b.length, M = A.map((row, i) => [...row, b[i]]);
  for (let c = 0; c < n; c++) {
    let piv = c;
    for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[piv][c])) piv = r;
    if (Math.abs(M[piv][c]) < 1e-300) return null;
    [M[c], M[piv]] = [M[piv], M[c]];
    for (let r = c + 1; r < n; r++) {
      const f = M[r][c] / M[c][c];
      if (f) for (let k = c; k <= n; k++) M[r][k] -= f * M[c][k];
    }
  }
  const x = new Array(n).fill(0);
  for (let r = n - 1; r >= 0; r--) {
    let acc = M[r][n];
    for (let k = r + 1; k < n; k++) acc -= M[r][k] * x[k];
    x[r] = acc / M[r][r];
  }
  return x;
}

// Levenberg-Marquardt on the natural-map residual r(p) = p - Proj(p + c T(p))
function mmNewton(T, p, eps, maxIter = 60) {
  const d = p.length;
  let t = T(p);
  const c = 1 / Math.max(1e-12, ...t.map(Math.abs));
  const resid = (q, tq) => q.map((qi, i) => qi - proj(qi + c * tq[i]));
  let r = resid(p, t), nr = r.reduce((a, x) => a + x * x, 0), g = gap(t, p);
  let best = [g, p], lam = 1e-6;
  for (let it = 0; it < maxIter; it++) {
    if (g <= eps) return [p, g];
    const J = Array.from({ length: d }, () => new Array(d).fill(0));
    for (let j = 0; j < d; j++) {
      const h = p[j] < 0.5 ? 1e-7 : -1e-7, q = p.slice();
      q[j] += h;
      const rq = resid(q, T(q));
      for (let i = 0; i < d; i++) J[i][j] = (rq[i] - r[i]) / h;
    }
    const JTJ = Array.from({ length: d }, (_, i) => Array.from({ length: d }, (_, j) => {
      let s = 0; for (let k = 0; k < d; k++) s += J[k][i] * J[k][j]; return s;
    }));
    const JTr = Array.from({ length: d }, (_, i) => { let s = 0; for (let k = 0; k < d; k++) s += J[k][i] * r[k]; return s; });
    let improved = false;
    for (let ls = 0; ls < 12; ls++) {
      const A = JTJ.map((row, i) => row.map((v, j) => (i === j ? v + lam * (1 + JTJ[i][i]) : v)));
      const step = solveLinear(A, JTr.map(x => -x));
      if (!step) { lam *= 10; continue; }
      const q = p.map((pi, i) => proj(pi + step[i])), tq = T(q), rq = resid(q, tq);
      const nq = rq.reduce((a, x) => a + x * x, 0);
      if (nq < nr) {
        p = q; t = tq; r = rq; nr = nq; g = gap(t, p);
        if (g < best[0]) best = [g, p];
        lam = Math.max(1e-12, lam / 10); improved = true; break;
      }
      lam *= 10;
    }
    if (!improved) break;
  }
  return [best[1], best[0]];
}

// projected extragradient with Khobotov backtracking
function mmExtragradient(T, p, eps, maxIter = 2000) {
  let t = T(p), g = gap(t, p), best = [g, p], eta = 1;
  for (let it = 0; it < maxIter; it++) {
    if (g <= eps) return [p, g];
    let y, ty;
    for (;;) {
      y = p.map((pi, i) => proj(pi + eta * t[i]));
      ty = T(y);
      const gy = gap(ty, y);
      if (gy <= eps) return [y, gy];
      const dy = norm(y.map((v, i) => v - p[i])), dt = norm(ty.map((v, i) => v - t[i]));
      if (eta * dt <= 0.9 * dy + 1e-18 || eta < 1e-12) break;
      eta *= 0.5;
    }
    p = p.map((pi, i) => proj(pi + eta * ty[i]));
    t = T(p); g = gap(t, p);
    if (g < best[0]) best = [g, p];
    eta *= 1.5;
  }
  return [best[1], best[0]];
}

// nonlinear Gauss-Seidel: each 1-d complementarity problem by bisection
function mmCoordinate(T, p, eps, sweeps = 60) {
  p = p.slice();
  let g = gap(T(p), p);
  for (let sw = 0; sw < sweeps && g > eps; sw++) {
    for (let i = 0; i < p.length; i++) {
      const h = x => { const q = p.slice(); q[i] = x; return T(q)[i]; };
      if (h(1) >= 0) p[i] = 1;
      else if (h(0) <= 0) p[i] = 0;
      else {
        let lo = 0, hi = 1;
        for (let k = 0; k < 40; k++) { const mid = (lo + hi) / 2; if (h(mid) > 0) lo = mid; else hi = mid; }
        p[i] = (lo + hi) / 2;
      }
    }
    g = gap(T(p), p);
  }
  return [p, g];
}

// complete fallback: best-first box subdivision; a box whose centre has gap > lip*radius holds no zero
function mmSubdivide(T, d, eps, lip, maxCells = 200000) {
  const heap = [];
  const push = e => { heap.push(e); let i = heap.length - 1; while (i > 0) { const pa = (i - 1) >> 1; if (heap[pa][0] <= heap[i][0]) break; [heap[pa], heap[i]] = [heap[i], heap[pa]]; i = pa; } };
  const pop = () => {
    const top = heap[0], last = heap.pop();
    if (heap.length) {
      heap[0] = last; let i = 0;
      for (;;) { const l = 2 * i + 1, r = l + 1; let m = i; if (l < heap.length && heap[l][0] < heap[m][0]) m = l; if (r < heap.length && heap[r][0] < heap[m][0]) m = r; if (m === i) break; [heap[m], heap[i]] = [heap[i], heap[m]]; i = m; }
    }
    return top;
  };
  const centre = (lo, hi) => lo.map((a, i) => (a + hi[i]) / 2);
  let lo = new Array(d).fill(0), hi = new Array(d).fill(1), c = centre(lo, hi);
  push([gap(T(c), c), lo, hi, c]);
  for (let cells = 0; heap.length && cells < maxCells; cells++) {
    const [g, blo, bhi, bc] = pop();
    if (g <= eps) return [bc, g];
    let w = 0;
    for (let k = 1; k < d; k++) if (bhi[k] - blo[k] > bhi[w] - blo[w]) w = k;
    const mid = (blo[w] + bhi[w]) / 2;
    for (const [a, b] of [[blo[w], mid], [mid, bhi[w]]]) {
      const nlo = blo.slice(), nhi = bhi.slice();
      nlo[w] = a; nhi[w] = b;
      const nc = centre(nlo, nhi), ng = gap(T(nc), nc);
      const r = Math.max(...nlo.map((x, i) => (nhi[i] - x) / 2));
      if (ng <= lip * r + 1e-15) push([ng, nlo, nhi, nc]);
    }
  }
  throw new Error("subdivision gave up (cell cap)");
}

function marketMaker(TF, eps, warm, lipFn) {
  const d = TF.supp.length, e0 = TF.evals, T = p => TF.eval(p);
  if (d === 0) return { p: [], gap: 0, method: "empty", evals: 0 };
  if (d === 1) { const p = mmBisect1d(T, eps); return { p, gap: gap(T(p), p), method: "bisection", evals: TF.evals - e0 }; }
  let p = TF.supp.map(s => warm.get(s) ?? 0.5);
  let g = gap(T(p), p);
  if (g <= eps) return { p, gap: g, method: "warm start", evals: TF.evals - e0 };
  for (const [name, solver] of [["Newton", mmNewton], ["extragradient", mmExtragradient], ["Gauss–Seidel", mmCoordinate]]) {
    [p, g] = solver(T, p, eps);
    if (g <= eps && gap(T(p), p) <= eps) return { p, gap: g, method: name, evals: TF.evals - e0 };
  }
  if (!lipFn || d > 8) throw new Error("heuristics failed and no guaranteed fallback for d = " + d);
  [p, g] = mmSubdivide(T, d, eps, lipFn());
  return { p, gap: g, method: "subdivision", evals: TF.evals - e0 };
}

// ---------------------------------------------------------------- the outer recursion
// P_n := MarketMaker_n(TradingFirm_n(P_<n), P_<n)
class Market {
  constructor(traders, dp, { schedule = FastSchedule, tol = n => 1e-3 / (n * n) } = {}) {
    this.dp = dp; this.sched = schedule; this.tol = tol;
    this.states = traders.map((trader, i) => ({ k: i + 1, trader, start: i + 1, H: new Map(), Hcash: 0, M: 0 }));
    this.history = []; this.day = 0; this.firmValue = 0; this.sumEps = 0;
  }
  step() {
    const n = this.day + 1, t0 = performance.now();
    COUNT.oracle = 0;
    const ws = this.dp.advance(n, this.history);
    const active = this.states.filter(st => st.start <= n);
    const strats = active.map(st => new Strategy(st.trader.strategy(n, this.history, this.dp), n, this.history));
    const TF = new TradingFirm(active.map((st, i) => new DayTrader(st, strats[i], ws, this.sched)), this.sched);
    const eps = this.tol(n);
    const res = marketMaker(TF, eps, this.history.at(-1) ?? new Map(), this.sched === FastSchedule ? () => TF.lipschitzOfGap() : null);
    const P = new Map(TF.supp.map((s, i) => [s, res.p[i]]));
    this.history.push(P);
    const g = gap(TF.eval(res.p), res.p);
    this.firmValue += g; this.sumEps += eps;
    // raw holdings, worst plausible loss M, settlement of decided sentences
    active.forEach((st, i) => {
      const sg = strats[i], s = sg.eval(P);
      sg.sents.forEach((x, q) => {
        if (s[q] !== 0) { st.H.set(x, (st.H.get(x) ?? 0) + s[q]); st.Hcash -= s[q] * (P.get(x) ?? 0); }
      });
      if (st.H.size) {
        st.M = Math.max(st.M, -ws.minLinear(st.Hcash, st.H));
        for (const { sents, vecs } of ws.components([...st.H.keys()]))
          sents.forEach((x, q) => {
            if (vecs.every(v => v[q] === vecs[0][q])) { st.Hcash += st.H.get(x) * vecs[0][q]; st.H.delete(x); }
          });
      }
    });
    this.day = n;
    return { n, d: TF.supp.length, method: res.method, evals: res.evals, gap: g, eps, oracle: COUNT.oracle, ms: performance.now() - t0 };
  }
}

// ---------------------------------------------------------------- traders (paper's feature language)
const P = Price;
const trader = (name, strategy) => ({ name, strategy });
const complementArb = phi => trader("complement " + phi.key, (n) => {
  const x = sub(sub(1, P(phi, n)), P(neg(phi), n));
  return new Map([[phi, x], [neg(phi), x]]);
});
const conjArb = (a, b) => trader("∧/∨ arbitrage", (n) => {
  const x = sub(sub(add(P(a, n), P(b, n)), P(conj(a, b), n)), P(disj(a, b), n));
  return new Map([[conj(a, b), x], [disj(a, b), x], [a, mul(-1, x)], [b, mul(-1, x)]]);
});
const provenBuyer = watch => trader("buys proven sentences", (n, h, dp) => {
  const m = new Map();
  for (const s of watch) {
    if (dp.D.has(s)) m.set(s, sub(1, P(s, n)));
    else if (dp.D.has(neg(s))) m.set(s, mul(-1, P(s, n)));
  }
  return m;
});
// buys or sells whatever D_n already decides propositionally (a small consistency check)
const decidedBuyer = watch => trader("buys decided combinations", (n, h, dp) => {
  const m = new Map();
  for (const s of watch) {
    const v = dp.ws.components([s])[0].vecs;
    if (v.every(x => x[0] === v[0][0])) m.set(s, v[0][0] ? sub(1, P(s, n)) : mul(-1, P(s, n)));
  }
  return m;
});
const informed = (f, truth) => trader("informed", n => new Map([[f(n), sub(truth(n) ? 1 : 0, P(f(n), n))]]));
const stubborn = (f, q) => trader("stubborn", n => new Map([[f(n), sub(q, P(f(n), n))]]));
const paradox = chi => trader("paradox bettor", n => new Map([[chi(n), clip(mul(sub(0.5, P(chi(n), n)), 10), -1, 1)]]));
const rotator = (a, b) => trader("rotator", n => new Map([[a, mul(sub(P(b, n), 0.5), -1)], [b, sub(P(a, n), 0.5)]]));
const expander = (a, b) => trader("expander", n => {
  const x = sub(P(a, n), 0.5), y = sub(P(b, n), 0.5);
  return new Map([[a, sub(x, y)], [b, add(x, y)]]);
});
const meanRevert = phi => trader("mean reversion", n => (n === 1 ? new Map() : new Map([[phi, mul(sub(P(phi, n - 1), P(phi, n)), 0.5)]])));
const idle = () => trader("idle", () => new Map());

// ---------------------------------------------------------------- scenarios
const fresh = i => atom(1000 + i);   // a new sentence every day
const chi = i => atom(5000 + i);     // chi_i is revealed true iff P_i(chi_i) < 1/2

function miniMath(A = 8, delay = 4) {
  const truth = i => i % 3 !== 1;
  const lit = i => (truth(i) ? atom(i) : neg(atom(i)));
  const dp = new DeductiveProcess((n, history) => {
    const out = [];
    if (n % 2 === 0 && n / 2 < A - 1) { const i = n / 2; if (truth(i) || truth(i + 1)) out.push(disj(atom(i), atom(i + 1))); }
    if (n % 5 === 0 && n / 5 - 1 < A) out.push(lit(n / 5 - 1));
    const m = n - delay;
    if (m >= 1) out.push(m % 3 !== 0 ? fresh(m) : neg(fresh(m)));
    if (n >= 2) { const c = chi(n - 1); out.push((history[n - 2].get(c) ?? 0) < 0.5 ? c : neg(c)); }
    return out;
  });
  const a = Array.from({ length: A }, (_, i) => atom(i));
  const traders = [
    complementArb(a[0]), complementArb(a[1]), complementArb(a[2]),
    conjArb(a[0], a[1]), conjArb(a[2], a[3]),
    provenBuyer([...a, ...a.slice(0, A - 1).map((x, i) => disj(x, a[i + 1]))]),
    stubborn(fresh, 0.5), informed(fresh, n => n % 3 !== 0),
    paradox(chi), rotator(a[4], a[5]), expander(a[6], a[7]), meanRevert(a[3]),
    decidedBuyer([neg(a[0]), conj(a[0], a[1]), disj(a[0], a[1]), conj(a[2], a[3]), disj(a[2], a[3])]),
  ];
  return { traders, dp, truth };
}

function duel(k, delay = 3) {
  const dp = new DeductiveProcess(n => (n - delay >= 1 ? [fresh(n - delay)] : []));
  const traders = [stubborn(fresh, 0.5), ...Array.from({ length: k - 2 }, idle), informed(fresh, () => true)];
  return { traders, dp };
}

if (typeof module !== "undefined") module.exports = { atom, neg, conj, disj, gap, maxOverAllWorlds, Market, miniMath, duel, fresh, chi, FastSchedule, PaperSchedule };
