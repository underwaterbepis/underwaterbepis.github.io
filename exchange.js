// ================================================================ the Arithmetic Exchange
// Facts about numbers are listed each day, traders bet on them, and a slow prover settles
// the bets a few days later.  Prices come from LIA-fast (the engine above).

// ---------------------------------------------------------------- number theory
function rng32(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97];
function modpow(b, e, m) {
  let r = 1n; b %= m;
  while (e > 0n) { if (e & 1n) r = (r * b) % m; b = (b * b) % m; e >>= 1n; }
  return r;
}
// deterministic Miller-Rabin, exact for n < 3.3e24
function isPrime(n) {
  n = BigInt(n);
  if (n < 2n) return false;
  const bases = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n];
  for (const p of bases) { if (n === p) return true; if (n % p === 0n) return false; }
  let d = n - 1n, s = 0;
  while ((d & 1n) === 0n) { d >>= 1n; s++; }
  for (const a of bases) {
    let x = modpow(a, d, n);
    if (x === 1n || x === n - 1n) continue;
    let composite = true;
    for (let r = 1; r < s; r++) { x = (x * x) % n; if (x === n - 1n) { composite = false; break; } }
    if (composite) return false;
  }
  return true;
}
// smallest prime factor among primes <= bound (0 if none, or if n itself is that prime)
function smallFactor(n, bound) {
  for (const p of SMALL_PRIMES) { if (p > bound) break; if (n !== p && n % p === 0) return p; }
  return 0;
}
// product over primes p <= bound of p/(p-1): how much surviving a sieve raises the odds
const sieveBoost = bound => SMALL_PRIMES.filter(p => p <= bound).reduce((acc, p) => (acc * p) / (p - 1), 1);
function collatzSteps(m) { let s = 0; while (m !== 1) { m = m % 2 === 0 ? m / 2 : 3 * m + 1; s++; } return s; }
// decimal digits of pi by the Rabinowitz-Wagon spigot: PI[k] is the k-th digit after the point
function piDigits(n) {
  const len = Math.floor((10 * (n + 2)) / 3) + 1, a = new Array(len).fill(2), out = [];
  let nines = 0, pre = 0;
  for (let j = 0; j < n + 2; j++) {
    let q = 0;
    for (let i = len; i > 0; i--) { const x = 10 * a[i - 1] + q * i; a[i - 1] = x % (2 * i - 1); q = Math.floor(x / (2 * i - 1)); }
    a[0] = q % 10; q = Math.floor(q / 10);
    if (q === 9) nines++;
    else if (q === 10) { out.push(pre + 1); for (let k = 0; k < nines; k++) out.push(0); pre = 0; nines = 0; }
    else { out.push(pre); pre = q; for (let k = 0; k < nines; k++) out.push(9); nines = 0; }
  }
  return out.slice(2);   // drop the leading 0 and the 3
}

// ---------------------------------------------------------------- facts
const FAMILIES = {
  prime: { label: "Primes", perDay: 8 },
  pi: { label: "Digits of π", perDay: 2 },
  collatz: { label: "Collatz", perDay: 2 },
};
const COLLATZ_T = 110;

class Exchange {
  constructor(traderSpecs, seed = 20161) {
    this.rng = rng32(seed);
    this.items = new Map();          // sentence -> fact
    this.byDay = new Map();          // day -> facts listed that day
    this.dueOn = new Map();          // day -> facts the prover settles that day
    this.resolved = [];
    this.stats = { prime: new Map(), collatz: [0, 0] };   // what the learners have seen
    this.nextAtom = 0;
    this.queue = [];                  // facts a visitor asked about, listed tomorrow
    this.specs = traderSpecs;
    const dp = new DeductiveProcess(n => {
      const out = [];
      for (const f of this.dueOn.get(n) || []) {
        out.push(f.truth ? f.s : neg(f.s));
        f.settled = n;
        this.learn(f);
        this.resolved.push(f);
      }
      return out;
    });
    this.market = new Market(traderSpecs.map(spec => this.makeTrader(spec)), dp);
  }
  get day() { return this.market.day; }
  primeBucket(n) { return (smallFactor(n, 7) ? "x" : "s") + Math.floor(Math.log10(n)); }
  learn(f) {
    if (f.family === "prime") {
      const b = this.primeBucket(f.n), c = this.stats.prime.get(b) || [0, 0];
      c[0] += f.truth ? 1 : 0; c[1] += 1; this.stats.prime.set(b, c);
    } else if (f.family === "collatz") { this.stats.collatz[0] += f.truth ? 1 : 0; this.stats.collatz[1] += 1; }
  }
  fact(family, data, day) {
    const s = atom(this.nextAtom++);
    const f = { s, family, day, ...data };
    this.items.set(s, f);
    if (!this.byDay.has(day)) this.byDay.set(day, []);
    this.byDay.get(day).push(f);
    if (!this.dueOn.has(f.due)) this.dueOn.set(f.due, []);
    this.dueOn.get(f.due).push(f);
    return f;
  }
  primeFact(n, day, asked = false) {
    return this.fact("prime", { n, truth: isPrime(n), due: day + 2 + Math.floor(Math.log10(n) / 2), asked,
      text: n.toLocaleString("en-US") + " is prime" }, day);
  }
  listFacts(day) {
    const r = this.rng;
    for (const n of this.queue.splice(0)) this.primeFact(n, day, true);
    for (let i = 0; i < FAMILIES.prime.perDay; i++) this.primeFact(Math.floor(10 ** (3 + 5 * r())), day);
    for (let i = 0; i < FAMILIES.pi.perDay; i++) {
      const k = 1 + Math.floor(PI.length * r()), d = Math.floor(10 * r());
      this.fact("pi", { k, d, truth: PI[k - 1] === d, due: day + 3, text: "digit " + k + " of π is " + d }, day);
    }
    for (let i = 0; i < FAMILIES.collatz.perDay; i++) {
      const m = 10000 + Math.floor(990000 * r());
      this.fact("collatz", { m, truth: collatzSteps(m) > COLLATZ_T, due: day + 2,
        text: m.toLocaleString("en-US") + " takes more than " + COLLATZ_T + " Collatz steps" }, day);
    }
  }
  // a trader is a heuristic opinion(fact) -> probability, traded linearly: c * (opinion - price)
  makeTrader(spec) {
    const ex = this;
    return {
      name: spec.name,
      strategy(n) {
        const m = new Map();
        for (const f of ex.byDay.get(n) || []) {
          if (f.family !== spec.family) continue;
          const q = spec.opinion(f, ex);
          if (q !== null) m.set(f.s, mul(sub(q, Price(f.s, n)), spec.c ?? 0.25));
        }
        return m;
      },
    };
  }
  step() {
    const n = this.market.day + 1;
    this.listFacts(n);
    const rec = this.market.step();       // the prover reveals day n's facts first, so learners see them
    const P = this.market.history[n - 1];
    for (const f of this.byDay.get(n) || []) {
      f.price = P.get(f.s) ?? 0;
      f.opinions = this.specs.map(sp => (sp.family === f.family ? sp.opinion(f, this) : null));
    }
    return rec;
  }
  // each trader's say in today's prices: v_k * (budget mass still alive), normalised per family
  shares() {
    const w = this.market.states.map(st => this.market.sched.traderWeight(st.k) * this.market.sched.tail(this.market.sched.firstAlive(st.M)) * (this.specs[st.k - 1].c ?? 0.25));
    const tot = {};
    this.specs.forEach((sp, i) => { tot[sp.family] = (tot[sp.family] || 0) + w[i]; });
    return this.specs.map((sp, i) => w[i] / tot[sp.family]);
  }
  // price a fact right now without trading on it: the fixed point of the current firm on one sentence
  quote(f) {
    const n = this.market.day + 1, m = this.market, ws = m.dp.ws;
    const dts = [];
    m.states.forEach((st, i) => {
      const sp = this.specs[i];
      if (sp.family !== f.family) return;
      const q = sp.opinion(f, this);
      if (q === null) return;
      const strat = new Strategy(new Map([[f.s, mul(sub(q, Price(f.s, n)), sp.c ?? 0.25)]]), n, m.history);
      dts.push(new DayTrader(st, strat, ws, m.sched));
    });
    if (!dts.length) return null;
    const TF = new TradingFirm(dts, m.sched);
    return mmBisect1d(p => TF.eval(p), 1e-9)[0];
  }
}

// ---------------------------------------------------------------- the traders
const ln = Math.log;
const clamp01 = x => Math.max(0, Math.min(1, x));
const TRADERS = [
  { id: "pnt", family: "prime", name: "Prime number theorem", about: "Any n is prime with probability 1/ln n.",
    opinion: f => clamp01(1 / ln(f.n)) },
  { id: "parity", family: "prime", name: "Parity", about: "Even numbers above 2 are composite; odd ones are prime with probability 2/ln n.",
    opinion: f => (f.n === 2 ? 1 : f.n % 2 === 0 ? 0 : clamp01(2 / ln(f.n))) },
  { id: "optimist", family: "prime", name: "Optimist", about: "A bad heuristic: odd numbers are prime 90% of the time.",
    opinion: f => (f.n % 2 === 0 ? 0 : 0.9) },
  { id: "sieve7", family: "prime", name: "Sieve to 7", about: "Divides by 2, 3, 5 and 7. Survivors are prime with probability 4.375/ln n.",
    opinion: f => ([2, 3, 5, 7].includes(f.n) ? 1 : smallFactor(f.n, 7) ? 0 : clamp01(sieveBoost(7) / ln(f.n))) },
  { id: "sieve97", family: "prime", name: "Sieve to 97", about: "Trial division by every prime up to 97. Survivors below 97² are certainly prime; above, about 8.2/ln n.",
    opinion: f => (SMALL_PRIMES.includes(f.n) ? 1 : smallFactor(f.n, 97) ? 0 : f.n < 9409 ? 1 : clamp01(sieveBoost(97) / ln(f.n))) },
  { id: "learner", family: "prime", name: "Frequency learner", about: "Sieves to 7, then uses the prime rate it has seen among settled numbers of the same size.",
    opinion: (f, ex) => {
      if ([2, 3, 5, 7].includes(f.n)) return 1;
      if (smallFactor(f.n, 7)) return 0;
      const c = ex.stats.prime.get(ex.primeBucket(f.n)) || [0, 0];
      return (c[0] + 1) / (c[1] + 2);
    } },
  { id: "mr", family: "prime", name: "Miller–Rabin", about: "Runs a primality test. Exact, and polynomial-time, so a logical inductor must learn to trust it.",
    opinion: f => (isPrime(f.n) ? 1 : 0), optional: true },
  { id: "uniform", family: "pi", name: "Uniform digits", about: "Every digit of π is equally likely: 1/10.", opinion: () => 0.1 },
  { id: "sevens", family: "pi", name: "Lucky sevens", about: "A bad heuristic: π likes the digit 7 (40%), so other digits get 6.7%.",
    opinion: f => (f.d === 7 ? 0.4 : 0.6 / 9) },
  { id: "spigot", family: "pi", name: "Computes π", about: "Runs a spigot algorithm for the digit. Exact at these positions.",
    opinion: f => (PI[f.k - 1] === f.d ? 1 : 0), optional: true },
  { id: "coin", family: "collatz", name: "Coin flip", about: "No idea: 50%.", opinion: () => 0.5 },
  { id: "rate", family: "collatz", name: "Base-rate learner", about: "Uses the fraction of settled numbers that took more than " + COLLATZ_T + " steps.",
    opinion: (f, ex) => (ex.stats.collatz[0] + 1) / (ex.stats.collatz[1] + 2) },
  { id: "runner", family: "collatz", name: "Runs the sequence", about: "Iterates 3n+1 until it reaches 1. Exact and cheap.",
    opinion: f => (collatzSteps(f.m) > COLLATZ_T ? 1 : 0) },
];
const PI = piDigits(3200);
