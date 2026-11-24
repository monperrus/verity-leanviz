'use strict';
//
// The architecture of a project, computed in the page from what every bundle already carries: the module table
// and graph.bin. Pure functions only, no DOM and no fetch, so `node --test tests/arch.test.mjs` exercises the
// same code the page runs, and tools/arch.mjs runs it on a bundle on disk. Loaded as a plain script before
// app.js; in Node, the same functions are exported.
//
// Two questions an engineer asks of a large project, answered here:
// - How do its parts depend on each other? `areaGraph` sums declaration references between the areas one level
//   below a module prefix. Modules cannot import in a cycle, but areas can reference each other both ways, and
//   in agent-written code they do (verity's Verity, Compiler and Contracts all reach into each other), so
//   `feedbackOrder` finds the order that goes against the fewest references, `backEdges` names the ones it goes
//   against, and `columns` places what is used left of what uses it along the rest.
// - What carries the main results? `dominators` computes, from chosen roots, the dominator tree of the reference
//   graph: X owns Y when every chain of references from the roots to Y passes through X, so what X owns exists
//   only to serve X (Cooper, Harvey and Kennedy, "A Simple, Fast Dominance Algorithm", 2001).

// Names the elaborator makes up: proofs split out of a definition, equation lemmas, sizeOf lemmas, matchers,
// compiler stages. They are real declarations, so they stay in the data, but a reader rarely wants them.
// `.eq_1` and `.eq_def` are equation lemmas with a dot rather than an underscore, so the underscore forms
// below missed them; they were the bulk of every pair of declarations sharing a statement.
const GENERATED = /(^|\.)(_proof_\d+|_simp_\d+|_eq_\d+|eq_\d+|eq_def|_unfold|_sizeOf_\d+|sizeOf_spec|_cstage\d*|_spec_\d+|_elambda_\d+|_private|_aux_\d+|match_\d+|proof_\d+|_sparseCasesOn_\d+|_closed_\d+|_lambda_\d+|_rarg|_redArg|_boxed|_override|_hyg\.\d+|injEq|_lemma_\d+|_f|_g)($|\.)|✝/;
const isGenerated = (name) => GENERATED.test(name) || /\.\d+$/.test(name);

/** The area a module falls in one level below `prefix` ('' for the top), or null when it is not under it. */
function areaOf(moduleName, prefix) {
  if (!prefix) return moduleName.split('.')[0];
  if (moduleName === prefix) return '';
  if (!moduleName.startsWith(prefix + '.')) return null;
  return moduleName.slice(prefix.length + 1).split('.')[0];
}

/**
 * Areas below `prefix` and the references between them.
 *
 * `modules` is the bundle's module table ({n, s, c}), `moduleIdx` the indices of the modules to consider (the
 * project's own), `g` the graph ({fOff, fTo}) and `keep(id)` says whether a declaration counts (the page passes
 * its generated-helper filter). A declaration in the module that is exactly `prefix` belongs to the area ''.
 *
 * Returns `areas`: Map name -> {decls, modules}, `edges`: Map "from\tto" -> number of references, counting each
 * (declaration, referenced declaration) pair once and only between different areas, and `examples`: Map
 * "from\tto" -> up to `examples` such pairs [id, referenced id], the first in id order, so a reader can see which
 * declarations make an edge.
 */
function areaGraph(g, modules, moduleIdx, prefix, keep = () => true, examples = 0) {
  const areaOfModule = new Map();
  const areas = new Map();
  for (const mi of moduleIdx) {
    const a = areaOf(modules[mi].n, prefix);
    if (a === null) continue;
    areaOfModule.set(mi, a);
    if (!areas.has(a)) areas.set(a, { decls: 0, modules: 0 });
    areas.get(a).modules++;
  }
  // id -> area, through the module ranges; ids outside the considered modules map to undefined
  const ranges = [...areaOfModule.keys()].map(mi => [modules[mi].s, modules[mi].s + modules[mi].c, areaOfModule.get(mi)])
    .sort((x, y) => x[0] - y[0]);
  const starts = ranges.map(r => r[0]);
  const areaOfId = (id) => {
    let lo = 0, hi = starts.length - 1, at = -1;
    while (lo <= hi) {
      const mid = (lo + hi) >> 1;
      if (starts[mid] <= id) { at = mid; lo = mid + 1; } else hi = mid - 1;
    }
    return at >= 0 && id < ranges[at][1] ? ranges[at][2] : undefined;
  };
  const edges = new Map();
  const shown = new Map();
  for (const [lo, hi, a] of ranges) {
    for (let id = lo; id < hi; id++) {
      if (!keep(id)) continue;
      areas.get(a).decls++;
      for (let e = g.fOff[id]; e < g.fOff[id + 1]; e++) {
        const t = g.fTo[e];
        const b = areaOfId(t);
        if (b === undefined || b === a) continue;
        const k = a + '\t' + b;
        edges.set(k, (edges.get(k) || 0) + 1);
        if (examples) {
          if (!shown.has(k)) shown.set(k, []);
          if (shown.get(k).length < examples) shown.get(k).push([id, t]);
        }
      }
    }
  }
  return { areas, edges, examples: shown };
}

/**
 * An order of `nodes` in which users come before what they use, going against as few references as possible.
 * `edges` is a Map "a\tb" -> weight, meaning a uses b. Returns Map node -> position. Up to EXACT_LIMIT nodes the
 * order is optimal (`exactOrder`); beyond, it is the greedy heuristic (`greedyOrder`), which can be a little worse:
 * on verity's three top areas it goes against 1,257 references where the best order goes against 1,202.
 */
const EXACT_LIMIT = 16;
function feedbackOrder(nodes, edges) {
  return nodes.length <= EXACT_LIMIT ? exactOrder(nodes, edges) : greedyOrder(nodes, edges);
}

/**
 * The order with the least total weight against it, by dynamic programming over subsets: cost[S] is the least weight
 * against an order that places the set S first, and appending v after S goes against every edge from v into S.
 * 2^n * n steps, a few milliseconds at n = 16. Ties keep the order of the sorted names.
 */
function exactOrder(nodes, edges) {
  const vs = [...nodes].sort();
  const n = vs.length;
  const at = new Map(vs.map((v, i) => [v, i]));
  const w = Array.from({ length: n }, () => new Float64Array(n)); // w[a][b]: weight of a uses b
  for (const [k, x] of edges) {
    const [a, b] = k.split('\t');
    if (at.has(a) && at.has(b) && a !== b) w[at.get(a)][at.get(b)] = x;
  }
  const full = (1 << n) - 1;
  const cost = new Float64Array(full + 1).fill(Infinity);
  const prev = new Int32Array(full + 1).fill(-1);
  cost[0] = 0;
  for (let s = 0; s < full; s++) {
    if (cost[s] === Infinity) continue;
    for (let v = 0; v < n; v++) {
      if (s & (1 << v)) continue;
      let c = cost[s];
      for (let u = 0; u < n; u++) if (s & (1 << u)) c += w[v][u];
      const t = s | (1 << v);
      if (c < cost[t]) { cost[t] = c; prev[t] = v; }
    }
  }
  const order = [];
  for (let s = full; s; s &= ~(1 << prev[s])) order.unshift(vs[prev[s]]);
  return new Map(order.map((v, i) => [v, i]));
}

/**
 * The weighted greedy heuristic of Eades, Lin and Smyth ("A fast and effective heuristic for the feedback arc set
 * problem", 1993). Nodes nothing alive uses are taken first, nodes that use nothing alive last, and when neither
 * exists, the node whose outgoing references most exceed its incoming ones goes first. Ties break by name, so the
 * order is the same on every visit.
 */
function greedyOrder(nodes, edges) {
  const out = new Map(nodes.map(v => [v, new Map()]));
  const inn = new Map(nodes.map(v => [v, new Map()]));
  for (const [k, w] of edges) {
    const [a, b] = k.split('\t');
    if (out.has(a) && out.has(b) && a !== b) { out.get(a).set(b, w); inn.get(b).set(a, w); }
  }
  const alive = new Set(nodes);
  const weight = (m) => { let s = 0; for (const [v, w] of m) if (alive.has(v)) s += w; return s; };
  const sorted = () => [...alive].sort();
  const first = [], last = [];
  while (alive.size) {
    for (let changed = true; changed;) {
      changed = false;
      for (const v of sorted()) {
        if (weight(out.get(v)) === 0) { last.unshift(v); alive.delete(v); changed = true; }
      }
      for (const v of sorted()) {
        if (weight(inn.get(v)) === 0) { first.push(v); alive.delete(v); changed = true; }
      }
    }
    if (!alive.size) break;
    let best = null, bestDelta = -Infinity;
    for (const v of sorted()) {
      const delta = weight(out.get(v)) - weight(inn.get(v));
      if (delta > bestDelta) { best = v; bestDelta = delta; }
    }
    first.push(best);
    alive.delete(best);
  }
  return new Map([...first, ...last].map((v, i) => [v, i]));
}

/** The edges that go against `order`: from a node to one placed before it, which a layered drawing cannot point right. */
function backEdges(edges, order) {
  const back = new Set();
  for (const k of edges.keys()) {
    const [a, b] = k.split('\t');
    if (order.has(a) && order.has(b) && order.get(a) > order.get(b)) back.add(k);
  }
  return back;
}

/**
 * A column per node along the edges that are not in `back`: 0 for a node that uses no other, else one more than the
 * highest column among the nodes it uses. What is used therefore sits left of what uses it.
 */
function columns(nodes, edges, back) {
  const succ = new Map(nodes.map(v => [v, []]));
  for (const k of edges.keys()) {
    if (back.has(k)) continue;
    const [a, b] = k.split('\t');
    if (succ.has(a) && succ.has(b)) succ.get(a).push(b);
  }
  const col = new Map();
  for (const root of nodes) {
    if (col.has(root)) continue;
    const work = [[root, 0]];
    const onPath = new Set([root]);
    while (work.length) {
      const top = work[work.length - 1];
      const [v, i] = top;
      const out = succ.get(v);
      if (i < out.length) {
        top[1]++;
        const w = out[i];
        if (!col.has(w)) {
          if (onPath.has(w)) throw new Error(`columns: ${v} -> ${w} closes a cycle; pass it in back`);
          onPath.add(w);
          work.push([w, 0]);
        }
        continue;
      }
      work.pop();
      onPath.delete(v);
      col.set(v, out.reduce((m, w) => Math.max(m, col.get(w) + 1), 0));
    }
  }
  return col;
}

/**
 * How many pairs of edges cross in a drawing with `rows` (an array of columns, each an array of nodes top to bottom),
 * counting only edges between adjacent columns, the ones drawn as plain curves: two such edges between the same
 * pair of columns cross when their ends are in opposite orders. Longer edges bow around the boxes and are left out.
 */
function crossings(rows, edges) {
  const at = new Map();
  rows.forEach((c, ci) => c.forEach((v, ri) => at.set(v, [ci, ri])));
  const byGap = new Map();
  for (const k of edges.keys()) {
    const [a, b] = k.split('\t');
    if (!at.has(a) || !at.has(b)) continue;
    let [ca, ra] = at.get(a), [cb, rb] = at.get(b);
    if (Math.abs(ca - cb) !== 1) continue;
    if (ca > cb) [ca, ra, cb, rb] = [cb, rb, ca, ra];
    if (!byGap.has(ca)) byGap.set(ca, []);
    byGap.get(ca).push([ra, rb]);
  }
  let n = 0;
  for (const segs of byGap.values()) {
    for (let i = 0; i < segs.length; i++) {
      for (let j = i + 1; j < segs.length; j++) {
        if ((segs[i][0] - segs[j][0]) * (segs[i][1] - segs[j][1]) < 0) n++;
      }
    }
  }
  return n;
}

/**
 * Reorders the nodes within each column to cut crossings: the barycenter heuristic of Sugiyama, Tagawa and Toda,
 * sweeping left to right and back, each node moving to the mean row of its neighbours in other columns (weighted
 * by references), ties kept in the given order. Returns the best arrangement seen, the given one included, so it
 * never has more crossings than its input.
 */
function orderRows(rows, edges, sweeps = 8) {
  const nb = new Map();
  rows.flat().forEach(v => nb.set(v, []));
  for (const [k, w] of edges) {
    const [a, b] = k.split('\t');
    if (!nb.has(a) || !nb.has(b) || a === b) continue;
    nb.get(a).push([b, w]);
    nb.get(b).push([a, w]);
  }
  let cur = rows.map(c => [...c]);
  let best = cur.map(c => [...c]), bestN = crossings(best, edges);
  const reorder = (ci) => {
    const row = new Map();
    cur.forEach(c => c.forEach((v, ri) => row.set(v, ri)));
    const col = cur[ci];
    const key = new Map(col.map((v, ri) => {
      const ns = nb.get(v).filter(([u]) => !col.includes(u));
      const tw = ns.reduce((s, [, w]) => s + w, 0);
      return [v, tw ? ns.reduce((s, [u, w]) => s + w * row.get(u), 0) / tw : ri];
    }));
    cur[ci] = col.map((v, ri) => [v, ri]).sort((x, y) => key.get(x[0]) - key.get(y[0]) || x[1] - y[1]).map(([v]) => v);
  };
  for (let s = 0; s < sweeps; s++) {
    const order = s % 2 === 0 ? cur.map((_, i) => i) : cur.map((_, i) => cur.length - 1 - i);
    for (const ci of order) reorder(ci);
    const n = crossings(cur, edges);
    if (n < bestN) { best = cur.map(c => [...c]); bestN = n; }
  }
  return best;
}

/**
 * The dominator tree of the reference graph below `roots`, restricted to ids for which `inside(id)` holds.
 *
 * Returns {nodes, idom, owned}: `nodes` the reachable ids in reverse postorder (roots first), `idom` a Map id ->
 * immediate dominator id, or -1 for a node only the virtual root above all `roots` dominates, and `owned` a Map
 * id -> how many nodes it dominates, itself included.
 */
function dominators(g, roots, inside = () => true) {
  // depth-first postorder from a virtual root, -1, whose successors are the roots
  const post = [];
  const seen = new Set();
  const succOf = (v) => {
    if (v === -1) return roots;
    const out = [];
    for (let e = g.fOff[v]; e < g.fOff[v + 1]; e++) {
      const t = g.fTo[e];
      if (t !== v && inside(t)) out.push(t);
    }
    return out;
  };
  const work = [[-1, succOf(-1), 0]];
  seen.add(-1);
  while (work.length) {
    const top = work[work.length - 1];
    const [v, out, i] = top;
    if (i < out.length) {
      top[2]++;
      const w = out[i];
      if (!seen.has(w)) { seen.add(w); work.push([w, succOf(w), 0]); }
      continue;
    }
    work.pop();
    post.push(v);
  }
  const po = new Map(post.map((v, k) => [v, k]));
  const preds = new Map(post.map(v => [v, []]));
  for (const v of post) for (const w of succOf(v)) if (po.has(w)) preds.get(w).push(v);
  const idom = new Map([[-1, -1]]);
  const rpo = [...post].reverse();
  const intersect = (a, b) => {
    while (a !== b) {
      while (po.get(a) < po.get(b)) a = idom.get(a);
      while (po.get(b) < po.get(a)) b = idom.get(b);
    }
    return a;
  };
  for (let changed = true; changed;) {
    changed = false;
    for (const v of rpo) {
      if (v === -1) continue;
      let d;
      for (const p of preds.get(v)) {
        if (!idom.has(p)) continue;
        d = d === undefined ? p : intersect(p, d);
      }
      if (d !== undefined && idom.get(v) !== d) { idom.set(v, d); changed = true; }
    }
  }
  // subtree sizes, summed bottom-up over the dominator tree, deepest first
  const owned = new Map(post.map(v => [v, 1]));
  const depth = new Map([[-1, 0]]);
  const depthOf = (v) => {
    const chain = [];
    for (let u = v; !depth.has(u); u = idom.get(u)) chain.push(u);
    for (let k = chain.length - 1; k >= 0; k--) depth.set(chain[k], depth.get(idom.get(chain[k])) + 1);
    return depth.get(v);
  };
  const byDepth = post.filter(v => v !== -1).sort((a, b) => depthOf(b) - depthOf(a));
  for (const v of byDepth) {
    const p = idom.get(v);
    owned.set(p, owned.get(p) + owned.get(v));
  }
  owned.delete(-1);
  idom.delete(-1);
  return { nodes: rpo.filter(v => v !== -1), idom, owned };
}

if (typeof module !== 'undefined') {
  module.exports = { isGenerated, areaOf, areaGraph, feedbackOrder, exactOrder, greedyOrder, backEdges, columns, crossings, orderRows, dominators };
}
