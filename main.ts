// Sokoban solver: room-decomposition push-optimal A*.
//
// Strategy: every level is a 1-wide hallway plus 1-4 rooms (each in a 6x6
// slot, one door, 3-4 boxes). Boxes can never leave their room, so the
// level's push-optimal count is the sum of the rooms' optima. Each room is
// solved push-optimally on its own (A* over pushes, player-reachability BFS
// between pushes, live-cell + 2x2 deadlock pruning, admissible assignment
// heuristic), then the rooms are stitched together with walking moves in an
// order that lets the player exit every room. A whole-level push A* is kept
// as a fallback if decomposition ever fails. All budgets are by expansion
// count, never by the clock, so runs are byte-identical.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Directions in fixed order: up, down, left, right.
const DIRS = [
  [-1, 0, 'u'],
  [1, 0, 'd'],
  [0, -1, 'l'],
  [0, 1, 'r'],
];

// Deterministic work budgets (expansion counts, not wall time).
const PER_SEARCH_CAP = 600000;
const TOTAL_CAP = 3500000;
let totalExpansions = 0;

// ---------- small binary heap (min by f, then insertion order) ----------
function heapPush(h, item) {
  h.push(item);
  let i = h.length - 1;
  while (i > 0) {
    const p = (i - 1) >> 1;
    if (h[p].f < h[i].f || (h[p].f === h[i].f && h[p].n <= h[i].n)) break;
    const t = h[p]; h[p] = h[i]; h[i] = t;
    i = p;
  }
}
function heapPop(h) {
  const top = h[0];
  const last = h.pop();
  if (h.length > 0) {
    h[0] = last;
    let i = 0;
    for (;;) {
      const l = 2 * i + 1, r = l + 1;
      let m = i;
      if (l < h.length && (h[l].f < h[m].f || (h[l].f === h[m].f && h[l].n < h[m].n))) m = l;
      if (r < h.length && (h[r].f < h[m].f || (h[r].f === h[m].f && h[r].n < h[m].n))) m = r;
      if (m === i) break;
      const t = h[m]; h[m] = h[i]; h[i] = t;
      i = m;
    }
  }
  return top;
}

// ---------- level parsing ----------
function parseLevel(text) {
  const lines = text.split(/\r?\n/);
  while (lines.length && lines[lines.length - 1] === '') lines.pop();
  const H = lines.length;
  let W = 0;
  for (const l of lines) W = Math.max(W, l.length);
  const floor = new Uint8Array(W * H);
  const boxes = [];
  const goals = new Set();
  let player = -1;
  for (let r = 0; r < H; r++) {
    for (let c = 0; c < W; c++) {
      const ch = c < lines[r].length ? lines[r][c] : '#';
      const id = r * W + c;
      if (ch === '#') continue;
      floor[id] = 1;
      if (ch === '$' || ch === '*') boxes.push(id);
      if (ch === '.' || ch === '*') goals.add(id);
      if (ch === '@' || ch === '+') player = id;
    }
  }
  boxes.sort((a, b) => a - b);
  return { W, H, floor, boxes, goals, player };
}

// ---------- grid helpers ----------
function rc(id, W) { return [Math.floor(id / W), id % W]; }
function neighbours(id, W, H) {
  const [r, c] = rc(id, W);
  const out = [];
  for (const [dr, dc] of [[-1, 0], [1, 0], [0, -1], [0, 1]]) {
    const nr = r + dr, nc = c + dc;
    if (nr >= 0 && nr < H && nc >= 0 && nc < W) out.push(nr * W + nc);
  }
  return out;
}

// BFS distances from src over a cell set (returns Int32Array, -1 = unreachable).
function bfsDist(src, cellSet, W, H) {
  const dist = new Int32Array(W * H).fill(-1);
  dist[src] = 0;
  const q = [src];
  for (let qi = 0; qi < q.length; qi++) {
    const x = q[qi];
    for (const y of neighbours(x, W, H)) {
      if (cellSet.has(y) && dist[y] < 0) { dist[y] = dist[x] + 1; q.push(y); }
    }
  }
  return dist;
}

// All goal permutations (n <= 4).
function permutations(n) {
  const out = [];
  const a = [];
  for (let i = 0; i < n; i++) a.push(i);
  const gen = (k) => {
    if (k === n) { out.push(a.slice()); return; }
    for (let i = k; i < n; i++) {
      const t = a[k]; a[k] = a[i]; a[i] = t;
      gen(k + 1);
      const t2 = a[k]; a[k] = a[i]; a[i] = t2;
    }
  };
  gen(0);
  return out;
}

// ---------- push-optimal A* over one box set ----------
// boxCells: cells boxes may occupy. walkCells: cells the player may stand on
// (boxCells plus, for a room, the hallway cell outside its door).
// Returns { moves, endPlayer, pushes } or null.
function pushAStar(level, boxCells, walkCells, initBoxes, initGoals, initPlayer) {
  const { W, H } = level;
  const goals = [...initGoals].sort((a, b) => a - b);
  const n = goals.length;
  if (initBoxes.length !== n) return null;
  const perms = permutations(n);
  // Grid distances from each goal (admissible push lower bound per box).
  const dists = goals.map((g) => bfsDist(g, boxCells, W, H));
  const heuristic = (boxes) => {
    let best = Infinity;
    for (const p of perms) {
      let s = 0;
      for (let i = 0; i < n; i++) {
        const d = dists[p[i]][boxes[i]];
        if (d < 0) { s = Infinity; break; }
        s += d;
      }
      if (s < best) best = s;
    }
    return best;
  };
  // Live cells: box positions from which a goal is reachable by reverse pushes
  // (ignoring other boxes). A box outside this set can never be solved.
  const live = new Set(goals);
  {
    const q = goals.slice();
    for (let qi = 0; qi < q.length; qi++) {
      const x = q[qi];
      const [xr, xc] = rc(x, W);
      for (const [dr, dc] of [[-1, 0], [1, 0], [0, -1], [0, 1]]) {
        const yr = xr + dr, yc = xc + dc;
        const orr = yr + dr, occ = yc + dc;
        if (yr < 0 || yr >= H || yc < 0 || yc >= W) continue;
        if (orr < 0 || orr >= H || occ < 0 || occ >= W) continue;
        const y = yr * W + yc, o = orr * W + occ;
        if (!boxCells.has(y) || !walkCells.has(o) || live.has(y)) continue;
        live.add(y);
        q.push(y);
      }
    }
  }
  const goalSet = new Set(goals);
  const isDead = (boxes, boxSet) => {
    for (const b of boxes) if (!live.has(b)) return true;
    // 2x2 frozen block: four cells all wall-or-box, holding a box off-goal.
    for (let r = 0; r + 1 < H; r++) {
      for (let c = 0; c + 1 < W; c++) {
        const cells = [r * W + c, r * W + c + 1, (r + 1) * W + c, (r + 1) * W + c + 1];
        let nb = 0, offGoal = false, allBlocked = true;
        for (const cell of cells) {
          if (boxCells.has(cell)) {
            // a box cell inside the block counts as blocked only if occupied
            if (!boxSet.has(cell)) { allBlocked = false; break; }
            nb++;
            if (!goalSet.has(cell)) offGoal = true;
          } else if (walkCells.has(cell)) { allBlocked = false; break; }
          // else: wall (or outside the room) counts as blocked
        }
        if (allBlocked && nb > 0 && offGoal) return true;
      }
    }
    return false;
  };
  const solved = (boxes) => boxes.every((b) => goalSet.has(b));
  const keyOf = (boxes, player) => boxes.join(',') + '|' + player;

  const nodes = [];
  const heap = [];
  let counter = 0;
  const startBoxes = initBoxes.slice().sort((a, b) => a - b);
  const h0 = heuristic(startBoxes);
  if (h0 === Infinity || isDead(startBoxes, new Set(startBoxes))) return null;
  nodes.push({ boxes: startBoxes, player: initPlayer, parent: -1, moves: '', g: 0 });
  heapPush(heap, { f: h0, n: counter++, idx: 0 });
  const best = new Map();
  best.set(keyOf(startBoxes, initPlayer), 0);
  let expansions = 0;
  while (heap.length) {
    const cur = heapPop(heap);
    const node = nodes[cur.idx];
    const key = keyOf(node.boxes, node.player);
    if (best.get(key) < node.g) continue;
    if (solved(node.boxes)) {
      const parts = [];
      let i = cur.idx;
      while (i >= 0) { parts.push(nodes[i].moves); i = nodes[i].parent; }
      parts.reverse();
      return { moves: parts.join(''), endPlayer: node.player, pushes: node.g };
    }
    if (++expansions > PER_SEARCH_CAP || ++totalExpansions > TOTAL_CAP) return null;
    // Player reachability BFS from node.player over walkCells, avoiding boxes.
    const boxSet = new Set(node.boxes);
    const prev = new Map();
    prev.set(node.player, null);
    const q = [node.player];
    for (let qi = 0; qi < q.length; qi++) {
      const x = q[qi];
      const [xr, xc] = rc(x, W);
      for (const [dr, dc, ch] of DIRS) {
        const nr = xr + dr, nc = xc + dc;
        if (nr < 0 || nr >= H || nc < 0 || nc >= W) continue;
        const y = nr * W + nc;
        if (!walkCells.has(y) || boxSet.has(y) || prev.has(y)) continue;
        prev.set(y, [x, ch]);
        q.push(y);
      }
    }
    const walkTo = (target) => {
      if (!prev.has(target)) return null;
      const chars = [];
      let x = target;
      while (prev.get(x) !== null) {
        const [p, ch] = prev.get(x);
        chars.push(ch);
        x = p;
      }
      chars.reverse();
      return chars.join('');
    };
    for (let bi = 0; bi < node.boxes.length; bi++) {
      const b = node.boxes[bi];
      const [br, bc] = rc(b, W);
      for (const [dr, dc, ch] of DIRS) {
        const tr = br + dr, tc = bc + dc;
        const pr = br - dr, pc = bc - dc;
        if (tr < 0 || tr >= H || tc < 0 || tc >= W) continue;
        if (pr < 0 || pr >= H || pc < 0 || pc >= W) continue;
        const target = tr * W + tc, from = pr * W + pc;
        if (!boxCells.has(target) || boxSet.has(target)) continue;
        const walk = walkTo(from);
        if (walk === null) continue;
        const nb = node.boxes.slice();
        nb[bi] = target;
        nb.sort((a, b2) => a - b2);
        if (isDead(nb, new Set(nb))) continue;
        const g2 = node.g + 1;
        const k2 = keyOf(nb, b);
        if (best.has(k2) && best.get(k2) <= g2) continue;
        best.set(k2, g2);
        const h2 = heuristic(nb);
        if (h2 === Infinity) continue;
        nodes.push({ boxes: nb, player: b, parent: cur.idx, moves: walk + ch, g: g2 });
        heapPush(heap, { f: g2 + h2, n: counter++, idx: nodes.length - 1 });
      }
    }
  }
  return null;
}

// ---------- move simulation on the full level ----------
function simulate(level, boxes, player, moves) {
  const boxSet = new Set(boxes);
  let p = player;
  for (const ch of moves) {
    const d = DIRS.find((dd) => dd[2] === ch);
    if (!d) return null;
    const [pr, pc] = rc(p, level.W);
    const nr = pr + d[0], nc = pc + d[1];
    if (nr < 0 || nr >= level.H || nc < 0 || nc >= level.W) return null;
    const nxt = nr * level.W + nc;
    if (!level.floor[nxt]) return null;
    if (boxSet.has(nxt)) {
      const br = nr + d[0], bc = nc + d[1];
      if (br < 0 || br >= level.H || bc < 0 || bc >= level.W) return null;
      const beyond = br * level.W + bc;
      if (!level.floor[beyond] || boxSet.has(beyond)) return null;
      boxSet.delete(nxt);
      boxSet.add(beyond);
    }
    p = nxt;
  }
  return { boxes: [...boxSet].sort((a, b) => a - b), player: p };
}

// Walking BFS avoiding box cells; returns move string or null.
function walkPath(level, boxes, from, to) {
  const boxSet = new Set(boxes);
  const prev = new Map();
  prev.set(from, null);
  const q = [from];
  for (let qi = 0; qi < q.length; qi++) {
    const x = q[qi];
    if (x === to) break;
    const [xr, xc] = rc(x, level.W);
    for (const [dr, dc, ch] of DIRS) {
      const nr = xr + dr, nc = xc + dc;
      if (nr < 0 || nr >= level.H || nc < 0 || nc >= level.W) continue;
      const y = nr * level.W + nc;
      if (!level.floor[y] || boxSet.has(y) || prev.has(y)) continue;
      prev.set(y, [x, ch]);
      q.push(y);
    }
  }
  if (!prev.has(to)) return null;
  const chars = [];
  let x = to;
  while (prev.get(x) !== null) {
    const [p, ch] = prev.get(x);
    chars.push(ch);
    x = p;
  }
  chars.reverse();
  return chars.join('');
}

function allPerms(arr) {
  if (arr.length <= 1) return [arr.slice()];
  const out = [];
  for (let i = 0; i < arr.length; i++) {
    const rest = arr.slice(0, i).concat(arr.slice(i + 1));
    for (const p of allPerms(rest)) out.push([arr[i], ...p]);
  }
  return out;
}

// ---------- room decomposition ----------
function solveByRooms(level) {
  const { W, H, floor } = level;
  const [pr, pc] = rc(level.player, W);
  const hallRow = pr;
  // Connected components of floor cells outside the hallway row.
  const comp = new Int32Array(W * H).fill(-1);
  const comps = [];
  for (let id = 0; id < W * H; id++) {
    if (!floor[id] || Math.floor(id / W) === hallRow || comp[id] >= 0) continue;
    const cells = [];
    const q = [id];
    comp[id] = comps.length;
    for (let qi = 0; qi < q.length; qi++) {
      const x = q[qi];
      cells.push(x);
      for (const y of neighbours(x, W, H)) {
        if (floor[y] && Math.floor(y / W) !== hallRow && comp[y] < 0) {
          comp[y] = comps.length;
          q.push(y);
        }
      }
    }
    comps.push(cells);
  }
  // Every box must sit inside exactly one component.
  const roomOfBox = new Map();
  for (const b of level.boxes) {
    if (comp[b] < 0) return null;
    roomOfBox.set(b, comp[b]);
  }
  const rooms = [];
  for (let ci = 0; ci < comps.length; ci++) {
    const cells = comps[ci];
    const rboxes = level.boxes.filter((b) => comp[b] === ci);
    if (rboxes.length === 0) continue;
    const rgoals = [...level.goals].filter((g) => comp[g] === ci);
    if (rgoals.length !== rboxes.length) return null;
    // Door: a room cell adjacent to a hallway floor cell.
    const doors = [];
    for (const cell of cells) {
      for (const y of neighbours(cell, W, H)) {
        if (Math.floor(y / W) === hallRow && floor[y]) doors.push([cell, y]);
      }
    }
    if (doors.length === 0) return null;
    doors.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    const [doorCell, entryCell] = doors[0];
    const boxCells = new Set(cells);
    const walkCells = new Set(cells);
    walkCells.add(entryCell);
    const sol = pushAStar(level, boxCells, walkCells, rboxes, new Set(rgoals), entryCell);
    if (!sol) return null;
    rooms.push({ cells, boxes: rboxes, goals: rgoals, doorCell, entryCell, sol });
  }
  if (rooms.length === 0) return null;
  // Stitch: try room orders until the player can walk between them all.
  const orderings = allPerms(rooms.map((_, i) => i));
  for (const order of orderings) {
    let boxes = level.boxes.slice();
    let player = level.player;
    let moves = '';
    let ok = true;
    for (const ri of order) {
      const room = rooms[ri];
      const walk = walkPath(level, boxes, player, room.entryCell);
      if (walk === null) { ok = false; break; }
      const s1 = simulate(level, boxes, player, walk);
      if (!s1) { ok = false; break; }
      boxes = s1.boxes; player = s1.player; moves += walk;
      const s2 = simulate(level, boxes, player, room.sol.moves);
      if (!s2) { ok = false; break; }
      boxes = s2.boxes; player = s2.player; moves += room.sol.moves;
    }
    if (!ok) continue;
    if (boxes.every((b) => level.goals.has(b))) return moves;
  }
  return null;
}

// ---------- whole-level fallback ----------
function solveWhole(level) {
  const boxCells = new Set();
  const walkCells = new Set();
  for (let id = 0; id < level.W * level.H; id++) {
    if (level.floor[id]) { boxCells.add(id); walkCells.add(id); }
  }
  const sol = pushAStar(level, boxCells, walkCells, level.boxes, level.goals, level.player);
  return sol ? sol.moves : null;
}

function solveLevel(text) {
  const level = parseLevel(text);
  if (level.player < 0 || level.boxes.length === 0) return '';
  const byRooms = solveByRooms(level);
  if (byRooms !== null) return byRooms;
  const whole = solveWhole(level);
  if (whole !== null) return whole;
  return '';
}

for (const id of readdirSync(I).sort()) {
  const moves = solveLevel(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
