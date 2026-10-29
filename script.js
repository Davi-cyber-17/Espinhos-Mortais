'use strict';

/* ===== Configuração ===== */
const COLORS = [
  { n: 'Azul', c: '#00c3f0', l: '#6fe3ff' },
  { n: 'Verde', c: '#78c93c', l: '#a2ee6a' },
  { n: 'Amarelo', c: '#fdb92b', l: '#ffe08a' },
  { n: 'Vermelho', c: '#fb625a', l: '#ff9a94' },
  { n: 'Roxo', c: '#9b5de5', l: '#c9a3f5' },
  { n: 'Laranja', c: '#ff8a2b', l: '#ffb673' }
];
const W = 30, H = 30;              // mapa 30x30 casas (antes era 4x4)
const SPEED = 5.4, R = 0.45;       // velocidade (casas/s) e raio do jogador
const WARN = 1.5, FIRE = 1.3;      // aviso vermelho e tempo com espinhos de fora (s)
const runTime = w => w === 1 ? 7 : Math.max(3, 5.5 - 0.35 * (w - 1)); // tempo andando até o aviso
const SIDES = ['top', 'bottom', 'left', 'right'];
const SIDE_TXT = { top: 'CIMA ⬇', bottom: 'BAIXO ⬆', left: 'ESQUERDA ➡', right: 'DIREITA ⬅' };
const KEYSETS = [['KeyW', 'KeyS', 'KeyA', 'KeyD'], ['ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight'], ['KeyI', 'KeyK', 'KeyJ', 'KeyL']];
const KEYHINT = ['WASD', 'Setas', 'IJKL'];
// STUN + TURN públicos: ajudam a conectar celular, computador e redes diferentes (4G, Wi-Fi, etc.)
const PEER_OPTS = { config: { iceServers: [
  { urls: 'stun:stun.l.google.com:19302' },
  { urls: 'stun:stun1.l.google.com:19302' },
  { urls: 'stun:global.stun.twilio.com:3478' },
  { urls: ['turn:openrelay.metered.ca:80', 'turn:openrelay.metered.ca:443', 'turn:openrelay.metered.ca:443?transport=tcp'], username: 'openrelayproject', credential: 'openrelayproject' }
] } };

/* ===== Mapa (paredes) ===== */
// Os espinhos vêm de um lado só e as paredes bloqueiam a passagem: a área segura é o que fica atrás delas.
const SEG_BASE = [[7, 7, 4, 1], [7, 8, 1, 3], [14, 14, 2, 2]]; // 4 cantos em L + 1 bloco no centro
function wallSet() {
  const seen = new Set(), out = [];
  SEG_BASE.forEach(([x, y, w, h]) => [[x, y], [W - x - w, y], [x, H - y - h], [W - x - w, H - y - h]].forEach(([X, Y]) => {
    const k = X + ',' + Y + ',' + w + ',' + h; if (!seen.has(k)) { seen.add(k); out.push([X, Y, w, h]); }
  }));
  return out;
}
const GRID = new Uint8Array(W * H), COV = new Uint8Array(W * H);
let SEGS = [], STONES = [], wallSig = '';
function setWalls(list) {
  SEGS = list.map(s => s.slice()); GRID.fill(0); STONES = [];
  SEGS.forEach(([x, y, w, h]) => { for (let i = 0; i < w; i++) for (let j = 0; j < h; j++) GRID[(y + j) * W + x + i] = 1; });
  for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) if (GRID[y * W + x]) STONES.push([x, y]);
}
const isStone = (x, y) => x >= 0 && y >= 0 && x < W && y < H && GRID[y * W + x] === 1;
// casas atingidas pelos espinhos: do lado de origem até a primeira parede
function buildCov(side, doom = []) {
  const G = GRID.slice(); // paredes que vão sumir já não bloqueiam: a área de perigo mostrada é a final
  doom.forEach(k => { const sg = SEGS[k]; if (sg) for (let a = 0; a < sg[2]; a++) for (let b = 0; b < sg[3]; b++) G[(sg[1] + b) * W + sg[0] + a] = 0; });
  COV.fill(0);
  if (side === 'top') for (let x = 0; x < W; x++) for (let y = 0; y < H && !G[y * W + x]; y++) COV[y * W + x] = 1;
  else if (side === 'bottom') for (let x = 0; x < W; x++) for (let y = H - 1; y >= 0 && !G[y * W + x]; y--) COV[y * W + x] = 1;
  else if (side === 'left') for (let y = 0; y < H; y++) for (let x = 0; x < W && !G[y * W + x]; x++) COV[y * W + x] = 1;
  else for (let y = 0; y < H; y++) for (let x = W - 1; x >= 0 && !G[y * W + x]; x--) COV[y * W + x] = 1;
}
setWalls(wallSet());
function hitsStone(px, py, r) {
  for (let tx = Math.floor(px - r); tx <= Math.floor(px + r); tx++) for (let ty = Math.floor(py - r); ty <= Math.floor(py + r); ty++) {
    if (!isStone(tx, ty)) continue;
    const cx = Math.max(tx, Math.min(px, tx + 1)), cy = Math.max(ty, Math.min(py, ty + 1));
    if ((px - cx) ** 2 + (py - cy) ** 2 < r * r) return true;
  }
  return false;
}
function freePos(x, y) {
  x = Math.max(R, Math.min(W - R, x)); y = Math.max(R, Math.min(H - R, y));
  if (!hitsStone(x, y, R + .15)) return [x, y];
  for (let d = .5; d < 8; d += .5) for (let a = 0; a < 6.28; a += .5) {
    const nx = x + Math.cos(a) * d, ny = y + Math.sin(a) * d;
    if (nx > R && ny > R && nx < W - R && ny < H - R && !hitsStone(nx, ny, R + .15)) return [nx, ny];
  }
  return [W / 2, H / 2];
}

/* ===== Estado ===== */
const $ = s => document.querySelector(s);
let mode = null, isHost = false, me = 0, S = null, unionKeys = true, localSpecs = [];
let peer = null, hostConn = null, lobby = [], roomCode = '';
let cfg = { h: 1, b: 3 };
const keys = new Set(); let stick = [0, 0];

const show = id => document.querySelectorAll('.screen').forEach(s => s.classList.toggle('active', s.id === id));
const esc = s => String(s).replace(/[&<>"']/g, c => '&#' + c.charCodeAt(0) + ';');
const shuffle = a => { for (let i = a.length - 1; i > 0; i--) { const j = Math.random() * (i + 1) | 0; [a[i], a[j]] = [a[j], a[i]]; } return a; };
const aliveIdx = () => S.players.map((_, i) => i).filter(i => S.players[i].alive);
const msg = t => { $('#onlineMsg').textContent = t || ''; };
const nm = () => $('#name').value.trim() || 'Jogador';

/* ===== Regras (rodam no host ou no modo local) ===== */
function newGame(specs, gone = []) {
  const n = specs.length;
  setWalls(wallSet());
  S = {
    ph: 'run', w: 1, tl: 0, tm: 0, side: SIDES[Math.random() * 4 | 0], doom: [], win: null,
    players: specs.map((s, i) => {
      const a = -Math.PI / 2 + i * 2 * Math.PI / n;
      const [x, y] = freePos(W / 2 + 11 * Math.cos(a), H / 2 + 11 * Math.sin(a));
      return { n: s.n, kind: s.kind, kb: s.kb === undefined ? -1 : s.kb, bot: s.kind === 'bot', x, y, ix: 0, iy: 0, alive: !gone[i] };
    })
  };
  buildCov(S.side, []);
  S.tl = S.tm = runTime(1);
  planBots();
  resetVis();
  broadcast();
}

function bfs(sx, sy) {
  const f = new Int16Array(W * H).fill(-1), q = [sy * W + sx]; f[q[0]] = 0;
  for (let h = 0; h < q.length; h++) {
    const c = q[h], cx = c % W, cy = (c / W) | 0;
    for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
      if (!dx && !dy) continue;
      const nx = cx + dx, ny = cy + dy;
      if (nx < 0 || ny < 0 || nx >= W || ny >= H || GRID[ny * W + nx] || f[ny * W + nx] >= 0) continue;
      if (dx && dy && (GRID[cy * W + nx] || GRID[ny * W + cx])) continue;
      f[ny * W + nx] = f[c] + 1; q.push(ny * W + nx);
    }
  }
  return f;
}

// lugar seguro: fora do caminho dos espinhos (com folga dos lados, se possível)
function safeSpot(x, y, margin) {
  const i = y * W + x; if (GRID[i] || COV[i]) return false;
  if (!margin) return true;
  const lat = (S.side === 'top' || S.side === 'bottom') ? [[1, 0], [-1, 0]] : [[0, 1], [0, -1]];
  return lat.every(([dx, dy]) => { const nx = x + dx, ny = y + dy; return nx < 0 || ny < 0 || nx >= W || ny >= H || GRID[ny * W + nx] || !COV[ny * W + nx]; });
}

function planBots() {
  const claimed = new Set();
  shuffle(aliveIdx().filter(i => S.players[i].bot)).forEach(i => {
    const b = S.players[i], d = bfs(b.x | 0, b.y | 0);
    let best = -1, bd = 1e9;
    for (const margin of [true, false]) {
      for (let t = 0; t < W * H; t++) {
        if (d[t] < 0 || d[t] >= bd || claimed.has(t) || !safeSpot(t % W, (t / W) | 0, margin)) continue;
        best = t; bd = d[t];
      }
      if (best >= 0) break;
    }
    b.delay = .15 + Math.random() * .9;
    if (best < 0 || Math.random() < .15) { b.field = null; b.tx = b.x; b.ty = b.y; return; } // às vezes o robô erra
    claimed.add(best);
    const tx = best % W, ty = (best / W) | 0;
    b.tx = tx + .5 + (Math.random() - .5) * .3; b.ty = ty + .5 + (Math.random() - .5) * .3;
    b.field = bfs(tx, ty);
  });
}

function botThink(dt) {
  S.players.forEach(b => {
    if (!b.alive || !b.bot) return;
    if (b.delay > 0) { b.delay -= dt; b.ix = b.iy = 0; return; }
    if (!b.field) { b.ix = b.iy = 0; return; }
    const tx = b.x | 0, ty = b.y | 0, f = b.field, cur = f[ty * W + tx];
    let ax = b.tx, ay = b.ty;
    if (cur > 0) {
      let bv = cur, nx = -1, ny = -1;
      for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
        const X = tx + dx, Y = ty + dy;
        if ((!dx && !dy) || X < 0 || Y < 0 || X >= W || Y >= H) continue;
        if (dx && dy && (GRID[ty * W + X] || GRID[Y * W + tx])) continue;
        const v = f[Y * W + X]; if (v >= 0 && v < bv) { bv = v; nx = X; ny = Y; }
      }
      if (nx >= 0) { ax = nx + .5; ay = ny + .5; }
    }
    const dx = ax - b.x, dy = ay - b.y, d = Math.hypot(dx, dy);
    if (d > .15) { const k = Math.min(1, d / .6); b.ix = dx / d * k; b.iy = dy / d * k; } else { b.ix = b.iy = 0; }
  });
}

function kbVector(slot, union) {
  let x = 0, y = 0;
  for (const s of (union ? [0, 1] : [slot])) {
    const k = KEYSETS[s];
    if (keys.has(k[0])) y--; if (keys.has(k[1])) y++; if (keys.has(k[2])) x--; if (keys.has(k[3])) x++;
  }
  if (union || slot === 0) { x += stick[0]; y += stick[1]; }
  const l = Math.hypot(x, y); if (l > 1) { x /= l; y /= l; }
  return [x, y];
}

function pushOut(p) {
  for (let it = 0; it < 2; it++) {
    for (let tx = Math.floor(p.x - R); tx <= Math.floor(p.x + R); tx++) for (let ty = Math.floor(p.y - R); ty <= Math.floor(p.y + R); ty++) {
      if (!isStone(tx, ty)) continue;
      const cx = Math.max(tx, Math.min(p.x, tx + 1)), cy = Math.max(ty, Math.min(p.y, ty + 1));
      const dx = p.x - cx, dy = p.y - cy, d2 = dx * dx + dy * dy;
      if (d2 >= R * R) continue;
      if (d2 > 1e-9) { const d = Math.sqrt(d2), k = (R - d) / d; p.x += dx * k; p.y += dy * k; }
      else {
        const l = p.x - tx, r = tx + 1 - p.x, t = p.y - ty, b = ty + 1 - p.y, m = Math.min(l, r, t, b);
        if (m === l) p.x = tx - R; else if (m === r) p.x = tx + 1 + R; else if (m === t) p.y = ty - R; else p.y = ty + 1 + R;
      }
    }
  }
  p.x = Math.max(R, Math.min(W - R, p.x)); p.y = Math.max(R, Math.min(H - R, p.y));
}

function move(p, dt) {
  let { ix, iy } = p; const l = Math.hypot(ix, iy); if (l > 1) { ix /= l; iy /= l; }
  const sp = SPEED * (p.bot ? .92 : 1) * dt;
  p.x += ix * sp; p.y += iy * sp;
  pushOut(p);
}

function separate() {
  const a = aliveIdx(), ps = S.players;
  for (let it = 0; it < 2; it++) for (let i = 0; i < a.length; i++) for (let j = i + 1; j < a.length; j++) {
    const p = ps[a[i]], q = ps[a[j]]; let dx = q.x - p.x, dy = q.y - p.y, d = Math.hypot(dx, dy);
    if (d >= 2 * R) continue;
    if (d < 1e-6) { dx = Math.random() - .5; dy = Math.random() - .5; d = Math.hypot(dx, dy); }
    const k = (2 * R - d) / 2 / d; p.x -= dx * k; p.y -= dy * k; q.x += dx * k; q.y += dy * k;
  }
  a.forEach(i => pushOut(ps[i]));
}

// Quem estiver no caminho dos espinhos (fora da sombra das paredes) morre.
function judge() {
  S.players.forEach(p => { if (p.alive && COV[(p.y | 0) * W + (p.x | 0)]) p.alive = false; });
}

function endGame() {
  const a = aliveIdx(); S.ph = 'over'; S.win = a.length === 1 ? a[0] : -1; S.tl = 0; broadcast();
}
function nextWave() {
  S.w++;
  // algumas paredes ficam piscando durante a onda e somem quando o aviso vermelho começa
  const n = S.w < 2 ? 0 : Math.min(S.w >= 4 && SEGS.length > 4 ? 2 : 1, SEGS.length - 1);
  S.doom = shuffle(SEGS.map((_, k) => k)).slice(0, n);
  S.side = SIDES[Math.random() * 4 | 0]; buildCov(S.side, S.doom);
  S.ph = 'run'; S.tl = S.tm = runTime(S.w); planBots();
}

function step(dt) {
  if (!S || S.ph === 'over') return;
  botThink(dt);
  S.players.forEach(p => {
    if (!p.alive) return;
    if (p.kind === 'kb') { const v = kbVector(p.kb, unionKeys); p.ix = v[0]; p.iy = v[1]; }
    move(p, dt);
  });
  separate();
  S.tl -= dt;
  if (S.ph === 'run' && S.tl <= 0) {
    S.ph = 'warn'; S.tl = S.tm = WARN;
    if (S.doom.length) { setWalls(SEGS.filter((_, k) => !S.doom.includes(k))); S.doom = []; buildCov(S.side, []); }
  }
  else if (S.ph === 'warn' && S.tl <= 0) { S.ph = 'fire'; S.tl = S.tm = FIRE; judge(); }
  else if (S.ph === 'fire') { judge(); if (S.tl <= 0) { aliveIdx().length <= 1 ? endGame() : nextWave(); } }
  if (S.ph !== 'fire' && S.ph !== 'over' && aliveIdx().length <= 1) endGame();
}

function restart() {
  if (mode === 'local') newGame(localSpecs);
  else newGame(lobby.map((l, i) => ({ n: l.n, kind: i === 0 ? 'kb' : 'net', kb: 0 })), lobby.map(l => !!l.gone));
}

/* ===== Rede: snapshot do host para os convidados ===== */
const r2 = v => Math.round(v * 100) / 100;
function broadcast() {
  if (mode !== 'online' || !isHost || !S) return;
  const m = { t: 'state', s: {
    ph: S.ph, tl: r2(S.tl), tm: S.tm, w: S.w, win: S.win,
    sd: S.side, dm: S.doom, wl: SEGS,
    p: S.players.map(p => [r2(p.x), r2(p.y), p.alive ? 1 : 0]),
    n: S.players.map(p => p.n)
  } };
  lobby.forEach(l => l.conn && l.conn.open && l.conn.send(m));
}

let lastSim = performance.now(), snapAcc = 0, lastIn = [9, 9], lastInAt = 0;
setInterval(() => {
  const now = performance.now(), dt = Math.min(.05, (now - lastSim) / 1000); lastSim = now;
  if (!S) return;
  if (isHost) {
    step(dt);
    snapAcc += dt;
    if (S.ph !== 'over' && snapAcc >= 1 / 30) { snapAcc = 0; broadcast(); }
  } else if (mode === 'online' && hostConn && hostConn.open) {
    const v = kbVector(0, true);
    if (Math.abs(v[0] - lastIn[0]) > .03 || Math.abs(v[1] - lastIn[1]) > .03 || now - lastInAt > 300) {
      lastIn = v; lastInAt = now; hostConn.send({ t: 'in', x: +v[0].toFixed(2), y: +v[1].toFixed(2) });
    }
  }
}, 1000 / 60);

/* ===== Renderização (canvas) ===== */
const cv = $('#cv'), g = cv.getContext('2d');
let cw = 0, ch = 0, dpr = 1;
const cam = { x: W / 2, y: H / 2, s: 14 };
let V = [], wasAlive = [], fxs = [], lastW = 0, zoneBorn = 0, shakeUntil = 0, lastPh = '', panSig = '';
const LB = [];

function resize() {
  const r = $('#boardWrap').getBoundingClientRect(); if (!r.width || !r.height) return;
  dpr = Math.min(2, window.devicePixelRatio || 1); cw = r.width; ch = r.height;
  cv.width = Math.round(cw * dpr); cv.height = Math.round(ch * dpr); cv.style.width = cw + 'px'; cv.style.height = ch + 'px';
}
new ResizeObserver(resize).observe($('#boardWrap'));
addEventListener('resize', resize);

function resetVis() {
  V = S.players.map(p => ({ x: p.x, y: p.y, fx: 0, fy: 1 }));
  wasAlive = S.players.map(p => p.alive); fxs = []; lastW = 0; panSig = '';
}

const timeLeft = now => isHost ? Math.max(0, S.tl) : Math.max(0, S.tl - (now - S.at) / 1000);

function updateVis(dt, now) {
  const ps = S.players;
  while (V.length < ps.length) { const p = ps[V.length]; V.push({ x: p.x, y: p.y, fx: 0, fy: 1 }); wasAlive.push(p.alive); }
  const k = 1 - Math.exp(-dt * 22);
  ps.forEach((p, i) => {
    const v = V[i]; let nx = p.x, ny = p.y;
    if (!isHost && Math.hypot(p.x - v.x, p.y - v.y) < 4) { nx = v.x + (p.x - v.x) * k; ny = v.y + (p.y - v.y) * k; }
    const mx = nx - v.x, my = ny - v.y; if (Math.hypot(mx, my) > .002) { v.fx = mx; v.fy = my; }
    v.x = nx; v.y = ny;
    if (wasAlive[i] && !p.alive) fxs.push({ x: v.x, y: v.y, t: now, c: i });
    wasAlive[i] = p.alive;
  });
  if (S.w !== lastW) { lastW = S.w; zoneBorn = now; }
  if (S.ph !== lastPh) { if (S.ph === 'fire') shakeUntil = now + 260; lastPh = S.ph; }
  fxs = fxs.filter(f => now - f.t < 1600);
}

function focusPts() {
  const ps = S.players; let idx = [];
  if (mode === 'local') idx = ps.map((_, i) => i).filter(i => ps[i].kind === 'kb' && ps[i].alive);
  else if (ps[me] && ps[me].alive) idx = [me];
  if (!idx.length) idx = ps.map((_, i) => i).filter(i => ps[i].alive);
  return idx.map(i => V[i]).filter(Boolean);
}

function updateCam(dt) {
  const pts = focusPts(), lo = Math.min(cw, ch) / W, hi = Math.min(cw, ch) / 14;
  let tx = W / 2, ty = H / 2, ts = lo;
  if (pts.length) {
    let x0 = 1e9, x1 = -1e9, y0 = 1e9, y1 = -1e9;
    pts.forEach(p => { x0 = Math.min(x0, p.x); x1 = Math.max(x1, p.x); y0 = Math.min(y0, p.y); y1 = Math.max(y1, p.y); });
    ts = Math.min(cw / (x1 - x0 + 14), ch / (y1 - y0 + 14)); tx = (x0 + x1) / 2; ty = (y0 + y1) / 2;
  }
  ts = Math.max(lo, Math.min(hi, ts));
  const k = 1 - Math.exp(-dt * 5);
  cam.s += (ts - cam.s) * k; cam.x += (tx - cam.x) * k; cam.y += (ty - cam.y) * k;
}

function label(t, x, y, px, c, w) { LB.push({ t, x, y, px, c, w }); }

function draw(now) {
  g.setTransform(dpr, 0, 0, dpr, 0, 0);
  g.fillStyle = '#03050c'; g.fillRect(0, 0, cw, ch);
  const s = cam.s, vw = cw / s, vh = ch / s;
  const cx = vw >= W ? W / 2 : Math.max(vw / 2, Math.min(W - vw / 2, cam.x));
  const cy = vh >= H ? H / 2 : Math.max(vh / 2, Math.min(H - vh / 2, cam.y));
  let ox = 0, oy = 0; if (now < shakeUntil) { ox = (Math.random() - .5) * 5; oy = (Math.random() - .5) * 5; }
  LB.length = 0;
  g.save();
  g.translate(cw / 2 + ox, ch / 2 + oy); g.scale(s, s); g.translate(-cx, -cy);
  const x0 = Math.max(0, Math.floor(cx - vw / 2)), x1 = Math.min(W - 1, Math.ceil(cx + vw / 2));
  const y0 = Math.max(0, Math.floor(cy - vh / 2)), y1 = Math.min(H - 1, Math.ceil(cy + vh / 2));

  // chão e grade
  for (let y = y0; y <= y1; y++) for (let x = x0; x <= x1; x++) { g.fillStyle = (x + y) % 2 ? '#0b1426' : '#0e1a31'; g.fillRect(x, y, 1, 1); }
  g.strokeStyle = 'rgba(34,230,255,.10)'; g.lineWidth = 1 / s; g.beginPath();
  for (let x = x0; x <= x1 + 1; x++) { g.moveTo(x, y0); g.lineTo(x, y1 + 1); }
  for (let y = y0; y <= y1 + 1; y++) { g.moveTo(x0, y); g.lineTo(x1 + 1, y); }
  g.stroke();
  g.strokeStyle = 'rgba(34,230,255,.25)'; g.lineWidth = 9 / s; g.strokeRect(0, 0, W, H);
  g.strokeStyle = '#22e6ff'; g.lineWidth = 3 / s; g.strokeRect(0, 0, W, H);

  // espinhos: vêm de um lado só; as paredes bloqueiam a passagem
  if (S.ph !== 'over') {
    const fire = S.ph === 'fire';
    g.save(); g.beginPath();
    for (let ty = y0; ty <= y1; ty++) for (let tx = x0; tx <= x1; tx++) if (COV[ty * W + tx]) g.rect(tx, ty, 1, 1);
    g.clip();
    if (!fire) {
      const a = S.ph === 'run' ? .09 : .2 + .16 * (.5 + .5 * Math.sin(now / 90));
      g.fillStyle = `rgba(255,59,92,${a})`; g.fillRect(x0, y0, x1 - x0 + 1, y1 - y0 + 1);
      if (S.ph === 'warn') {
        g.strokeStyle = 'rgba(255,59,92,.4)'; g.lineWidth = .3; g.beginPath();
        const st = 1.1, ya = y0, yb = y1 + 1, xb = x1 + 1;
        for (let c = Math.floor((x0 + ya) / st) * st; c <= xb + yb; c += st) { g.moveTo(c - ya, ya); g.lineTo(c - yb, yb); }
        g.stroke();
      }
    } else {
      const tl = Math.max(0, timeLeft(now)), el = S.tm - tl, front = Math.min(1, el / .3) * (W + 2), fade = tl < .25 ? tl / .25 : 1;
      g.fillStyle = 'rgba(22,4,12,.82)'; g.fillRect(x0, y0, x1 - x0 + 1, y1 - y0 + 1);
      const sub = s < 18 ? 1 : 2, cell = 1 / sub;
      g.beginPath();
      for (let ty = y0; ty <= y1; ty++) for (let tx = x0; tx <= x1; tx++) {
        if (!COV[ty * W + tx]) continue;
        const dist = S.side === 'top' ? ty : S.side === 'bottom' ? H - 1 - ty : S.side === 'left' ? tx : W - 1 - tx;
        let k = Math.max(0, Math.min(1, (front - dist) / 1.2)) * fade; k = k * k * (3 - 2 * k);
        if (k <= 0) continue;
        for (let a = 0; a < sub; a++) for (let b = 0; b < sub; b++) {
          const px = tx + (a + .5) * cell, py = ty + (b + .5) * cell, hw = cell * .34, h = cell * .8 * k;
          g.moveTo(px, py - h * .55); g.lineTo(px + hw, py + h * .45); g.lineTo(px - hw, py + h * .45); g.closePath();
        }
      }
      g.fillStyle = '#d6f3ff'; g.fill(); g.strokeStyle = '#22e6ff'; g.lineWidth = .04; g.stroke();
    }
    g.restore();
    // setas na borda de onde os espinhos saem
    if (S.ph === 'run' || S.ph === 'warn') {
      const ang = { top: Math.PI / 2, bottom: -Math.PI / 2, left: 0, right: Math.PI }[S.side];
      g.strokeStyle = `rgba(255,59,92,${.55 + .35 * Math.sin(now / 160)})`; g.lineWidth = .13;
      const horiz = S.side === 'top' || S.side === 'bottom';
      for (let t = 1; t < (horiz ? W : H); t += 3) {
        const px = horiz ? t : S.side === 'left' ? .9 : W - .9, py = horiz ? (S.side === 'top' ? .9 : H - .9) : t;
        g.save(); g.translate(px, py); g.rotate(ang); g.beginPath(); g.moveTo(-.3, -.4); g.lineTo(.3, 0); g.lineTo(-.3, .4); g.stroke(); g.restore();
      }
      g.lineWidth = 8 / s; g.beginPath();
      if (S.side === 'top') { g.moveTo(0, 0); g.lineTo(W, 0); } else if (S.side === 'bottom') { g.moveTo(0, H); g.lineTo(W, H); }
      else if (S.side === 'left') { g.moveTo(0, 0); g.lineTo(0, H); } else { g.moveTo(W, 0); g.lineTo(W, H); }
      g.stroke();
    }
  }

  // paredes (as que vão sumir piscam em vermelho)
  const doomT = new Set();
  (S.doom || []).forEach(k => { const sg = SEGS[k]; if (sg) for (let a = 0; a < sg[2]; a++) for (let b = 0; b < sg[3]; b++) doomT.add((sg[1] + b) * W + sg[0] + a); });
  const blink = .3 + .5 * (.5 + .5 * Math.sin(now / 110));
  for (const [tx, ty] of STONES) {
    if (tx < x0 || tx > x1 || ty < y0 || ty > y1) continue;
    const dm = doomT.has(ty * W + tx);
    if (dm) g.globalAlpha = blink;
    g.fillStyle = dm ? '#4a1a2a' : '#1a2748'; g.fillRect(tx + .07, ty + .07, .86, .86);
    g.strokeStyle = dm ? '#ff3b5c' : '#22e6ff'; g.lineWidth = .06; g.strokeRect(tx + .07, ty + .07, .86, .86);
    g.strokeStyle = dm ? 'rgba(255,59,92,.5)' : 'rgba(34,230,255,.35)'; g.lineWidth = .04; g.strokeRect(tx + .3, ty + .3, .4, .4);
    g.globalAlpha = 1;
  }

  // marcas de queda
  fxs.forEach(f => {
    const a = (now - f.t) / 1600, c = COLORS[f.c % 6];
    g.globalAlpha = Math.max(0, 1 - a); g.strokeStyle = c.c; g.lineWidth = .1;
    g.beginPath(); g.arc(f.x, f.y, .5 + a * 2.2, 0, 6.2832); g.stroke();
    g.lineWidth = .14; g.beginPath(); g.moveTo(f.x - .3, f.y - .3); g.lineTo(f.x + .3, f.y + .3); g.moveTo(f.x + .3, f.y - .3); g.lineTo(f.x - .3, f.y + .3); g.stroke();
    g.globalAlpha = 1;
  });

  // jogadores
  const ps = S.players;
  ps.map((_, i) => i).filter(i => ps[i].alive && V[i]).sort((a, b) => V[a].y - V[b].y).forEach(i => {
    const v = V[i], c = COLORS[i % 6], DR = .5;
    g.fillStyle = 'rgba(0,0,0,.35)'; g.beginPath(); g.ellipse(v.x, v.y + .14, DR * 1.05, DR * .8, 0, 0, 6.2832); g.fill();
    const gr = g.createRadialGradient(v.x - .15, v.y - .18, .04, v.x, v.y, DR * 1.1);
    gr.addColorStop(0, '#fff'); gr.addColorStop(.25, c.l); gr.addColorStop(.7, c.c); gr.addColorStop(1, c.c);
    g.fillStyle = gr; g.beginPath(); g.arc(v.x, v.y, DR, 0, 6.2832); g.fill();
    const fl = Math.hypot(v.fx, v.fy) || 1;
    g.save(); g.translate(v.x + v.fx / fl * .1, v.y + v.fy / fl * .1); g.rotate(Math.atan2(v.fy, v.fx));
    g.fillStyle = '#050812'; g.fillRect(.02, -.18, .3, .36); g.fillStyle = c.c; g.fillRect(.08, -.025, .18, .05);
    g.restore();
    const mine = mode === 'local' ? ps[i].kind === 'kb' : i === me;
    if (mine) {
      g.strokeStyle = '#fff'; g.lineWidth = .06; g.setLineDash([.18, .14]); g.beginPath(); g.arc(v.x, v.y, DR + .12, 0, 6.2832); g.stroke(); g.setLineDash([]);
      g.fillStyle = '#fff'; g.beginPath(); g.moveTo(v.x - .2, v.y - 1.25); g.lineTo(v.x + .2, v.y - 1.25); g.lineTo(v.x, v.y - .95); g.fill();
    }
    label(ps[i].n, v.x, v.y - .8, Math.max(10, Math.min(15, s * .55)), '#fff', 700);
    if (S.ph === 'over' && S.win === i) label('👑', v.x, v.y - 1.5, Math.max(16, s * .9), '#fff', 700);
  });
  g.restore();

  // rótulos em tela
  g.textAlign = 'center'; g.textBaseline = 'middle';
  LB.forEach(l => {
    const x = (l.x - cx) * s + cw / 2 + ox, y = (l.y - cy) * s + ch / 2 + oy;
    g.font = `${l.w} ${l.px}px Rajdhani, Orbitron, system-ui, sans-serif`;
    g.lineWidth = 3; g.strokeStyle = 'rgba(3,5,12,.85)'; g.strokeText(l.t, x, y); g.fillStyle = l.c; g.fillText(l.t, x, y);
  });

  // seta para o abrigo mais próximo quando você está no caminho dos espinhos e ele está fora da tela
  let ai = -1;
  if (S.ph !== 'over') {
    if (mode === 'local') { const hs = ps.map((_, k) => k).filter(k => ps[k].kind === 'kb' && ps[k].alive); if (hs.length === 1) ai = hs[0]; }
    else if (ps[me] && ps[me].alive) ai = me;
  }
  if (ai >= 0 && V[ai] && COV[(ps[ai].y | 0) * W + (ps[ai].x | 0)]) {
    const v = V[ai]; let bx = -1, by = -1, bd = 1e9;
    for (let ty = 0; ty < H; ty++) for (let tx = 0; tx < W; tx++) {
      if (!safeSpot(tx, ty, false)) continue;
      const d = Math.hypot(tx + .5 - v.x, ty + .5 - v.y); if (d < bd) { bd = d; bx = tx + .5; by = ty + .5; }
    }
    const sx = (bx - cx) * s + cw / 2, sy = (by - cy) * s + ch / 2;
    if (bx >= 0 && (sx < 0 || sx > cw || sy < 0 || sy > ch)) {
      const dx = sx - cw / 2, dy = sy - ch / 2, m = 34, t = Math.min((cw / 2 - m) / Math.abs(dx || 1e-6), (ch / 2 - m) / Math.abs(dy || 1e-6));
      const ax = cw / 2 + dx * t, ay = ch / 2 + dy * t, an = Math.atan2(dy, dx);
      g.save(); g.translate(ax, ay); g.rotate(an);
      g.fillStyle = '#3dffa0'; g.shadowColor = '#3dffa0'; g.shadowBlur = 10;
      g.beginPath(); g.moveTo(14, 0); g.lineTo(-8, -10); g.lineTo(-8, 10); g.closePath(); g.fill();
      g.restore();
      g.font = '700 12px Rajdhani, system-ui, sans-serif'; g.fillStyle = '#eafff5'; g.fillText(Math.round(bd) + ' m', ax - Math.cos(an) * 24, ay - Math.sin(an) * 24);
    }
  }

  // minimapa
  const ms = Math.round(Math.min(120, Math.min(cw, ch) * .3)), mx = cw - ms - 8, my = ch - ms - 8, q = ms / W;
  g.fillStyle = 'rgba(5,8,18,.78)'; g.fillRect(mx, my, ms, ms);
  g.fillStyle = 'rgba(120,150,210,.5)'; STONES.forEach(([x, y]) => g.fillRect(mx + x * q, my + y * q, q, q));
  if (S.ph !== 'over') { g.fillStyle = 'rgba(255,59,92,.28)'; for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) if (COV[y * W + x]) g.fillRect(mx + x * q, my + y * q, q + .4, q + .4); }
  ps.forEach((p, i) => {
    if (!p.alive || !V[i]) return;
    g.fillStyle = COLORS[i % 6].c; g.beginPath(); g.arc(mx + V[i].x * q, my + V[i].y * q, Math.max(2.2, q * .55), 0, 6.2832); g.fill();
  });
  g.save(); g.beginPath(); g.rect(mx, my, ms, ms); g.clip();
  g.strokeStyle = 'rgba(255,255,255,.65)'; g.lineWidth = 1; g.strokeRect(mx + (cx - vw / 2) * q, my + (cy - vh / 2) * q, vw * q, vh * q);
  g.restore();
  g.strokeStyle = S.ph === 'warn' ? '#ff3b5c' : 'rgba(34,230,255,.7)'; g.lineWidth = 1.5; g.strokeRect(mx + .5, my + .5, ms - 1, ms - 1);
}

/* ===== HUD e painéis ===== */
const hudEl = $('#hud'), waveEl = $('#wave'), stEl = $('#status'), barI = $('#bar i');
const setText = (el, t) => { if (el.textContent !== t) el.textContent = t; };

function hud(now) {
  const ps = S.players, tl = timeLeft(now), n = aliveIdx().length;
  const dead = mode === 'online' ? !ps[me].alive : !ps.some(p => p.kind === 'kb' && p.alive);
  let cls = S.ph, txt = '';
  if (S.ph === 'run') txt = dead ? 'Você caiu — assistindo' : `${S.doom.length ? '🧱 Paredes piscando vão sumir! ' : ''}Espinhos vêm de ${SIDE_TXT[S.side]} · ${tl.toFixed(1)}s`;
  else if (S.ph === 'warn') txt = `⚠ ESPINHOS DE ${SIDE_TXT[S.side]} EM ${Math.ceil(tl)}`;
  else if (S.ph === 'fire') txt = '💥 ESPINHOS!';
  else { cls = 'run'; txt = 'Fim de jogo'; }
  if (hudEl.className !== cls) hudEl.className = cls;
  setText(stEl, txt); setText(waveEl, `ONDA ${S.w} · ${n} ${n === 1 ? 'VIVO' : 'VIVOS'}`);
  barI.style.width = (S.ph === 'over' ? 0 : Math.max(0, Math.min(1, tl / (S.tm || 1))) * 100) + '%';
}

function panels() {
  const ps = S.players, sig = ps.map(p => p.n + (p.alive ? 1 : 0)).join('|') + mode + me;
  if (sig === panSig) return; panSig = sig;
  const h = Math.ceil(ps.length / 2);
  const mk = i => {
    const p = ps[i], c = COLORS[i];
    const tag = !p.alive ? '☠' : p.bot ? '🤖' : (mode === 'local' && p.kind === 'kb') ? KEYHINT[p.kb] : '';
    return `<div class="pl${p.alive ? '' : ' dead'}${mode === 'online' && i === me ? ' me' : ''}" style="--c:${c.c};--l:${c.l}"><div class="av">${esc(p.n.charAt(0).toUpperCase())}</div><div class="col"><small>${esc(p.n)}</small><em>${tag}</em></div></div>`;
  };
  $('#topBar').innerHTML = ps.slice(0, h).map((_, i) => mk(i)).join('');
  $('#botBar').innerHTML = ps.slice(h).map((_, i) => mk(i + h)).join('');
}

function overlay() {
  const o = $('#overlay'); let h = '';
  if (S.ph === 'over') {
    const w = S.win;
    h = `<h2>${w < 0 ? 'Empate!' : '🏆 ' + esc(S.players[w].n) + ' venceu!'}</h2>`;
    h += isHost ? '<button class="btn" id="ovAgain">Jogar de novo</button>' : '<p class="msg">Aguardando o host…</p>';
    h += '<button class="btn ghost" id="ovMenu">Sair</button>';
  }
  o.classList.toggle('on', !!h);
  if (o.dataset.h !== h) { o.innerHTML = h; o.dataset.h = h; }
}

let lastT = performance.now();
function frame(now) {
  requestAnimationFrame(frame);
  const dt = Math.min(.05, (now - lastT) / 1000); lastT = now;
  if (!S || !cw || !$('#game').classList.contains('active')) return;
  updateVis(dt, now); updateCam(dt); draw(now); hud(now); panels(); overlay();
}
requestAnimationFrame(frame);

/* ===== Controles ===== */
if ('ontouchstart' in window || navigator.maxTouchPoints > 0) document.body.classList.add('touch');
addEventListener('keydown', e => {
  if (!$('#game').classList.contains('active')) return;
  if (e.code.startsWith('Arrow') || e.code === 'Space') e.preventDefault();
  keys.add(e.code);
});
addEventListener('keyup', e => keys.delete(e.code));
addEventListener('blur', () => keys.clear());

const stEl2 = $('#stick'), knob = stEl2.querySelector('i'); let sid = null;
function setStick(e) {
  const r = stEl2.getBoundingClientRect(), m = r.width / 2 * .7;
  let dx = e.clientX - (r.left + r.width / 2), dy = e.clientY - (r.top + r.height / 2); const l = Math.hypot(dx, dy);
  if (l > m) { dx *= m / l; dy *= m / l; }
  stick = [dx / m, dy / m]; if (Math.hypot(stick[0], stick[1]) < .15) stick = [0, 0];
  knob.style.transform = `translate(${dx}px,${dy}px)`;
}
stEl2.addEventListener('pointerdown', e => { sid = e.pointerId; stEl2.setPointerCapture(sid); setStick(e); e.preventDefault(); });
stEl2.addEventListener('pointermove', e => { if (e.pointerId === sid) setStick(e); });
const relStick = e => { if (e.pointerId === sid) { sid = null; stick = [0, 0]; knob.style.transform = ''; } };
stEl2.addEventListener('pointerup', relStick); stEl2.addEventListener('pointercancel', relStick);

$('#btnQuit').onclick = () => { if (confirm('Sair da partida?')) leave(); };
$('#overlay').onclick = e => {
  const id = e.target.id;
  if (id === 'ovAgain') restart();
  else if (id === 'ovMenu') leave();
};

/* ===== Menus ===== */
$('#btnOnline').onclick = () => show('online');
$('#btnLocal').onclick = () => { renderCfg(); show('local'); };
document.querySelectorAll('.back').forEach(b => b.onclick = () => show('menu'));

function renderCfg() {
  document.querySelectorAll('#humCount .num').forEach(b => b.classList.toggle('sel', +b.dataset.v === cfg.h));
  document.querySelectorAll('#botCount .num').forEach(b => b.classList.toggle('sel', +b.dataset.v === cfg.b));
  const t = cfg.h + cfg.b;
  $('#btnLocalStart').disabled = t < 2 || t > 6;
  $('#localMsg').textContent = t < 2 ? 'Escolha pelo menos 2 jogadores.' : t > 6 ? 'No máximo 6 jogadores.' :
    `${t} jogadores · ${cfg.h === 1 ? 'WASD, setas ou joystick' : KEYHINT.slice(0, cfg.h).join(' / ')}`;
}
[['#humCount', 1, 3, 'h'], ['#botCount', 0, 5, 'b']].forEach(([sel, a, z, key]) => {
  for (let n = a; n <= z; n++) {
    const b = document.createElement('button');
    b.className = 'num'; b.textContent = n; b.dataset.v = n; b.onclick = () => { cfg[key] = n; renderCfg(); };
    $(sel).append(b);
  }
});

$('#btnLocalStart').onclick = () => {
  const { h, b } = cfg;
  mode = 'local'; isHost = true; me = 0; unionKeys = h === 1;
  localSpecs = [];
  for (let i = 0; i < h; i++) localSpecs.push({ n: COLORS[i].n, kind: 'kb', kb: i });
  for (let i = 0; i < b; i++) localSpecs.push({ n: COLORS[h + i].n, kind: 'bot' });
  newGame(localSpecs); show('game'); resize();
};

function leave(t) {
  if (peer) peer.destroy();
  peer = null; hostConn = null; lobby = []; S = null; wallSig = ''; mode = null; isHost = false; stick = [0, 0]; keys.clear();
  show(t ? 'online' : 'menu'); msg(t);
}

/* ===== Online (salas via PeerJS / WebRTC, o host controla o jogo) ===== */
const genCode = () => Array.from({ length: 4 }, () => 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789'[Math.random() * 32 | 0]).join('');

function renderLobby(names) {
  $('#roomCode').textContent = roomCode;
  $('#plist').innerHTML = names.map((n, i) => `<li style="--c:${COLORS[i].c}"><i></i>${esc(n)}${i === 0 ? ' (host)' : ''}${i === me ? ' (você)' : ''}</li>`).join('');
  $('#btnStart').style.display = isHost ? '' : 'none';
  $('#btnCopy').style.display = isHost ? '' : 'none';
  $('#btnStart').disabled = names.length < 2;
  $('#lobbyMsg').textContent = isHost ? (names.length < 2 ? 'Esperando mais jogadores…' : '') : 'Esperando o host iniciar…';
}

function sendLobby() {
  const names = lobby.map(l => l.n);
  lobby.forEach(l => l.conn && l.conn.open && l.conn.send({ t: 'lobby', names }));
  renderLobby(names);
}

function createRoom(tries = 0) {
  const name = nm(); roomCode = genCode(); msg('Criando sala…');
  if (peer) peer.destroy();
  peer = new Peer('spikeattacks-' + roomCode, PEER_OPTS);
  peer.on('open', () => {
    mode = 'online'; isHost = true; me = 0; S = null;
    lobby = [{ n: name, conn: null }];
    show('lobby'); renderLobby([name]);
  });
  peer.on('connection', c => {
    c.on('data', d => hostMsg(c, d));
    c.on('close', () => drop(c));
  });
  peer.on('error', e => {
    if (e.type === 'unavailable-id' && tries < 4) createRoom(tries + 1);
    else msg('Erro de conexão. Tente de novo.');
  });
}

function hostMsg(c, d) {
  if (d.t === 'join') {
    if (S || lobby.length >= 6) { c.send({ t: 'full' }); return; }
    lobby.push({ n: String(d.n).slice(0, 10), conn: c });
    c.send({ t: 'you', i: lobby.length - 1 });
    sendLobby();
  } else if (d.t === 'in' && S) {
    const i = lobby.findIndex(l => l.conn === c), p = S.players[i];
    if (p && p.alive) {
      const x = +d.x, y = +d.y;
      if (isFinite(x) && isFinite(y)) { p.ix = Math.max(-1, Math.min(1, x)); p.iy = Math.max(-1, Math.min(1, y)); }
    }
  }
}

function drop(c) {
  const i = lobby.findIndex(l => l.conn === c);
  if (i < 0) return;
  if (S) { lobby[i].gone = true; S.players[i].alive = false; S.players[i].ix = S.players[i].iy = 0; broadcast(); }
  else {
    lobby.splice(i, 1);
    lobby.forEach((l, k) => l.conn && l.conn.send({ t: 'you', i: k }));
    sendLobby();
  }
}

function joinRoom() {
  const code = $('#code').value.trim().toUpperCase();
  if (code.length < 4) return msg('Digite o código da sala.');
  roomCode = code; msg('Conectando…');
  if (peer) peer.destroy();
  peer = new Peer(PEER_OPTS);
  let ok = false;
  const fail = () => { if (!ok) msg('Sala não encontrada.'); };
  peer.on('open', () => {
    hostConn = peer.connect('spikeattacks-' + code, { reliable: true });
    hostConn.on('open', () => { ok = true; hostConn.send({ t: 'join', n: nm() }); });
    hostConn.on('data', guestMsg);
    hostConn.on('close', () => { if (ok && mode) leave('A sala foi encerrada.'); });
    setTimeout(fail, 8000);
  });
  peer.on('error', fail);
}

function guestMsg(d) {
  if (d.t === 'full') leave('Sala cheia ou jogo já começou.');
  else if (d.t === 'you') { me = d.i; mode = 'online'; isHost = false; }
  else if (d.t === 'lobby') { mode = 'online'; if (!S) show('lobby'); renderLobby(d.names); }
  else if (d.t === 'state') {
    mode = 'online';
    const s = d.s, sig = s.sd + JSON.stringify(s.wl) + JSON.stringify(s.dm);
    if (sig !== wallSig) { wallSig = sig; setWalls(s.wl); buildCov(s.sd, s.dm); }
    S = {
      ph: s.ph, tl: s.tl, tm: s.tm, w: s.w, win: s.win, at: performance.now(), side: s.sd, doom: s.dm,
      players: s.p.map((a, i) => ({ n: s.n[i], x: a[0], y: a[1], alive: !!a[2] }))
    };
    if (!$('#game').classList.contains('active')) { show('game'); resize(); }
  }
}

$('#btnCreate').onclick = () => createRoom();
$('#btnJoin').onclick = joinRoom;
$('#btnLeave').onclick = () => leave();
$('#btnCopy').onclick = async () => {
  const url = location.origin + location.pathname + '?sala=' + roomCode;
  try { await navigator.clipboard.writeText(url); $('#lobbyMsg').textContent = 'Link copiado!'; }
  catch { prompt('Copie o link da sala:', url); }
};

// abrir um link de sala (?sala=ABCD) já preenche o código
const q = new URLSearchParams(location.search).get('sala');
if (q) { $('#code').value = q.toUpperCase().slice(0, 4); show('online'); }
$('#btnStart').onclick = () => {
  if (lobby.length < 2) return;
  mode = 'online'; unionKeys = true;
  newGame(lobby.map((l, i) => ({ n: l.n, kind: i === 0 ? 'kb' : 'net', kb: 0 })));
  show('game'); resize();
};
