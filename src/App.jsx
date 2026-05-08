import React, {
  useState, useRef, useLayoutEffect, useMemo, useCallback,
  useEffect, forwardRef, useImperativeHandle,
} from 'react';

// ---------- ids ----------
let _id = 0;
const newId = () => ++_id;

// ---------- pen ----------
const PEN_MIN = 0.1;
const PEN_MAX = 1000;
const sliderToSize = (s) => PEN_MIN * Math.pow(PEN_MAX / PEN_MIN, s / 100);
const sizeToSlider = (sz) => 100 * Math.log(sz / PEN_MIN) / Math.log(PEN_MAX / PEN_MIN);

// ---------- system constants ----------
const DEFAULT_VERTICAL_SIZES = [200, 300, 400, 600, 800, 1000, 1200];
const DEFAULT_GAP_SIZES = [200, 400, 600, 800, 1000];
const CUT_STROKE_HALO = 200;
const BITMAP_Y_PADDING = 200;
const BITMAP_GROW_CHUNK = 400;
const DPR_CAP = 2;
const RDP_EPSILON = 0.5;

// ---------- lasso constants ----------
const HANDLE_SIZE = 9;
const HANDLE_HIT_RADIUS = 14;
const ROTATE_HANDLE_DIST = 32;
const LASSO_COLOR = '#c43a2c';

// ---------- helpers ----------
const computeBlockTops = (arr) => {
  const tops = {};
  let y = 0;
  for (const b of arr) {
    tops[b.id] = y;
    y += b.height;
  }
  return tops;
};

const findStrokeBlockId = (stroke, arr, tops) => {
  if (!stroke.points || stroke.points.length === 0) return null;
  const sortedY = stroke.points.map((p) => p.y).sort((a, b) => a - b);
  const medianY = sortedY[Math.floor(sortedY.length / 2)];

  let bestCutId = null;
  let bestCutDist = Infinity;
  for (const b of arr) {
    if (b.type !== 'cut') continue;
    const top = tops[b.id];
    const bottom = top + b.height;
    if (medianY >= top - CUT_STROKE_HALO && medianY <= bottom + CUT_STROKE_HALO) {
      const center = (top + bottom) / 2;
      const dist = Math.abs(medianY - center);
      if (dist < bestCutDist) { bestCutDist = dist; bestCutId = b.id; }
    }
  }
  if (bestCutId !== null) return bestCutId;

  for (const b of arr) {
    if (b.type !== 'gap') continue;
    const top = tops[b.id];
    const bottom = top + b.height;
    if (medianY >= top && medianY <= bottom) return b.id;
  }
  return null;
};

const computeBbox = (points) => {
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  for (const p of points) {
    if (p.x < minX) minX = p.x;
    if (p.y < minY) minY = p.y;
    if (p.x > maxX) maxX = p.x;
    if (p.y > maxY) maxY = p.y;
  }
  return { minX, minY, maxX, maxY };
};

const rdpSimplify = (points, epsilon) => {
  if (points.length <= 2) return points;
  const keep = new Uint8Array(points.length);
  keep[0] = 1;
  keep[points.length - 1] = 1;
  const stack = [[0, points.length - 1]];
  while (stack.length) {
    const [lo, hi] = stack.pop();
    if (hi <= lo + 1) continue;
    const ax = points[lo].x, ay = points[lo].y;
    const bx = points[hi].x, by = points[hi].y;
    const dx = bx - ax, dy = by - ay;
    const segLenSq = dx * dx + dy * dy;
    let bestI = -1, bestD2 = -1;
    for (let i = lo + 1; i < hi; i++) {
      const px = points[i].x - ax, py = points[i].y - ay;
      let d2;
      if (segLenSq === 0) {
        d2 = px * px + py * py;
      } else {
        const t = (px * dx + py * dy) / segLenSq;
        const projX = t * dx, projY = t * dy;
        const ex = px - projX, ey = py - projY;
        d2 = ex * ex + ey * ey;
      }
      if (d2 > bestD2) { bestD2 = d2; bestI = i; }
    }
    if (bestI !== -1 && bestD2 > epsilon * epsilon) {
      keep[bestI] = 1;
      stack.push([lo, bestI]);
      stack.push([bestI, hi]);
    }
  }
  const out = [];
  for (let i = 0; i < points.length; i++) if (keep[i]) out.push(points[i]);
  return out;
};

const renderStrokeToCtx = (ctx, stroke, yShift = 0) => {
  if (!stroke.points || stroke.points.length === 0) return;
  ctx.strokeStyle = `rgba(15, 15, 15, ${stroke.opacity})`;
  ctx.fillStyle = `rgba(15, 15, 15, ${stroke.opacity})`;
  ctx.lineWidth = stroke.size;
  if (stroke.points.length === 1) {
    ctx.beginPath();
    ctx.arc(stroke.points[0].x, stroke.points[0].y + yShift, stroke.size / 2, 0, Math.PI * 2);
    ctx.fill();
    return;
  }
  ctx.beginPath();
  ctx.moveTo(stroke.points[0].x, stroke.points[0].y + yShift);
  for (let i = 1; i < stroke.points.length; i++) {
    ctx.lineTo(stroke.points[i].x, stroke.points[i].y + yShift);
  }
  ctx.stroke();
};

const createBlockBitmap = (logicalWidth, logicalHeight, dpr) => {
  const canvas = document.createElement('canvas');
  const w = Math.max(1, Math.ceil(logicalWidth * dpr));
  const h = Math.max(1, Math.ceil(logicalHeight * dpr));
  canvas.width = w;
  canvas.height = h;
  const ctx = canvas.getContext('2d');
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.scale(dpr, dpr);
  ctx.lineCap = 'round';
  ctx.lineJoin = 'round';
  return { canvas, ctx, logicalWidth, logicalHeight, dpr };
};

const blitBitmap = (srcEntry, dstCtx) => {
  dstCtx.drawImage(
    srcEntry.canvas,
    0, 0,
    srcEntry.logicalWidth, srcEntry.logicalHeight,
  );
};

// ---------- lasso helpers ----------
const pointInPolygon = (px, py, polygon) => {
  if (polygon.length < 3) return false;
  let inside = false;
  for (let i = 0, j = polygon.length - 1; i < polygon.length; j = i++) {
    const xi = polygon[i].x, yi = polygon[i].y;
    const xj = polygon[j].x, yj = polygon[j].y;
    const intersect = ((yi > py) !== (yj > py))
      && (px < (xj - xi) * (py - yi) / (yj - yi) + xi);
    if (intersect) inside = !inside;
  }
  return inside;
};

// Apply selection transform: flip→scale→rotate→translate, all relative to bbox center
const applySelectionTransform = (x, y, cx, cy, tr) => {
  let lx = x - cx, ly = y - cy;
  if (tr.flipH) lx = -lx;
  if (tr.flipV) ly = -ly;
  lx *= tr.scaleX; ly *= tr.scaleY;
  const cos = Math.cos(tr.angle), sin = Math.sin(tr.angle);
  const rx = lx * cos - ly * sin, ry = lx * sin + ly * cos;
  return { x: rx + cx + tr.tx, y: ry + cy + tr.ty };
};

const getHandlePositions = (bbox, tr) => {
  const { minX, minY, maxX, maxY, cx, cy } = bbox;
  const t = (x, y) => applySelectionTransform(x, y, cx, cy, tr);
  const tl = t(minX, minY);
  const tr2 = t(maxX, minY);
  const br = t(maxX, maxY);
  const bl = t(minX, maxY);
  const tc = { x: (tl.x + tr2.x) / 2, y: (tl.y + tr2.y) / 2 };
  const bc = { x: (bl.x + br.x) / 2, y: (bl.y + br.y) / 2 };
  const lc = { x: (tl.x + bl.x) / 2, y: (tl.y + bl.y) / 2 };
  const rc = { x: (tr2.x + br.x) / 2, y: (tr2.y + br.y) / 2 };
  // Rotation handle: away from center along the "up" direction of the bbox
  const outX = tc.x - bc.x, outY = tc.y - bc.y;
  const outLen = Math.sqrt(outX * outX + outY * outY) || 1;
  const rotate = {
    x: tc.x + (outX / outLen) * ROTATE_HANDLE_DIST,
    y: tc.y + (outY / outLen) * ROTATE_HANDLE_DIST,
  };
  return { tl, tr: tr2, br, bl, tc, bc, lc, rc, rotate };
};

const hitTestHandles = (px, py, handles) => {
  const r2 = HANDLE_HIT_RADIUS * HANDLE_HIT_RADIUS;
  // Rotation handle first
  const rot = handles.rotate;
  if ((px - rot.x) ** 2 + (py - rot.y) ** 2 <= r2) return 'rotate';
  for (const name of ['tl', 'tr', 'br', 'bl', 'tc', 'bc', 'lc', 'rc']) {
    const h = handles[name];
    if ((px - h.x) ** 2 + (py - h.y) ** 2 <= r2) return name;
  }
  return null;
};

const makeStarterFrame = (name, opts = {}) => {
  const sm = opts.sideMargin ?? 38;
  return {
    id: newId(),
    name,
    canvasWidth: opts.canvasWidth ?? 690,
    sideMargin: sm,
    blocks: opts.blocks ?? [
      { id: newId(), type: 'cut', height: 600, marginLeft: sm, marginRight: sm },
      { id: newId(), type: 'gap', height: 200 },
      { id: newId(), type: 'cut', height: 800, marginLeft: sm, marginRight: sm },
    ],
  };
};

// ---------- CSS ----------
const STYLES = `
@import url('https://cdn.jsdelivr.net/gh/orioncactus/pretendard@v1.3.9/dist/web/static/pretendard.min.css');
@import url('https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@400;500;600&display=swap');

.conti-root {
  --bg: #f3f0e8;
  --bg-panel: #ebe6d9;
  --bg-canvas-area: #ddd8c8;
  --paper: #fdfbf5;
  --cut: #ffffff;
  --gap: #d9d9d9;
  --ink: #16140f;
  --ink-2: #3a3631;
  --muted: #837e72;
  --line: #cac3b1;
  --accent: #c43a2c;
  --accent-soft: #f1ddd9;

  position: fixed; inset: 0;
  display: flex; flex-direction: column;
  font-family: 'Pretendard', -apple-system, system-ui, sans-serif;
  color: var(--ink);
  background: var(--bg);
  user-select: none;
  -webkit-user-select: none;
  overflow: hidden;
}
.conti-root *, .conti-root *::before, .conti-root *::after { box-sizing: border-box; }
.conti-root .mono { font-family: 'JetBrains Mono', ui-monospace, monospace; }
.conti-root button { font-family: inherit; cursor: pointer; border: none; background: none; color: inherit; }
.conti-root input { font-family: inherit; }

/* topbar */
.conti-topbar {
  display: flex; align-items: center;
  height: 56px; flex: 0 0 56px;
  padding: 0 18px;
  background: var(--bg);
  border-bottom: 1px solid var(--line);
  gap: 16px;
  overflow: hidden;
}
.conti-brand { display: flex; align-items: center; gap: 10px; flex-shrink: 0; }
.conti-brand-mark {
  width: 22px; height: 22px; border-radius: 50%;
  background: var(--ink); position: relative;
}
.conti-brand-mark::after {
  content: ''; position: absolute;
  top: 6px; left: 6px; width: 10px; height: 10px;
  border-radius: 50%; background: var(--paper);
}
.conti-brand-name { font-weight: 700; font-size: 15px; letter-spacing: -0.01em; }
.conti-brand-version { font-family: 'JetBrains Mono', monospace; font-size: 10px; color: var(--muted); margin-top: 1px; }

.conti-tools { display: flex; align-items: center; gap: 14px; flex: 1; min-width: 0; }
.conti-tool { display: flex; align-items: center; gap: 8px; flex-shrink: 0; }
.conti-tool-sep {
  width: 1px; height: 24px;
  background: var(--line);
  flex-shrink: 0;
}
.conti-tool-label {
  font-family: 'JetBrains Mono', monospace;
  font-size: 10px; letter-spacing: 0.08em;
  color: var(--muted); text-transform: uppercase;
  flex-shrink: 0;
}
.conti-tool input[type="range"] {
  -webkit-appearance: none; appearance: none;
  width: 100px; height: 4px;
  background: var(--line); border-radius: 999px;
  outline: none;
}
.conti-tool input[type="range"]::-webkit-slider-thumb {
  -webkit-appearance: none; appearance: none;
  width: 14px; height: 14px;
  background: var(--ink); border-radius: 50%;
  cursor: pointer; border: 2px solid var(--paper);
  box-shadow: 0 0 0 1px var(--ink);
}
.conti-tool input[type="range"]::-moz-range-thumb {
  width: 14px; height: 14px;
  background: var(--ink); border-radius: 50%;
  cursor: pointer; border: 2px solid var(--paper);
  box-shadow: 0 0 0 1px var(--ink);
}
.conti-num {
  width: 56px; padding: 4px 6px;
  font-family: 'JetBrains Mono', monospace;
  font-size: 12px;
  background: var(--paper);
  border: 1px solid var(--line);
  border-radius: 4px;
  text-align: right;
  color: var(--ink);
}
.conti-num:focus { outline: none; border-color: var(--ink); }
.conti-tool-unit {
  font-family: 'JetBrains Mono', monospace;
  font-size: 11px; color: var(--muted);
  margin-left: -4px;
}
.conti-pen-preview {
  width: 38px; height: 38px;
  display: flex; align-items: center; justify-content: center;
  background: var(--paper);
  border: 1px solid var(--line);
  border-radius: 50%;
  flex-shrink: 0;
}
.conti-pen-dot { border-radius: 50%; background: var(--ink); }

.conti-actions { display: flex; align-items: center; gap: 6px; flex-shrink: 0; }
.conti-icon-btn {
  display: flex; align-items: center; gap: 5px;
  padding: 5px 9px;
  font-family: 'JetBrains Mono', monospace;
  font-size: 11px; letter-spacing: 0.04em;
  color: var(--ink-2);
  background: transparent;
  border: 1px solid transparent;
  border-radius: 5px;
  transition: all 0.12s ease;
  text-transform: lowercase;
  white-space: nowrap;
  flex-shrink: 0;
}
.conti-icon-btn:hover:not(:disabled) { background: var(--bg-panel); border-color: var(--line); }
.conti-icon-btn:active:not(:disabled) { transform: translateY(1px); }
.conti-icon-btn:disabled { opacity: 0.35; cursor: not-allowed; }
.conti-icon-btn.active { background: var(--ink); color: var(--paper); border-color: var(--ink); }
.conti-icon-btn.danger:hover:not(:disabled) { color: var(--accent); border-color: var(--accent); }
.conti-icon-btn.accent { background: var(--accent); color: var(--paper); border-color: var(--accent); }

/* selection action bar */
.conti-sel-bar {
  display: flex; align-items: center; gap: 4px;
  padding: 3px 8px;
  background: var(--accent-soft);
  border: 1px solid rgba(196,58,44,0.25);
  border-radius: 6px;
  flex-shrink: 0;
}
.conti-sel-bar .conti-sel-label {
  font-family: 'JetBrains Mono', monospace;
  font-size: 10px; letter-spacing: 0.1em;
  color: var(--accent);
  text-transform: uppercase;
  margin-right: 4px;
}

/* main */
.conti-main { display: flex; flex: 1; min-height: 0; }

/* sidebar */
.conti-sidebar {
  width: 240px; flex: 0 0 240px;
  background: var(--bg-panel);
  border-right: 1px solid var(--line);
  overflow-y: auto;
  padding: 20px 18px;
}
.conti-sidebar.right {
  border-right: none;
  border-left: 1px solid var(--line);
  width: 220px; flex: 0 0 220px;
}
.conti-section { margin-bottom: 24px; }
.conti-section h3 {
  font-family: 'JetBrains Mono', monospace;
  font-size: 10px; letter-spacing: 0.14em;
  color: var(--muted);
  text-transform: uppercase;
  margin: 0 0 10px 0;
  display: flex; align-items: center; justify-content: space-between;
}
.conti-section h3 .count { color: var(--ink); }
.conti-section h3::before {
  content: ''; flex: 0 0 6px; height: 6px;
  background: var(--accent); border-radius: 50%;
  margin-right: 8px;
}

.conti-preset-grid { display: grid; grid-template-columns: 1fr 1fr; gap: 6px; }
.conti-preset {
  padding: 10px 8px;
  background: var(--paper);
  border: 1px solid var(--line);
  border-radius: 5px;
  font-family: 'JetBrains Mono', monospace;
  font-size: 11px; color: var(--ink);
  text-align: left;
  transition: all 0.12s ease;
  display: flex; flex-direction: column; gap: 2px;
}
.conti-preset:hover:not(:disabled) { background: var(--ink); color: var(--paper); border-color: var(--ink); }
.conti-preset:hover:not(:disabled) .conti-preset-sub { color: var(--paper); opacity: 0.6; }
.conti-preset:disabled { opacity: 0.4; cursor: not-allowed; }
.conti-preset-num { font-weight: 600; font-size: 13px; }
.conti-preset-sub { font-size: 9px; color: var(--muted); letter-spacing: 0.06em; text-transform: uppercase; }

.conti-config-row {
  display: flex; align-items: center; justify-content: space-between;
  padding: 8px 0;
  border-bottom: 1px dashed var(--line);
}
.conti-config-row:last-child { border-bottom: none; }
.conti-config-row label {
  font-family: 'JetBrains Mono', monospace;
  font-size: 11px; color: var(--muted);
}
.conti-config-row input {
  width: 70px; padding: 4px 6px;
  font-family: 'JetBrains Mono', monospace;
  font-size: 12px;
  background: var(--paper);
  border: 1px solid var(--line);
  border-radius: 4px;
  text-align: right;
  color: var(--ink);
}
.conti-config-row input:focus { outline: none; border-color: var(--ink); }
.conti-config-readonly {
  font-family: 'JetBrains Mono', monospace;
  font-size: 12px; color: var(--ink); font-weight: 600;
}

/* frame list (left sidebar) */
.conti-frame-row {
  display: flex; align-items: center; gap: 4px;
  padding: 6px 8px;
  background: var(--paper);
  border: 1px solid var(--line);
  border-radius: 5px;
  margin-bottom: 4px;
  cursor: pointer;
  transition: all 0.12s ease;
}
.conti-frame-row:hover { border-color: var(--ink-2); }
.conti-frame-row.active { background: var(--ink); border-color: var(--ink); }
.conti-frame-row.active input { color: var(--paper); }
.conti-frame-row.active .del { color: rgba(255,255,255,0.6); }
.conti-frame-row.active .del:hover:not(:disabled) { color: var(--paper); background: rgba(255,255,255,0.12); }
.conti-frame-row input {
  flex: 1; min-width: 0;
  padding: 2px 4px;
  font-family: 'Pretendard', sans-serif;
  font-size: 12px;
  background: transparent;
  border: 1px solid transparent;
  border-radius: 3px;
  color: var(--ink);
  cursor: text;
}
.conti-frame-row input:focus {
  outline: none;
  border-color: var(--line);
  background: var(--paper);
  color: var(--ink) !important;
}
.conti-frame-row .del {
  width: 22px; height: 22px;
  display: flex; align-items: center; justify-content: center;
  font-size: 14px;
  color: var(--muted);
  border-radius: 3px;
  flex-shrink: 0;
  transition: all 0.12s ease;
}
.conti-frame-row .del:hover:not(:disabled) { background: var(--accent-soft); color: var(--accent); }
.conti-frame-row .del:disabled { opacity: 0.3; cursor: not-allowed; }

.conti-add-btn {
  width: 100%;
  padding: 10px;
  margin-top: 4px;
  font-family: 'JetBrains Mono', monospace;
  font-size: 11px;
  color: var(--muted);
  background: transparent;
  border: 1px dashed var(--line);
  border-radius: 5px;
  transition: all 0.12s ease;
  letter-spacing: 0.04em;
}
.conti-add-btn:hover {
  color: var(--ink);
  border-color: var(--ink);
  border-style: solid;
  background: var(--paper);
}

/* canvas area */
.conti-canvas-area {
  flex: 1; min-width: 0;
  background:
    radial-gradient(circle at 1px 1px, var(--line) 1px, transparent 0) 0 0 / 24px 24px,
    var(--bg-canvas-area);
  overflow: auto;
  position: relative;
}
.conti-canvas-inner {
  display: flex;
  align-items: flex-start;
  gap: 140px;
  padding: 56px 100px 200px 100px;
  width: max-content;
  min-width: 100%;
}

/* frame */
.conti-frame {
  position: relative;
  flex-shrink: 0;
  display: flex;
  flex-direction: column;
}
.conti-frame-label {
  font-family: 'JetBrains Mono', monospace;
  font-size: 12px;
  color: var(--muted);
  padding: 0 0 8px 2px;
  cursor: pointer;
  user-select: none;
  letter-spacing: 0.04em;
  transition: color 0.12s ease;
}
.conti-frame-label:hover { color: var(--ink-2); }
.conti-frame.selected .conti-frame-label { color: var(--accent); font-weight: 600; }
.conti-frame-stage {
  position: relative;
  background: var(--gap);
  box-shadow:
    0 1px 2px rgba(0,0,0,0.04),
    0 4px 12px rgba(0,0,0,0.06),
    0 16px 40px rgba(0,0,0,0.08);
  transition: outline 0.12s ease;
}
.conti-frame.selected .conti-frame-stage {
  outline: 2px solid var(--accent);
  outline-offset: 4px;
}
.conti-block { position: absolute; pointer-events: none; }
.conti-block.cut { background: var(--cut); }
.conti-block.gap { background: var(--gap); }

.conti-frame-canvas {
  position: absolute; top: 0; left: 0;
  display: block;
  pointer-events: none;
}
/* Overlay canvas: sits on top, handles all events */
.conti-frame-overlay {
  position: absolute; top: 0; left: 0;
  display: block;
  z-index: 5;
}
.conti-frame-overlay.tool-pen { cursor: crosshair; }
.conti-frame-overlay.tool-lasso { cursor: cell; }
.conti-frame-overlay.tool-lasso-selected { cursor: move; }

/* dimension labels */
.conti-dim {
  position: absolute;
  display: flex; align-items: center;
  pointer-events: none;
  white-space: nowrap;
}
.conti-dim-bracket {
  width: 12px; flex-shrink: 0;
  position: relative; height: 100%;
}
.conti-dim-bracket::before, .conti-dim-bracket::after {
  content: ''; position: absolute; left: 0;
  width: 12px; height: 1px;
  background: var(--accent);
}
.conti-dim-bracket::before { top: 0; }
.conti-dim-bracket::after { bottom: 0; }
.conti-dim-bracket .vline {
  position: absolute; left: 0; top: 0; bottom: 0;
  width: 1px; background: var(--accent);
}
.conti-dim-text {
  margin-left: 8px;
  font-family: 'JetBrains Mono', monospace;
  font-size: 11px;
  display: flex; flex-direction: column; gap: 1px;
}
.conti-dim-kind {
  font-size: 9px; letter-spacing: 0.08em;
  color: var(--muted); text-transform: uppercase;
}
.conti-dim-size { font-weight: 600; color: var(--ink); }
.conti-dim.gap .conti-dim-bracket::before,
.conti-dim.gap .conti-dim-bracket::after,
.conti-dim.gap .vline { background: var(--muted); }
.conti-dim.gap .conti-dim-size { color: var(--muted); }

/* block list (right sidebar) */
.conti-block-row {
  position: relative;
  display: flex; align-items: center; gap: 6px;
  padding: 6px 8px;
  background: var(--paper);
  border: 1px solid var(--line);
  border-radius: 5px;
  margin-bottom: 4px;
  transition: border-color 0.12s ease, opacity 0.15s ease;
}
.conti-block-row:hover { border-color: var(--ink-2); }
.conti-block-row.dragging {
  opacity: 0.35;
  border-color: var(--accent);
  border-style: dashed;
}
.conti-block-row .drop-indicator {
  position: absolute;
  left: -2px; right: -2px;
  height: 3px;
  background: var(--accent);
  border-radius: 2px;
  z-index: 5;
  pointer-events: none;
  box-shadow: 0 0 0 1px var(--paper);
}
.conti-block-row .drop-indicator::before,
.conti-block-row .drop-indicator::after {
  content: '';
  position: absolute;
  top: 50%; transform: translateY(-50%);
  width: 6px; height: 6px;
  border-radius: 50%;
  background: var(--accent);
}
.conti-block-row .drop-indicator::before { left: -3px; }
.conti-block-row .drop-indicator::after { right: -3px; }
.conti-block-row .drop-indicator.above { top: -4px; }
.conti-block-row .drop-indicator.below { bottom: -4px; }

.conti-drag-handle {
  width: 14px; height: 22px;
  display: flex; align-items: center; justify-content: center;
  flex-shrink: 0;
  color: var(--muted);
  cursor: grab;
  border-radius: 3px;
  touch-action: none;
  transition: color 0.12s ease, background 0.12s ease;
}
.conti-drag-handle:hover { color: var(--ink); background: var(--bg-panel); }
.conti-drag-handle:active { cursor: grabbing; }
.conti-block-row.dragging .conti-drag-handle { cursor: grabbing; color: var(--accent); }

.conti-block-tag {
  font-family: 'JetBrains Mono', monospace;
  font-size: 9px; letter-spacing: 0.06em;
  text-transform: uppercase;
  padding: 2px 5px;
  border-radius: 3px;
  flex-shrink: 0;
}
.conti-block-tag.cut { background: var(--ink); color: var(--paper); }
.conti-block-tag.gap { background: var(--accent-soft); color: var(--accent); }
.conti-block-row input {
  width: 100%; min-width: 0; flex: 1;
  padding: 2px 4px;
  font-family: 'JetBrains Mono', monospace;
  font-size: 11px;
  background: transparent;
  border: 1px solid transparent;
  border-radius: 3px;
  text-align: right;
  color: var(--ink);
}
.conti-block-row input:focus { outline: none; border-color: var(--line); background: var(--bg-panel); }
.conti-block-row .del {
  width: 22px; height: 22px;
  display: flex; align-items: center; justify-content: center;
  font-size: 14px;
  color: var(--muted);
  border-radius: 3px;
  flex-shrink: 0;
  transition: all 0.12s ease;
}
.conti-block-row .del:hover { background: var(--accent-soft); color: var(--accent); }

.conti-empty {
  padding: 18px 12px;
  text-align: center;
  font-size: 12px;
  color: var(--muted);
  border: 1px dashed var(--line);
  border-radius: 5px;
}

/* margin sub-row (right sidebar, cut blocks only) */
.conti-block-margin-row {
  display: flex; align-items: center; gap: 4px;
  padding: 4px 8px 6px 8px;
  margin-top: -6px;
  margin-bottom: 4px;
  background: var(--bg-panel);
  border: 1px solid var(--line);
  border-top: none;
  border-radius: 0 0 5px 5px;
}
.conti-margin-label {
  font-family: 'JetBrains Mono', monospace;
  font-size: 9px; letter-spacing: 0.06em;
  color: var(--muted); text-transform: uppercase;
  flex-shrink: 0; width: 10px; text-align: center;
}
.conti-margin-sep {
  flex: 1;
  height: 1px;
  background: var(--line);
}
.conti-block-margin-row input {
  width: 42px; padding: 2px 4px;
  font-family: 'JetBrains Mono', monospace;
  font-size: 10px;
  background: var(--paper);
  border: 1px solid var(--line);
  border-radius: 3px;
  text-align: right;
  color: var(--ink);
  flex-shrink: 0;
}
.conti-block-margin-row input:focus { outline: none; border-color: var(--ink); }

/* tweak: cut block row gets a flat bottom when margin row follows */
.conti-block-row.has-margin { border-radius: 5px 5px 0 0; margin-bottom: 0; }


.conti-status {
  position: fixed; bottom: 12px; left: 50%;
  transform: translateX(-50%);
  display: flex; gap: 16px;
  padding: 6px 14px;
  background: rgba(22, 20, 15, 0.85);
  color: var(--paper);
  font-family: 'JetBrains Mono', monospace;
  font-size: 10px; letter-spacing: 0.06em;
  border-radius: 999px;
  backdrop-filter: blur(8px);
  -webkit-backdrop-filter: blur(8px);
  pointer-events: none;
  z-index: 10;
}
.conti-status .dot { width: 6px; height: 6px; background: #6fc275; border-radius: 50%; align-self: center; }
.conti-status .dot.lasso { background: var(--accent); }

/* viewport-active block highlight (right sidebar) */
.conti-block-row.viewport-active {
  border-color: var(--accent);
  background: var(--accent-soft);
  box-shadow: inset 3px 0 0 var(--accent);
}
.conti-block-row.viewport-active .conti-block-tag.cut {
  background: var(--accent);
}
.conti-block-row.viewport-active .conti-block-tag.gap {
  background: var(--accent);
  color: var(--paper);
}
.conti-block-row.viewport-active input {
  color: var(--accent);
  font-weight: 600;
}
.conti-block-margin-row.viewport-active {
  border-color: var(--accent);
  background: color-mix(in srgb, var(--accent-soft) 60%, var(--bg-panel));
  box-shadow: inset 3px 0 0 var(--accent);
}

@media (max-width: 900px) {
  .conti-sidebar.right { display: none; }
}
@media (max-width: 700px) {
  .conti-sidebar { width: 200px; flex: 0 0 200px; }
  .conti-tool input[type="range"] { width: 70px; }
}
`;

// ---------- FrameView ----------
const FrameView = forwardRef(function FrameView(
  {
    frame, isSelected, showDimensions, activeTool, selectionPhase,
    getBlockBitmap,
    onSelect,
    onPointerDown, onPointerMove, onPointerUp,
  },
  ref,
) {
  const canvasRef = useRef(null);
  const overlayRef = useRef(null);
  const dprRef = useRef(1);

  const totalHeight = useMemo(
    () => frame.blocks.reduce((s, b) => s + b.height, 0),
    [frame.blocks],
  );
  const cutWidth = Math.max(50, frame.canvasWidth - 2 * frame.sideMargin); // kept for left sidebar display only

  const blockLayout = useMemo(() => {
    let y = 0;
    let cutCounter = 0;
    let gapCounter = 0;
    return frame.blocks.map((b) => {
      const item = { ...b, top: y };
      if (b.type === 'cut') { cutCounter += 1; item.num = cutCounter; }
      else { gapCounter += 1; item.num = gapCounter; }
      y += b.height;
      return item;
    });
  }, [frame.blocks]);

  const redraw = useCallback(() => {
    const c = canvasRef.current;
    if (!c) return;
    const ctx = c.getContext('2d');
    const dpr = dprRef.current;
    ctx.clearRect(0, 0, c.width / dpr, c.height / dpr);

    let y = 0;
    for (const b of frame.blocks) {
      const entry = getBlockBitmap(b.id);
      if (entry) {
        ctx.drawImage(
          entry.canvas,
          0, 0,
          entry.canvas.width, entry.canvas.height,
          0, y - BITMAP_Y_PADDING,
          entry.logicalWidth, entry.logicalHeight,
        );
      }
      y += b.height;
    }
  }, [frame.blocks, getBlockBitmap]);

  useLayoutEffect(() => {
    const dpr = Math.min(window.devicePixelRatio || 1, DPR_CAP);
    dprRef.current = dpr;

    // Main canvas
    const c = canvasRef.current;
    if (c) {
      c.width = Math.max(1, frame.canvasWidth * dpr);
      c.height = Math.max(1, totalHeight * dpr);
      c.style.width = `${frame.canvasWidth}px`;
      c.style.height = `${totalHeight}px`;
      const ctx = c.getContext('2d');
      ctx.setTransform(1, 0, 0, 1, 0, 0);
      ctx.scale(dpr, dpr);
      ctx.lineCap = 'round';
      ctx.lineJoin = 'round';
    }

    // Overlay canvas
    const oc = overlayRef.current;
    if (oc) {
      oc.width = Math.max(1, frame.canvasWidth * dpr);
      oc.height = Math.max(1, totalHeight * dpr);
      oc.style.width = `${frame.canvasWidth}px`;
      oc.style.height = `${totalHeight}px`;
    }

    redraw();
  }, [frame.canvasWidth, totalHeight, redraw]);

  useImperativeHandle(ref, () => ({
    redraw,
    getMainCanvas: () => canvasRef.current,
    getOverlayCanvas: () => overlayRef.current,
    getDpr: () => dprRef.current,
    clearOverlay: () => {
      const oc = overlayRef.current;
      if (!oc) return;
      const ctx = oc.getContext('2d');
      ctx.clearRect(0, 0, oc.width, oc.height);
    },
  }), [redraw]);

  // Determine overlay cursor class
  let overlayCursorClass = 'tool-pen';
  if (activeTool === 'lasso') {
    if (selectionPhase === 'selected' || selectionPhase === 'dragging'
      || selectionPhase === 'resizing' || selectionPhase === 'rotating') {
      overlayCursorClass = 'tool-lasso-selected';
    } else {
      overlayCursorClass = 'tool-lasso';
    }
  }

  const handleDown = (e) => {
    onSelect(frame.id);
    onPointerDown(e, frame.id, overlayRef.current);
  };

  return (
    <div className={`conti-frame ${isSelected ? 'selected' : ''}`} data-frame-id={frame.id}>
      <div className="conti-frame-label" onClick={() => onSelect(frame.id)}>
        {frame.name}
      </div>
      <div
        className="conti-frame-stage"
        style={{ width: `${frame.canvasWidth}px`, height: `${totalHeight}px` }}
      >
        {blockLayout.map((b) => {
          const ml = b.type === 'cut' ? (b.marginLeft ?? frame.sideMargin) : 0;
          const mr = b.type === 'cut' ? (b.marginRight ?? frame.sideMargin) : 0;
          const bw = b.type === 'cut' ? Math.max(10, frame.canvasWidth - ml - mr) : frame.canvasWidth;
          return (
            <div
              key={`bg-${b.id}`}
              className={`conti-block ${b.type}`}
              style={{
                top: `${b.top}px`,
                left: `${ml}px`,
                width: `${bw}px`,
                height: `${b.height}px`,
              }}
            />
          );
        })}
        {/* Main drawing canvas (pointer-events none, driven by overlay) */}
        <canvas
          ref={canvasRef}
          className="conti-frame-canvas"
          style={{ touchAction: 'none' }}
        />
        {/* Overlay: handles all pointer events */}
        <canvas
          ref={overlayRef}
          className={`conti-frame-overlay ${overlayCursorClass}`}
          style={{ touchAction: 'none' }}
          onPointerDown={handleDown}
          onPointerMove={(e) => onPointerMove(e, overlayRef.current)}
          onPointerUp={(e) => onPointerUp(e, overlayRef.current)}
          onPointerCancel={(e) => onPointerUp(e, overlayRef.current)}
          onPointerLeave={(e) => onPointerUp(e, overlayRef.current)}
        />
        {showDimensions && blockLayout.map((b) => (
          <div
            key={`dim-${b.id}`}
            className={`conti-dim ${b.type}`}
            style={{
              top: `${b.top}px`,
              height: `${b.height}px`,
              left: `${frame.canvasWidth + 10}px`,
            }}
          >
            <div className="conti-dim-bracket"><div className="vline" /></div>
            <div className="conti-dim-text">
              <span className="conti-dim-kind">
                {b.type === 'cut' ? `cut ${String(b.num).padStart(2, '0')}` : 'gap'}
              </span>
              <span className="conti-dim-size">{b.height}px</span>
            </div>
          </div>
        ))}
      </div>
    </div>
  );
});

// ---------- main ----------
export default function ContiProgram() {
  const [frames, setFrames] = useState(() => [makeStarterFrame('Frame 1')]);
  const [selectedFrameId, setSelectedFrameId] = useState(() => frames[0].id);
  const selectedFrame = frames.find((f) => f.id === selectedFrameId) || null;

  // Per-frame drawing state.
  const strokesByFrameRef = useRef({});
  const ensureFrameStore = useCallback((fid) => {
    if (!strokesByFrameRef.current[fid]) {
      strokesByFrameRef.current[fid] = { byBlock: {}, bitmaps: {}, history: [] };
    }
    return strokesByFrameRef.current[fid];
  }, []);
  for (const f of frames) ensureFrameStore(f.id);

  // Pen state
  const [penSize, setPenSize] = useState(4);
  const [penOpacity, setPenOpacity] = useState(100);

  // Tool state
  const [activeTool, setActiveTool] = useState('pen'); // 'pen' | 'lasso'
  const [hasSelection, setHasSelection] = useState(false);
  const [hasClipboard, setHasClipboard] = useState(false);
  const [selectionPhase, setSelectionPhase] = useState('idle');

  // Drawing in-progress state.
  const drawingRef = useRef(null);
  const currentStrokeRef = useRef(null);

  // Lasso state machine
  const lassoRef = useRef({
    phase: 'idle', // 'idle'|'drawing'|'selected'|'dragging'|'resizing'|'rotating'
    frameId: null,
    lassoPoints: [],
    selectedItems: [],  // { stroke, blockId, blockTop, framePoints }
    bbox: null,         // { minX, minY, maxX, maxY, cx, cy }
    transform: { tx: 0, ty: 0, scaleX: 1, scaleY: 1, angle: 0, flipH: false, flipV: false },
    dragStart: null,
    origTransform: null,
    dragHandle: null,
    origHandleDist: null,
  });

  // Clipboard (copy/paste)
  const clipboardRef = useRef(null);

  // Multi-touch pan tracking.
  const canvasAreaRef = useRef(null);
  const activeTouchPointersRef = useRef(new Map());
  const panStateRef = useRef(null);

  // Imperative handles to each FrameView
  const frameRefs = useRef({});

  const selectAndScrollToFrame = useCallback((frameId) => {
    setSelectedFrameId(frameId);
    const area = canvasAreaRef.current;
    if (!area) return;
    const el = area.querySelector(`[data-frame-id="${frameId}"]`);
    if (!el) return;
    const areaRect = area.getBoundingClientRect();
    const elRect = el.getBoundingClientRect();
    area.scrollTo({
      left: area.scrollLeft + elRect.left - areaRect.left - 80,
      top: 0,
      behavior: 'smooth',
    });
  }, []);

  // ---------- block bitmap management ----------
  const getBitmapDpr = useCallback(
    () => Math.min(window.devicePixelRatio || 1, DPR_CAP),
    [],
  );

  const ensureBlockBitmap = useCallback((frameId, block, frameWidth, neededLocalMaxY) => {
    const store = ensureFrameStore(frameId);
    const dpr = getBitmapDpr();
    const required = Math.max(
      block.height,
      neededLocalMaxY ?? 0,
    ) + 2 * BITMAP_Y_PADDING;
    const targetH = Math.ceil(required / BITMAP_GROW_CHUNK) * BITMAP_GROW_CHUNK;

    let entry = store.bitmaps[block.id];
    const widthMismatch = entry && entry.logicalWidth !== frameWidth;
    const tooShort = entry && entry.logicalHeight < required;

    if (!entry) {
      entry = createBlockBitmap(frameWidth, targetH, dpr);
      store.bitmaps[block.id] = entry;
    } else if (widthMismatch || tooShort) {
      const next = createBlockBitmap(
        frameWidth,
        Math.max(targetH, entry.logicalHeight),
        dpr,
      );
      blitBitmap(entry, next.ctx);
      store.bitmaps[block.id] = next;
      entry = next;
    }
    return entry;
  }, [ensureFrameStore, getBitmapDpr]);

  const clearBlockBitmap = useCallback((frameId, blockId) => {
    const store = ensureFrameStore(frameId);
    const entry = store.bitmaps[blockId];
    if (!entry) return;
    entry.ctx.save();
    entry.ctx.setTransform(1, 0, 0, 1, 0, 0);
    entry.ctx.clearRect(0, 0, entry.canvas.width, entry.canvas.height);
    entry.ctx.restore();
  }, [ensureFrameStore]);

  // Rebuild a block's bitmap (skips hidden strokes — used during lasso selection)
  const rebuildBlockBitmap = useCallback((frameId, block, frameWidth) => {
    const store = ensureFrameStore(frameId);
    const strokes = store.byBlock[block.id] || [];
    let maxY = 0;
    for (const s of strokes) {
      if (s.hidden) continue;
      if (s.bbox && s.bbox.maxY > maxY) maxY = s.bbox.maxY;
    }
    const entry = ensureBlockBitmap(frameId, block, frameWidth, maxY);
    clearBlockBitmap(frameId, block.id);
    for (const s of strokes) {
      if (s.hidden) continue;
      renderStrokeToCtx(entry.ctx, s, BITMAP_Y_PADDING);
    }
  }, [ensureFrameStore, ensureBlockBitmap, clearBlockBitmap]);

  const getBlockBitmapRef = useRef({});
  for (const f of frames) {
    if (!getBlockBitmapRef.current[f.id]) {
      const fid = f.id;
      getBlockBitmapRef.current[fid] = (blockId) => {
        const store = strokesByFrameRef.current[fid];
        return store ? store.bitmaps[blockId] || null : null;
      };
    }
  }

  // Block-row drag state.
  const [dragId, setDragId] = useState(null);
  const [dragOverId, setDragOverId] = useState(null);
  const [dragOverPos, setDragOverPos] = useState(null);
  const blockListRef = useRef(null);

  // Viewport-center active block tracking.
  const [activeBlockId, setActiveBlockId] = useState(null);

  // ---------- coord helper ----------
  const getCanvasPoint = (e, canvasEl, frame) => {
    const rect = canvasEl.getBoundingClientRect();
    const totalH = frame.blocks.reduce((s, b) => s + b.height, 0);
    const sx = frame.canvasWidth / rect.width;
    const sy = totalH / rect.height;
    return {
      x: (e.clientX - rect.left) * sx,
      y: (e.clientY - rect.top) * sy,
    };
  };

  // =====================================================================
  //  LASSO: overlay rendering
  // =====================================================================
  const renderSelectionOverlay = (frameId) => {
    const fref = frameRefs.current[frameId];
    if (!fref) return;
    const oc = fref.getOverlayCanvas();
    if (!oc) return;
    const dpr = fref.getDpr();

    const ctx = oc.getContext('2d');
    ctx.clearRect(0, 0, oc.width, oc.height);

    const lasso = lassoRef.current;
    const { phase, lassoPoints, selectedItems, bbox, transform } = lasso;

    ctx.save();
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';

    // ---- Phase: drawing ----
    if (phase === 'drawing' && lassoPoints.length > 1) {
      ctx.strokeStyle = LASSO_COLOR;
      ctx.lineWidth = 1.5;
      ctx.setLineDash([5, 3]);
      ctx.globalAlpha = 0.85;
      ctx.beginPath();
      ctx.moveTo(lassoPoints[0].x, lassoPoints[0].y);
      for (let i = 1; i < lassoPoints.length; i++) {
        ctx.lineTo(lassoPoints[i].x, lassoPoints[i].y);
      }
      ctx.stroke();
      ctx.setLineDash([]);
      ctx.globalAlpha = 1;
    }

    // ---- Phase: selected / dragging / resizing / rotating ----
    if (bbox && ['selected', 'dragging', 'resizing', 'rotating'].includes(phase)) {
      const { cx, cy } = bbox;

      // Draw each selected stroke with the current transform applied
      for (const item of selectedItems) {
        const pts = item.framePoints.map(p =>
          applySelectionTransform(p.x, p.y, cx, cy, transform)
        );
        ctx.strokeStyle = `rgba(15, 15, 15, ${item.stroke.opacity})`;
        ctx.fillStyle = `rgba(15, 15, 15, ${item.stroke.opacity})`;
        ctx.lineWidth = item.stroke.size;
        if (pts.length === 1) {
          ctx.beginPath();
          ctx.arc(pts[0].x, pts[0].y, item.stroke.size / 2, 0, Math.PI * 2);
          ctx.fill();
        } else {
          ctx.beginPath();
          ctx.moveTo(pts[0].x, pts[0].y);
          for (let i = 1; i < pts.length; i++) ctx.lineTo(pts[i].x, pts[i].y);
          ctx.stroke();
        }
      }

      // Draw selection bounding box
      const handles = getHandlePositions(bbox, transform);
      const corners = [handles.tl, handles.tr, handles.br, handles.bl];

      ctx.strokeStyle = LASSO_COLOR;
      ctx.lineWidth = 1.5;
      ctx.setLineDash([5, 3]);
      ctx.globalAlpha = 0.9;
      ctx.beginPath();
      ctx.moveTo(corners[0].x, corners[0].y);
      for (let i = 1; i < corners.length; i++) ctx.lineTo(corners[i].x, corners[i].y);
      ctx.closePath();
      ctx.stroke();
      ctx.setLineDash([]);
      ctx.globalAlpha = 1;

      // Line from tc to rotate handle
      ctx.strokeStyle = LASSO_COLOR;
      ctx.lineWidth = 1;
      ctx.globalAlpha = 0.5;
      ctx.beginPath();
      ctx.moveTo(handles.tc.x, handles.tc.y);
      ctx.lineTo(handles.rotate.x, handles.rotate.y);
      ctx.stroke();
      ctx.globalAlpha = 1;

      // Resize handles (squares)
      for (const hid of ['tl', 'tr', 'br', 'bl', 'tc', 'bc', 'lc', 'rc']) {
        const h = handles[hid];
        const hs = HANDLE_SIZE;
        ctx.fillStyle = '#ffffff';
        ctx.strokeStyle = LASSO_COLOR;
        ctx.lineWidth = 1.5;
        ctx.beginPath();
        ctx.rect(h.x - hs / 2, h.y - hs / 2, hs, hs);
        ctx.fill();
        ctx.stroke();
      }

      // Rotation handle (circle)
      const r = handles.rotate;
      ctx.fillStyle = LASSO_COLOR;
      ctx.strokeStyle = '#ffffff';
      ctx.lineWidth = 1.5;
      ctx.beginPath();
      ctx.arc(r.x, r.y, HANDLE_SIZE / 2 + 2, 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();
    }

    ctx.restore();
  };

  // =====================================================================
  //  LASSO: select strokes inside polygon
  // =====================================================================
  const selectStrokesInLasso = (frameId) => {
    const lasso = lassoRef.current;
    const frame = frames.find(f => f.id === frameId);
    if (!frame) return;
    const store = ensureFrameStore(frameId);
    const tops = computeBlockTops(frame.blocks);

    const selectedItems = [];
    const dirtyBlocks = new Set();

    for (const block of frame.blocks) {
      const blockTop = tops[block.id];
      const strokes = store.byBlock[block.id] || [];
      for (const stroke of strokes) {
        if (stroke.hidden) continue;
        // Use centroid of stroke bbox in frame coords for hit test
        const centX = (stroke.bbox.minX + stroke.bbox.maxX) / 2;
        const centY = (stroke.bbox.minY + stroke.bbox.maxY) / 2 + blockTop;
        if (pointInPolygon(centX, centY, lasso.lassoPoints)) {
          selectedItems.push({
            stroke,
            blockId: block.id,
            blockTop,
            framePoints: stroke.points.map(p => ({ x: p.x, y: p.y + blockTop })),
          });
          stroke.hidden = true;
          dirtyBlocks.add(block.id);
        }
      }
    }

    if (selectedItems.length === 0) {
      lasso.phase = 'idle';
      frameRefs.current[frameId]?.clearOverlay();
      setHasSelection(false);
      setSelectionPhase('idle');
      return;
    }

    // Compute bbox in frame coords
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    for (const item of selectedItems) {
      for (const p of item.framePoints) {
        if (p.x < minX) minX = p.x;
        if (p.y < minY) minY = p.y;
        if (p.x > maxX) maxX = p.x;
        if (p.y > maxY) maxY = p.y;
      }
    }
    // Add a little margin for stroke width
    const maxSz = Math.max(...selectedItems.map(i => i.stroke.size / 2));
    minX -= maxSz; minY -= maxSz;
    maxX += maxSz; maxY += maxSz;

    lasso.selectedItems = selectedItems;
    lasso.bbox = { minX, minY, maxX, maxY, cx: (minX + maxX) / 2, cy: (minY + maxY) / 2 };
    lasso.transform = { tx: 0, ty: 0, scaleX: 1, scaleY: 1, angle: 0, flipH: false, flipV: false };
    lasso.phase = 'selected';

    // Rebuild dirty blocks (hides selected strokes from main canvas)
    for (const blockId of dirtyBlocks) {
      const block = frame.blocks.find(b => b.id === blockId);
      if (block) rebuildBlockBitmap(frameId, block, frame.canvasWidth);
    }
    frameRefs.current[frameId]?.redraw();

    setHasSelection(true);
    setSelectionPhase('selected');
    renderSelectionOverlay(frameId);
  };

  // =====================================================================
  //  LASSO: apply selection (commit transformed strokes back to blocks)
  // =====================================================================
  const applyLassoSelection = (frameId, frame) => {
    const lasso = lassoRef.current;
    if (!lasso.selectedItems || lasso.selectedItems.length === 0) {
      cancelLassoSelection(frameId, frame);
      return;
    }

    const store = ensureFrameStore(frameId);
    const { bbox, transform, selectedItems } = lasso;
    const { cx, cy } = bbox;
    const tops = computeBlockTops(frame.blocks);
    const dirtyBlocks = new Set();

    for (const item of selectedItems) {
      // Remove hidden original from its block
      const origArr = store.byBlock[item.blockId];
      if (origArr) {
        const idx = origArr.indexOf(item.stroke);
        if (idx >= 0) origArr.splice(idx, 1);
        dirtyBlocks.add(item.blockId);
      }

      // Apply transform to get new frame-coord points
      const newFramePts = item.framePoints.map(p =>
        applySelectionTransform(p.x, p.y, cx, cy, transform)
      );

      // Find which block the transformed centroid belongs to
      const centX = newFramePts.reduce((s, p) => s + p.x, 0) / newFramePts.length;
      const centY = newFramePts.reduce((s, p) => s + p.y, 0) / newFramePts.length;
      const probe = { points: [{ x: centX, y: centY }] };
      const newBlockId = findStrokeBlockId(probe, frame.blocks, tops);
      if (newBlockId == null) continue;

      const newBlockTop = tops[newBlockId];
      const newLocalPts = newFramePts.map(p => ({ x: p.x, y: p.y - newBlockTop }));
      const newStroke = {
        points: newLocalPts,
        size: item.stroke.size,
        opacity: item.stroke.opacity,
        bbox: computeBbox(newLocalPts),
        hidden: false,
      };

      if (!store.byBlock[newBlockId]) store.byBlock[newBlockId] = [];
      store.byBlock[newBlockId].push(newStroke);
      store.history.push({ blockId: newBlockId });
      dirtyBlocks.add(newBlockId);
    }

    // Rebuild all dirty bitmaps
    for (const blockId of dirtyBlocks) {
      const block = frame.blocks.find(b => b.id === blockId);
      if (block) rebuildBlockBitmap(frameId, block, frame.canvasWidth);
    }
    frameRefs.current[frameId]?.redraw();

    // Reset
    lasso.phase = 'idle';
    lasso.selectedItems = [];
    lasso.bbox = null;
    lasso.frameId = null;
    frameRefs.current[frameId]?.clearOverlay();
    setHasSelection(false);
    setSelectionPhase('idle');
  };

  // =====================================================================
  //  LASSO: cancel selection (restore strokes, no transform applied)
  // =====================================================================
  const cancelLassoSelection = (frameId, frame) => {
    const lasso = lassoRef.current;
    const store = ensureFrameStore(frameId);
    const dirtyBlocks = new Set();

    for (const item of lasso.selectedItems || []) {
      item.stroke.hidden = false;
      dirtyBlocks.add(item.blockId);
    }

    const fr = frame || frames.find(f => f.id === frameId);
    for (const blockId of dirtyBlocks) {
      const block = fr?.blocks.find(b => b.id === blockId);
      if (block) rebuildBlockBitmap(frameId, block, fr.canvasWidth);
    }
    frameRefs.current[frameId]?.redraw();

    lasso.phase = 'idle';
    lasso.selectedItems = [];
    lasso.bbox = null;
    lasso.frameId = null;
    frameRefs.current[frameId]?.clearOverlay();
    setHasSelection(false);
    setSelectionPhase('idle');
  };

  // =====================================================================
  //  LASSO: copy
  // =====================================================================
  const copySelection = () => {
    const lasso = lassoRef.current;
    if (!lasso.selectedItems || lasso.selectedItems.length === 0) return;
    const { bbox, transform, selectedItems } = lasso;
    const { cx, cy } = bbox;

    clipboardRef.current = selectedItems.map(item => ({
      size: item.stroke.size,
      opacity: item.stroke.opacity,
      framePoints: item.framePoints.map(p =>
        applySelectionTransform(p.x, p.y, cx, cy, transform)
      ),
    }));
    setHasClipboard(true);
  };

  // =====================================================================
  //  LASSO: paste
  // =====================================================================
  const pasteSelection = () => {
    const cb = clipboardRef.current;
    if (!cb || cb.length === 0 || !selectedFrame) return;

    const OFFSET = 24;
    const store = ensureFrameStore(selectedFrameId);
    const tops = computeBlockTops(selectedFrame.blocks);
    const dirtyBlocks = new Set();

    for (const item of cb) {
      const offsetPts = item.framePoints.map(p => ({ x: p.x + OFFSET, y: p.y + OFFSET }));
      const centX = offsetPts.reduce((s, p) => s + p.x, 0) / offsetPts.length;
      const centY = offsetPts.reduce((s, p) => s + p.y, 0) / offsetPts.length;
      const probe = { points: [{ x: centX, y: centY }] };
      const blockId = findStrokeBlockId(probe, selectedFrame.blocks, tops);
      if (blockId == null) continue;

      const blockTop = tops[blockId];
      const localPts = offsetPts.map(p => ({ x: p.x, y: p.y - blockTop }));
      const newStroke = {
        points: localPts,
        size: item.size,
        opacity: item.opacity,
        bbox: computeBbox(localPts),
        hidden: false,
      };
      if (!store.byBlock[blockId]) store.byBlock[blockId] = [];
      store.byBlock[blockId].push(newStroke);
      store.history.push({ blockId });
      dirtyBlocks.add(blockId);
    }

    for (const blockId of dirtyBlocks) {
      const block = selectedFrame.blocks.find(b => b.id === blockId);
      if (block) rebuildBlockBitmap(selectedFrameId, block, selectedFrame.canvasWidth);
    }
    frameRefs.current[selectedFrameId]?.redraw();
  };

  // =====================================================================
  //  LASSO: flip H/V
  // =====================================================================
  const flipSelection = (axis) => {
    const lasso = lassoRef.current;
    if (!['selected', 'dragging', 'resizing', 'rotating'].includes(lasso.phase)) return;
    if (axis === 'h') {
      lasso.transform = { ...lasso.transform, flipH: !lasso.transform.flipH };
    } else {
      lasso.transform = { ...lasso.transform, flipV: !lasso.transform.flipV };
    }
    renderSelectionOverlay(lasso.frameId);
  };

  // =====================================================================
  //  LASSO: rotate by degrees
  // =====================================================================
  const rotateSelectionDeg = (deg) => {
    const lasso = lassoRef.current;
    if (!['selected', 'dragging', 'resizing', 'rotating'].includes(lasso.phase)) return;
    lasso.transform = {
      ...lasso.transform,
      angle: lasso.transform.angle + deg * Math.PI / 180,
    };
    renderSelectionOverlay(lasso.frameId);
  };

  // =====================================================================
  //  LASSO: delete selection
  // =====================================================================
  const deleteSelection = () => {
    const lasso = lassoRef.current;
    if (!lasso.selectedItems || lasso.selectedItems.length === 0) return;
    const frameId = lasso.frameId;
    const frame = frames.find(f => f.id === frameId);
    const store = ensureFrameStore(frameId);
    const dirtyBlocks = new Set();

    for (const item of lasso.selectedItems) {
      const arr = store.byBlock[item.blockId];
      if (arr) {
        const idx = arr.indexOf(item.stroke);
        if (idx >= 0) arr.splice(idx, 1);
        dirtyBlocks.add(item.blockId);
      }
    }

    for (const blockId of dirtyBlocks) {
      const block = frame?.blocks.find(b => b.id === blockId);
      if (block) rebuildBlockBitmap(frameId, block, frame.canvasWidth);
    }
    frameRefs.current[frameId]?.redraw();

    lasso.phase = 'idle';
    lasso.selectedItems = [];
    lasso.bbox = null;
    lasso.frameId = null;
    frameRefs.current[frameId]?.clearOverlay();
    setHasSelection(false);
    setSelectionPhase('idle');
  };

  // =====================================================================
  //  LASSO: pointer handlers
  // =====================================================================
  const handleLassoPointerDown = (e, frameId, overlayEl) => {
    // Two-finger touch → pan (same as pen mode)
    if (e.pointerType === 'touch') {
      activeTouchPointersRef.current.set(e.pointerId, { x: e.clientX, y: e.clientY });
      if (activeTouchPointersRef.current.size >= 2) {
        const lasso = lassoRef.current;
        if (lasso.phase === 'drawing') {
          lasso.phase = 'idle';
          frameRefs.current[frameId]?.clearOverlay();
          setSelectionPhase('idle');
        }
        if (!panStateRef.current) {
          const pts = [...activeTouchPointersRef.current.values()];
          const avgX = pts.reduce((s, p) => s + p.x, 0) / pts.length;
          const avgY = pts.reduce((s, p) => s + p.y, 0) / pts.length;
          panStateRef.current = { lastX: avgX, lastY: avgY };
        }
        try { overlayEl?.releasePointerCapture(e.pointerId); } catch (_) {}
        return;
      }
    }

    e.preventDefault();
    const frame = frames.find(f => f.id === frameId);
    if (!frame || !overlayEl) return;
    const p = getCanvasPoint(e, overlayEl, frame);
    const lasso = lassoRef.current;

    // If there's a selection in ANOTHER frame, apply it first
    if (lasso.frameId && lasso.frameId !== frameId &&
        ['selected', 'dragging', 'resizing', 'rotating'].includes(lasso.phase)) {
      const prevFrame = frames.find(f => f.id === lasso.frameId);
      if (prevFrame) applyLassoSelection(lasso.frameId, prevFrame);
    }

    // If already selected in this frame, check handle/move/deselect
    if (lasso.frameId === frameId &&
        ['selected', 'dragging', 'resizing', 'rotating'].includes(lasso.phase)) {
      const handles = getHandlePositions(lasso.bbox, lasso.transform);
      const hitHandle = hitTestHandles(p.x, p.y, handles);

      if (hitHandle === 'rotate') {
        lasso.phase = 'rotating';
        lasso.dragStart = p;
        lasso.origTransform = { ...lasso.transform };
        setSelectionPhase('rotating');
        try { overlayEl.setPointerCapture(e.pointerId); } catch (_) {}
        return;
      }

      if (hitHandle) {
        lasso.phase = 'resizing';
        lasso.dragHandle = hitHandle;
        lasso.dragStart = p;
        lasso.origTransform = { ...lasso.transform };
        // Compute handle-to-(transformed)center distance for scale reference
        const { cx, cy } = lasso.bbox;
        const cxT = cx + lasso.transform.tx;
        const cyT = cy + lasso.transform.ty;
        lasso.origHandleDist = { x: handles[hitHandle].x - cxT, y: handles[hitHandle].y - cyT };
        setSelectionPhase('resizing');
        try { overlayEl.setPointerCapture(e.pointerId); } catch (_) {}
        return;
      }

      // Check if inside bbox quad
      const inside = pointInPolygon(p.x, p.y, [handles.tl, handles.tr, handles.br, handles.bl]);
      if (inside) {
        lasso.phase = 'dragging';
        lasso.dragStart = p;
        lasso.origTransform = { ...lasso.transform };
        setSelectionPhase('dragging');
        try { overlayEl.setPointerCapture(e.pointerId); } catch (_) {}
        return;
      }

      // Clicked outside → apply selection, fall through to start new lasso
      applyLassoSelection(frameId, frame);
    }

    // Start new lasso
    lasso.phase = 'drawing';
    lasso.frameId = frameId;
    lasso.lassoPoints = [p];
    lasso.selectedItems = [];
    lasso.bbox = null;
    lasso.transform = { tx: 0, ty: 0, scaleX: 1, scaleY: 1, angle: 0, flipH: false, flipV: false };
    setSelectionPhase('drawing');
    try { overlayEl.setPointerCapture(e.pointerId); } catch (_) {}
    renderSelectionOverlay(frameId);
  };

  const handleLassoPointerMove = (e, overlayEl) => {
    // Two-finger pan
    if (e.pointerType === 'touch') {
      if (activeTouchPointersRef.current.has(e.pointerId)) {
        activeTouchPointersRef.current.set(e.pointerId, { x: e.clientX, y: e.clientY });
      }
      if (activeTouchPointersRef.current.size >= 2) {
        if (panStateRef.current && canvasAreaRef.current) {
          const pts = [...activeTouchPointersRef.current.values()];
          const avgX = pts.reduce((s, p) => s + p.x, 0) / pts.length;
          const avgY = pts.reduce((s, p) => s + p.y, 0) / pts.length;
          const dx = avgX - panStateRef.current.lastX;
          const dy = avgY - panStateRef.current.lastY;
          canvasAreaRef.current.scrollLeft -= dx;
          canvasAreaRef.current.scrollTop -= dy;
          panStateRef.current = { lastX: avgX, lastY: avgY };
        }
        return;
      }
    }

    const lasso = lassoRef.current;
    if (lasso.phase === 'idle') return;
    if (!overlayEl) return;
    e.preventDefault();

    const frame = frames.find(f => f.id === lasso.frameId);
    if (!frame) return;
    const p = getCanvasPoint(e, overlayEl, frame);

    if (lasso.phase === 'drawing') {
      lasso.lassoPoints.push(p);
      renderSelectionOverlay(lasso.frameId);
      return;
    }

    if (lasso.phase === 'dragging') {
      const dx = p.x - lasso.dragStart.x;
      const dy = p.y - lasso.dragStart.y;
      lasso.transform = {
        ...lasso.origTransform,
        tx: lasso.origTransform.tx + dx,
        ty: lasso.origTransform.ty + dy,
      };
      renderSelectionOverlay(lasso.frameId);
      return;
    }

    if (lasso.phase === 'resizing') {
      const { cx, cy } = lasso.bbox;
      const cxT = cx + lasso.origTransform.tx;
      const cyT = cy + lasso.origTransform.ty;
      const hid = lasso.dragHandle;
      const { origHandleDist } = lasso;

      // Current pointer vector from transformed center
      const dx = p.x - cxT;
      const dy = p.y - cyT;

      let newScaleX = lasso.origTransform.scaleX;
      let newScaleY = lasso.origTransform.scaleY;

      if (['tl', 'tr', 'bl', 'br'].includes(hid)) {
        if (Math.abs(origHandleDist.x) > 1) {
          newScaleX = Math.max(0.05, Math.abs(dx) / Math.abs(origHandleDist.x))
            * Math.sign(lasso.origTransform.scaleX);
        }
        if (Math.abs(origHandleDist.y) > 1) {
          newScaleY = Math.max(0.05, Math.abs(dy) / Math.abs(origHandleDist.y))
            * Math.sign(lasso.origTransform.scaleY);
        }
      } else if (['tc', 'bc'].includes(hid)) {
        if (Math.abs(origHandleDist.y) > 1) {
          newScaleY = Math.max(0.05, Math.abs(dy) / Math.abs(origHandleDist.y))
            * Math.sign(lasso.origTransform.scaleY);
        }
      } else if (['lc', 'rc'].includes(hid)) {
        if (Math.abs(origHandleDist.x) > 1) {
          newScaleX = Math.max(0.05, Math.abs(dx) / Math.abs(origHandleDist.x))
            * Math.sign(lasso.origTransform.scaleX);
        }
      }

      lasso.transform = { ...lasso.origTransform, scaleX: newScaleX, scaleY: newScaleY };
      renderSelectionOverlay(lasso.frameId);
      return;
    }

    if (lasso.phase === 'rotating') {
      const { cx, cy } = lasso.bbox;
      const cxT = cx + lasso.origTransform.tx;
      const cyT = cy + lasso.origTransform.ty;
      const startAngle = Math.atan2(lasso.dragStart.y - cyT, lasso.dragStart.x - cxT);
      const curAngle = Math.atan2(p.y - cyT, p.x - cxT);
      lasso.transform = {
        ...lasso.origTransform,
        angle: lasso.origTransform.angle + (curAngle - startAngle),
      };
      renderSelectionOverlay(lasso.frameId);
      return;
    }
  };

  const handleLassoPointerUp = (e, overlayEl) => {
    if (e.pointerType === 'touch') {
      activeTouchPointersRef.current.delete(e.pointerId);
      if (activeTouchPointersRef.current.size < 2) panStateRef.current = null;
    }

    const lasso = lassoRef.current;

    if (lasso.phase === 'drawing') {
      try { overlayEl?.releasePointerCapture(e.pointerId); } catch (_) {}
      if (lasso.lassoPoints.length >= 3) {
        selectStrokesInLasso(lasso.frameId);
      } else {
        lasso.phase = 'idle';
        frameRefs.current[lasso.frameId]?.clearOverlay();
        setSelectionPhase('idle');
      }
      return;
    }

    if (['dragging', 'resizing', 'rotating'].includes(lasso.phase)) {
      try { overlayEl?.releasePointerCapture(e.pointerId); } catch (_) {}
      lasso.phase = 'selected';
      setSelectionPhase('selected');
      renderSelectionOverlay(lasso.frameId);
      return;
    }
  };

  // =====================================================================
  //  Tool switch
  // =====================================================================
  const switchTool = (tool) => {
    if (tool === activeTool) return;
    // Apply any active selection before switching
    if (activeTool === 'lasso') {
      const lasso = lassoRef.current;
      if (lasso.phase !== 'idle' && lasso.frameId) {
        const fr = frames.find(f => f.id === lasso.frameId);
        if (['selected', 'dragging', 'resizing', 'rotating'].includes(lasso.phase)) {
          if (fr) applyLassoSelection(lasso.frameId, fr);
        } else {
          cancelLassoSelection(lasso.frameId, fr);
        }
      }
    }
    setActiveTool(tool);
  };

  // =====================================================================
  //  Keyboard shortcuts
  // =====================================================================
  useEffect(() => {
    const onKey = (e) => {
      const lasso = lassoRef.current;
      if (e.key === 'Escape' && lasso.phase !== 'idle' && lasso.frameId) {
        const fr = frames.find(f => f.id === lasso.frameId);
        if (['selected', 'dragging', 'resizing', 'rotating'].includes(lasso.phase)) {
          applyLassoSelection(lasso.frameId, fr);
        } else {
          cancelLassoSelection(lasso.frameId, fr);
        }
      }
    };
    window.addEventListener('keydown', onKey);
    return () => window.removeEventListener('keydown', onKey);
  });

  // ---------- pointer / drawing (pen) ----------
  const handlePointerDown = (e, frameId, overlayEl) => {
    if (activeTool === 'lasso') {
      handleLassoPointerDown(e, frameId, overlayEl);
      return;
    }

    // Two-finger pan
    if (e.pointerType === 'touch') {
      activeTouchPointersRef.current.set(e.pointerId, { x: e.clientX, y: e.clientY });
      if (activeTouchPointersRef.current.size >= 2) {
        if (drawingRef.current) {
          const cancelledFrameId = drawingRef.current.frameId;
          drawingRef.current = null;
          currentStrokeRef.current = null;
          frameRefs.current[cancelledFrameId]?.redraw();
        }
        if (!panStateRef.current) {
          const pts = [...activeTouchPointersRef.current.values()];
          const avgX = pts.reduce((s, p) => s + p.x, 0) / pts.length;
          const avgY = pts.reduce((s, p) => s + p.y, 0) / pts.length;
          panStateRef.current = { lastX: avgX, lastY: avgY };
        }
        try { overlayEl?.releasePointerCapture(e.pointerId); } catch (_) {}
        return;
      }
    }

    e.preventDefault();
    const frame = frames.find((f) => f.id === frameId);
    if (!frame || !overlayEl) return;
    try { overlayEl.setPointerCapture(e.pointerId); } catch (_) {}

    const p = getCanvasPoint(e, overlayEl, frame);
    drawingRef.current = { frameId };
    currentStrokeRef.current = {
      points: [p],
      size: penSize,
      opacity: penOpacity / 100,
    };

    // Draw on main canvas
    const mainCanvas = frameRefs.current[frameId]?.getMainCanvas();
    if (mainCanvas) {
      const ctx = mainCanvas.getContext('2d');
      ctx.fillStyle = `rgba(15, 15, 15, ${penOpacity / 100})`;
      ctx.beginPath();
      ctx.arc(p.x, p.y, penSize / 2, 0, Math.PI * 2);
      ctx.fill();
    }
  };

  const handlePointerMove = (e, overlayEl) => {
    if (activeTool === 'lasso') {
      handleLassoPointerMove(e, overlayEl);
      return;
    }

    // Two-finger pan
    if (e.pointerType === 'touch') {
      if (activeTouchPointersRef.current.has(e.pointerId)) {
        activeTouchPointersRef.current.set(e.pointerId, { x: e.clientX, y: e.clientY });
      }
      if (activeTouchPointersRef.current.size >= 2) {
        if (panStateRef.current && canvasAreaRef.current) {
          const pts = [...activeTouchPointersRef.current.values()];
          const avgX = pts.reduce((s, p) => s + p.x, 0) / pts.length;
          const avgY = pts.reduce((s, p) => s + p.y, 0) / pts.length;
          const dx = avgX - panStateRef.current.lastX;
          const dy = avgY - panStateRef.current.lastY;
          canvasAreaRef.current.scrollLeft -= dx;
          canvasAreaRef.current.scrollTop -= dy;
          panStateRef.current = { lastX: avgX, lastY: avgY };
        }
        return;
      }
    }

    if (!drawingRef.current || !overlayEl) return;
    e.preventDefault();
    const frame = frames.find((f) => f.id === drawingRef.current.frameId);
    if (!frame) return;
    const p = getCanvasPoint(e, overlayEl, frame);
    const s = currentStrokeRef.current;
    const last = s.points[s.points.length - 1];
    s.points.push(p);

    const mainCanvas = frameRefs.current[drawingRef.current.frameId]?.getMainCanvas();
    if (mainCanvas) {
      const ctx = mainCanvas.getContext('2d');
      ctx.strokeStyle = `rgba(15, 15, 15, ${s.opacity})`;
      ctx.lineWidth = s.size;
      ctx.lineCap = 'round';
      ctx.lineJoin = 'round';
      ctx.beginPath();
      ctx.moveTo(last.x, last.y);
      ctx.lineTo(p.x, p.y);
      ctx.stroke();
    }
  };

  const handlePointerUp = (e, overlayEl) => {
    if (activeTool === 'lasso') {
      handleLassoPointerUp(e, overlayEl);
      return;
    }

    if (e.pointerType === 'touch') {
      activeTouchPointersRef.current.delete(e.pointerId);
      if (activeTouchPointersRef.current.size < 2) panStateRef.current = null;
      if (!drawingRef.current) return;
    }

    if (!drawingRef.current) return;
    const drawState = drawingRef.current;
    drawingRef.current = null;
    if (overlayEl) {
      try { overlayEl.releasePointerCapture(e.pointerId); } catch (_) {}
    }
    const liveStroke = currentStrokeRef.current;
    currentStrokeRef.current = null;
    if (!liveStroke) return;

    const frame = frames.find((f) => f.id === drawState.frameId);
    if (!frame) return;

    const oldTops = computeBlockTops(frame.blocks);
    const ownerId = findStrokeBlockId(liveStroke, frame.blocks, oldTops);
    if (ownerId == null) return;
    const ownerBlock = frame.blocks.find((b) => b.id === ownerId);
    if (!ownerBlock) return;
    const ownerTop = oldTops[ownerId];

    const localPoints = liveStroke.points.map((p) => ({ x: p.x, y: p.y - ownerTop }));
    const simplified = rdpSimplify(localPoints, RDP_EPSILON);
    const stored = {
      points: simplified,
      size: liveStroke.size,
      opacity: liveStroke.opacity,
      bbox: computeBbox(simplified),
      hidden: false,
    };

    const store = ensureFrameStore(drawState.frameId);
    if (!store.byBlock[ownerId]) store.byBlock[ownerId] = [];
    store.byBlock[ownerId].push(stored);
    store.history.push({ blockId: ownerId });

    const entry = ensureBlockBitmap(
      drawState.frameId,
      ownerBlock,
      frame.canvasWidth,
      stored.bbox.maxY,
    );
    renderStrokeToCtx(entry.ctx, stored, BITMAP_Y_PADDING);
  };

  // ---------- frame management ----------
  const addFrame = () => {
    const tmpl = selectedFrame || frames[frames.length - 1];
    const f = makeStarterFrame(`Frame ${frames.length + 1}`, {
      canvasWidth: tmpl?.canvasWidth ?? 690,
      sideMargin: tmpl?.sideMargin ?? 38,
    });
    ensureFrameStore(f.id);
    setFrames((arr) => [...arr, f]);
    setSelectedFrameId(f.id);
  };

  const countStrokesInFrame = (frameId) => {
    const store = strokesByFrameRef.current[frameId];
    if (!store) return 0;
    let n = 0;
    for (const k in store.byBlock) n += store.byBlock[k].length;
    return n;
  };

  const removeFrame = (id) => {
    if (frames.length <= 1) return;
    const lasso = lassoRef.current;
    if (lasso.frameId === id && lasso.phase !== 'idle') {
      cancelLassoSelection(id, frames.find(f => f.id === id));
    }
    const target = frames.find((f) => f.id === id);
    const strokeCount = countStrokesInFrame(id);
    const msg = strokeCount > 0
      ? `"${target?.name}" 을(를) 삭제합니다. 안에 그린 ${strokeCount}개의 stroke도 함께 사라집니다. 계속하시겠습니까?`
      : `"${target?.name}" 을(를) 삭제합니다. 계속하시겠습니까?`;
    if (!window.confirm(msg)) return;

    delete strokesByFrameRef.current[id];
    delete frameRefs.current[id];
    delete getBlockBitmapRef.current[id];
    setFrames((arr) => {
      const next = arr.filter((f) => f.id !== id);
      if (id === selectedFrameId) {
        const idx = arr.findIndex((f) => f.id === id);
        const newSel = next[Math.max(0, Math.min(idx, next.length - 1))];
        if (newSel) setSelectedFrameId(newSel.id);
      }
      return next;
    });
  };

  const renameFrame = (id, name) => {
    setFrames((arr) => arr.map((f) => (f.id === id ? { ...f, name } : f)));
  };

  const updateFrameDim = (id, key, value) => {
    if (key === 'canvasWidth') {
      const frame = frames.find((f) => f.id === id);
      if (frame && frame.canvasWidth !== value) {
        for (const b of frame.blocks) {
          rebuildBlockBitmap(id, b, value);
        }
      }
    }
    setFrames((arr) => arr.map((f) => (f.id === id ? { ...f, [key]: value } : f)));
  };

  // ---------- block actions (selected frame) ----------
  const addCut = (height) => {
    if (!selectedFrame) return;
    const sm = selectedFrame.sideMargin;
    setFrames((arr) => arr.map((f) =>
      f.id === selectedFrameId
        ? { ...f, blocks: [...f.blocks, { id: newId(), type: 'cut', height, marginLeft: sm, marginRight: sm }] }
        : f
    ));
  };

  const addGap = (height) => {
    if (!selectedFrame) return;
    setFrames((arr) => arr.map((f) =>
      f.id === selectedFrameId
        ? { ...f, blocks: [...f.blocks, { id: newId(), type: 'gap', height }] }
        : f
    ));
  };

  const removeBlock = (blockId) => {
    if (!selectedFrame) return;
    const store = ensureFrameStore(selectedFrameId);
    const removedStrokes = store.byBlock[blockId] || [];
    const oldTops = computeBlockTops(selectedFrame.blocks);
    const removedBlock = selectedFrame.blocks.find((b) => b.id === blockId);
    const removedTop = oldTops[blockId] ?? 0;

    const newBlocks = selectedFrame.blocks.filter((b) => b.id !== blockId);

    if (removedBlock && removedStrokes.length > 0 && newBlocks.length > 0) {
      const newTops = computeBlockTops(newBlocks);
      const dirty = new Set();
      for (const s of removedStrokes) {
        const frameCoordPoints = s.points.map((p) => ({ x: p.x, y: p.y + removedTop }));
        const probe = { ...s, points: frameCoordPoints };
        const newOwner = findStrokeBlockId(probe, newBlocks, newTops);
        if (newOwner == null) continue;
        const newOwnerTop = newTops[newOwner];
        const reLocal = frameCoordPoints.map((p) => ({ x: p.x, y: p.y - newOwnerTop }));
        const reStored = {
          points: reLocal,
          size: s.size,
          opacity: s.opacity,
          bbox: computeBbox(reLocal),
          hidden: false,
        };
        if (!store.byBlock[newOwner]) store.byBlock[newOwner] = [];
        store.byBlock[newOwner].push(reStored);
        dirty.add(newOwner);
      }
      for (const bid of dirty) {
        const blk = newBlocks.find((b) => b.id === bid);
        if (blk) rebuildBlockBitmap(selectedFrameId, blk, selectedFrame.canvasWidth);
      }
    }

    delete store.byBlock[blockId];
    delete store.bitmaps[blockId];
    store.history = store.history.filter((h) => h.blockId !== blockId);

    setFrames((arr) => arr.map((f) =>
      f.id === selectedFrameId ? { ...f, blocks: newBlocks } : f
    ));
  };

  const updateBlockHeight = (blockId, value) => {
    if (!selectedFrame) return;
    const h = Math.max(50, Math.min(5000, parseInt(value, 10) || 200));
    const target = selectedFrame.blocks.find((b) => b.id === blockId);
    if (!target || target.height === h) return;
    setFrames((arr) => arr.map((f) =>
      f.id === selectedFrameId
        ? { ...f, blocks: f.blocks.map((b) => (b.id === blockId ? { ...b, height: h } : b)) }
        : f
    ));
  };

  const updateBlockMargin = (blockId, side, value) => {
    if (!selectedFrame) return;
    const v = Math.max(0, Math.min(500, parseInt(value, 10)));
    if (!Number.isFinite(v)) return;
    setFrames((arr) => arr.map((f) =>
      f.id === selectedFrameId
        ? { ...f, blocks: f.blocks.map((b) => (b.id === blockId ? { ...b, [side]: v } : b)) }
        : f
    ));
  };


  // ---------- viewport-center block tracking ----------
  useEffect(() => {
    const area = canvasAreaRef.current;
    if (!area) return;

    const computeActive = () => {
      if (!selectedFrame) { setActiveBlockId(null); return; }
      const areaRect = area.getBoundingClientRect();
      const centerY = areaRect.top + areaRect.height / 2;
      const rangeHalf = 200;
      const rangeTop = centerY - rangeHalf;
      const rangeBottom = centerY + rangeHalf;

      const frameEl = area.querySelector(`[data-frame-id="${selectedFrameId}"]`);
      if (!frameEl) { setActiveBlockId(null); return; }
      const stageEl = frameEl.querySelector('.conti-frame-stage');
      if (!stageEl) { setActiveBlockId(null); return; }
      const stageRect = stageEl.getBoundingClientRect();

      let y = 0;
      let bestId = null;
      let bestOverlap = -1;
      for (const b of selectedFrame.blocks) {
        const blockTop = stageRect.top + y;
        const blockBottom = blockTop + b.height;
        const overlap = Math.max(0, Math.min(blockBottom, rangeBottom) - Math.max(blockTop, rangeTop));
        if (overlap > bestOverlap) {
          bestOverlap = overlap;
          bestId = b.id;
        }
        y += b.height;
      }
      setActiveBlockId(bestId);
    };

    area.addEventListener('scroll', computeActive, { passive: true });
    window.addEventListener('resize', computeActive);
    computeActive();
    return () => {
      area.removeEventListener('scroll', computeActive);
      window.removeEventListener('resize', computeActive);
    };
  }, [selectedFrameId, selectedFrame]);


  const findRowAt = (clientY) => {
    const list = blockListRef.current;
    if (!list) return { id: null, pos: null };
    const rows = list.querySelectorAll('[data-block-id]');
    for (const el of rows) {
      const r = el.getBoundingClientRect();
      if (clientY >= r.top && clientY <= r.bottom) {
        const id = parseInt(el.getAttribute('data-block-id'), 10);
        const pos = clientY < r.top + r.height / 2 ? 'above' : 'below';
        return { id, pos };
      }
    }
    if (rows.length > 0) {
      const first = rows[0].getBoundingClientRect();
      const last = rows[rows.length - 1].getBoundingClientRect();
      if (clientY < first.top) {
        return { id: parseInt(rows[0].getAttribute('data-block-id'), 10), pos: 'above' };
      }
      if (clientY > last.bottom) {
        return { id: parseInt(rows[rows.length - 1].getAttribute('data-block-id'), 10), pos: 'below' };
      }
    }
    return { id: null, pos: null };
  };

  const handleHandlePointerDown = (e, id) => {
    e.preventDefault();
    e.stopPropagation();
    try { e.currentTarget.setPointerCapture(e.pointerId); } catch (_) {}
    setDragId(id);
    setDragOverId(null);
    setDragOverPos(null);
  };

  const handleHandlePointerMove = (e) => {
    if (dragId === null) return;
    e.preventDefault();
    const { id, pos } = findRowAt(e.clientY);
    setDragOverId(id);
    setDragOverPos(pos);
  };

  const handleHandlePointerUp = (e) => {
    if (dragId === null || !selectedFrame) {
      setDragId(null); setDragOverId(null); setDragOverPos(null);
      return;
    }
    try { e.currentTarget.releasePointerCapture(e.pointerId); } catch (_) {}

    if (dragOverId !== null && dragOverId !== dragId) {
      const fromIdx = selectedFrame.blocks.findIndex((x) => x.id === dragId);
      const overIdx = selectedFrame.blocks.findIndex((x) => x.id === dragOverId);
      if (fromIdx >= 0 && overIdx >= 0) {
        const next = [...selectedFrame.blocks];
        const [removed] = next.splice(fromIdx, 1);
        let insertIdx = next.findIndex((x) => x.id === dragOverId);
        if (dragOverPos === 'below') insertIdx += 1;
        next.splice(insertIdx, 0, removed);

        const sameOrder = next.length === selectedFrame.blocks.length
          && next.every((b, i) => b.id === selectedFrame.blocks[i].id);
        if (!sameOrder) {
          setFrames((arr) => arr.map((f) =>
            f.id === selectedFrameId ? { ...f, blocks: next } : f
          ));
        }
      }
    }
    setDragId(null);
    setDragOverId(null);
    setDragOverPos(null);
  };

  // ---------- undo / clear ----------
  const undo = () => {
    if (!selectedFrame) return;
    // Don't undo while lasso selection is active
    if (lassoRef.current.phase !== 'idle') return;
    const store = ensureFrameStore(selectedFrameId);
    if (store.history.length === 0) return;
    const last = store.history.pop();
    const list = store.byBlock[last.blockId];
    if (list && list.length > 0) list.pop();
    const block = selectedFrame.blocks.find((b) => b.id === last.blockId);
    if (block) rebuildBlockBitmap(selectedFrameId, block, selectedFrame.canvasWidth);
    frameRefs.current[selectedFrameId]?.redraw();
  };

  const clearAll = () => {
    if (!selectedFrame) return;
    // Cancel any active lasso first
    if (lassoRef.current.phase !== 'idle' && lassoRef.current.frameId === selectedFrameId) {
      cancelLassoSelection(selectedFrameId, selectedFrame);
    }
    if (!window.confirm(`"${selectedFrame.name}"의 모든 드로잉을 지웁니다. 계속하시겠습니까?`)) return;
    const store = ensureFrameStore(selectedFrameId);
    store.byBlock = {};
    store.bitmaps = {};
    store.history = [];
    frameRefs.current[selectedFrameId]?.redraw();
  };

  // ---------- derived ----------
  const previewSize = Math.max(2, Math.min(34, penSize));
  const selectedTotalHeight = selectedFrame
    ? selectedFrame.blocks.reduce((s, b) => s + b.height, 0)
    : 0;
  const selectedCutCount = selectedFrame
    ? selectedFrame.blocks.filter((b) => b.type === 'cut').length
    : 0;

  const selectedBlockLayout = useMemo(() => {
    if (!selectedFrame) return [];
    let cutCounter = 0;
    let gapCounter = 0;
    return selectedFrame.blocks.map((b) => {
      const item = { ...b };
      if (b.type === 'cut') { cutCounter += 1; item.num = cutCounter; }
      else { gapCounter += 1; item.num = gapCounter; }
      return item;
    });
  }, [selectedFrame]);

  return (
    <div className="conti-root">
      <style>{STYLES}</style>

      <header className="conti-topbar">
        <div className="conti-brand">
          <div className="conti-brand-mark" />
          <div>
            <div className="conti-brand-name">콘티 프로그램</div>
            <div className="conti-brand-version">conti.v0.6</div>
          </div>
        </div>

        {/* Tool selector */}
        <div className="conti-tool">
          <button
            className={`conti-icon-btn ${activeTool === 'pen' ? 'active' : ''}`}
            onClick={() => switchTool('pen')}
            title="펜 (P)"
          >
            ✏ pen
          </button>
          <button
            className={`conti-icon-btn ${activeTool === 'lasso' ? 'active' : ''}`}
            onClick={() => switchTool('lasso')}
            title="올가미 (L)"
          >
            ⬡ lasso
          </button>
        </div>

        <div className="conti-tool-sep" />

        {/* Pen options (only when pen mode) */}
        {activeTool === 'pen' && (
          <>
            <div className="conti-tool">
              <span className="conti-tool-label">size</span>
              <input
                type="range" min="0" max="100" step="0.5"
                value={sizeToSlider(penSize)}
                onChange={(e) => setPenSize(Math.round(sliderToSize(parseFloat(e.target.value)) * 10) / 10)}
              />
              <input
                className="conti-num" type="number"
                min={PEN_MIN} max={PEN_MAX} step="0.1"
                value={penSize}
                onChange={(e) => {
                  const v = parseFloat(e.target.value);
                  if (Number.isFinite(v)) setPenSize(Math.max(PEN_MIN, Math.min(PEN_MAX, v)));
                }}
              />
              <span className="conti-tool-unit">px</span>
            </div>

            <div className="conti-tool">
              <span className="conti-tool-label">opacity</span>
              <input
                type="range" min="0" max="100" step="1"
                value={penOpacity}
                onChange={(e) => setPenOpacity(parseInt(e.target.value, 10))}
              />
              <input
                className="conti-num" type="number"
                min="0" max="100" step="1"
                value={penOpacity}
                onChange={(e) => {
                  const v = parseInt(e.target.value, 10);
                  if (Number.isFinite(v)) setPenOpacity(Math.max(0, Math.min(100, v)));
                }}
              />
              <span className="conti-tool-unit">%</span>
            </div>

            <div className="conti-pen-preview" title="현재 펜">
              <div
                className="conti-pen-dot"
                style={{
                  width: `${previewSize}px`,
                  height: `${previewSize}px`,
                  opacity: penOpacity / 100,
                }}
              />
            </div>
          </>
        )}

        {/* Lasso selection actions */}
        {activeTool === 'lasso' && hasSelection && (
          <div className="conti-sel-bar">
            <span className="conti-sel-label">선택됨</span>
            <button
              className="conti-icon-btn"
              onClick={copySelection}
              title="복사 (Ctrl+C)"
            >
              ⎘ copy
            </button>
            <button
              className="conti-icon-btn"
              onClick={pasteSelection}
              title="붙여넣기 (Ctrl+V)"
              disabled={!hasClipboard}
            >
              ⎗ paste
            </button>
            <div className="conti-tool-sep" />
            <button
              className="conti-icon-btn"
              onClick={() => flipSelection('h')}
              title="수평 뒤집기"
            >
              ↔ flip H
            </button>
            <button
              className="conti-icon-btn"
              onClick={() => flipSelection('v')}
              title="수직 뒤집기"
            >
              ↕ flip V
            </button>
            <div className="conti-tool-sep" />
            <button
              className="conti-icon-btn"
              onClick={() => rotateSelectionDeg(-90)}
              title="90° 반시계 회전"
            >
              ↺ 90°
            </button>
            <button
              className="conti-icon-btn"
              onClick={() => rotateSelectionDeg(90)}
              title="90° 시계 회전"
            >
              ↻ 90°
            </button>
            <div className="conti-tool-sep" />
            <button
              className="conti-icon-btn"
              onClick={() => {
                const lasso = lassoRef.current;
                if (lasso.frameId) {
                  const fr = frames.find(f => f.id === lasso.frameId);
                  applyLassoSelection(lasso.frameId, fr);
                }
              }}
              title="선택 적용 (Esc)"
            >
              ✓ apply
            </button>
            <button
              className="conti-icon-btn danger"
              onClick={deleteSelection}
              title="선택 삭제"
            >
              ✕ del
            </button>
          </div>
        )}

        {/* Paste when no selection but clipboard has content */}
        {activeTool === 'lasso' && !hasSelection && hasClipboard && (
          <button
            className="conti-icon-btn"
            onClick={pasteSelection}
            title="붙여넣기"
          >
            ⎗ paste
          </button>
        )}

        <div style={{ flex: 1 }} />

        <div className="conti-actions">
          <button
            className="conti-icon-btn"
            onClick={undo}
            disabled={!selectedFrame || lassoRef.current.phase !== 'idle'}
          >
            ↶ undo
          </button>
          <button
            className="conti-icon-btn danger"
            onClick={clearAll}
            disabled={!selectedFrame}
          >
            clear all
          </button>
        </div>
      </header>

      <div className="conti-main">
        {/* left sidebar */}
        <aside className="conti-sidebar">
          <div className="conti-section">
            <h3>frames <span className="count mono">{frames.length}</span></h3>
            {frames.map((f) => (
              <div
                key={f.id}
                className={`conti-frame-row ${f.id === selectedFrameId ? 'active' : ''}`}
                onClick={() => selectAndScrollToFrame(f.id)}
              >
                <input
                  value={f.name}
                  onChange={(e) => renameFrame(f.id, e.target.value)}
                  onClick={(e) => e.stopPropagation()}
                />
                <button
                  className="del"
                  onClick={(e) => { e.stopPropagation(); removeFrame(f.id); }}
                  disabled={frames.length <= 1}
                  title="삭제"
                >×</button>
              </div>
            ))}
            <button className="conti-add-btn" onClick={addFrame}>+ new frame</button>
          </div>

          {selectedFrame && (
            <div className="conti-section">
              <h3>가로 system</h3>
              <div className="conti-config-row">
                <label>canvas</label>
                <input
                  type="number" min="200" max="2000" step="2"
                  value={selectedFrame.canvasWidth}
                  onChange={(e) => {
                    const v = parseInt(e.target.value, 10);
                    if (Number.isFinite(v)) {
                      updateFrameDim(selectedFrameId, 'canvasWidth', Math.max(200, Math.min(2000, v)));
                    }
                  }}
                />
              </div>
              <div className="conti-config-row">
                <label>side margin</label>
                <input
                  type="number" min="0" max="500" step="2"
                  value={selectedFrame.sideMargin}
                  onChange={(e) => {
                    const v = parseInt(e.target.value, 10);
                    if (Number.isFinite(v)) {
                      updateFrameDim(selectedFrameId, 'sideMargin', Math.max(0, Math.min(500, v)));
                    }
                  }}
                />
              </div>
              <div className="conti-config-row">
                <label>cut width</label>
                <span className="conti-config-readonly">
                  {Math.max(50, selectedFrame.canvasWidth - 2 * selectedFrame.sideMargin)}px
                </span>
              </div>
            </div>
          )}

          <div className="conti-section">
            <h3>cut <span className="count mono">+ height</span></h3>
            <div className="conti-preset-grid">
              {DEFAULT_VERTICAL_SIZES.map((h) => (
                <button
                  key={h} className="conti-preset"
                  onClick={() => addCut(h)}
                  disabled={!selectedFrame}
                >
                  <span className="conti-preset-num">{h}</span>
                  <span className="conti-preset-sub">+ cut</span>
                </button>
              ))}
            </div>
          </div>

          <div className="conti-section">
            <h3>gap <span className="count mono">200 × n</span></h3>
            <div className="conti-preset-grid">
              {DEFAULT_GAP_SIZES.map((h) => (
                <button
                  key={h} className="conti-preset"
                  onClick={() => addGap(h)}
                  disabled={!selectedFrame}
                >
                  <span className="conti-preset-num">{h}</span>
                  <span className="conti-preset-sub">+ gap</span>
                </button>
              ))}
            </div>
          </div>

          {/* Lasso tips */}
          {activeTool === 'lasso' && (
            <div className="conti-section">
              <h3>lasso tips</h3>
              <div style={{
                fontSize: '11px',
                color: 'var(--muted)',
                fontFamily: 'Pretendard, sans-serif',
                lineHeight: 1.6,
              }}>
                <div style={{ marginBottom: 4 }}>
                  <strong style={{ color: 'var(--ink)' }}>그리기</strong> 영역을 자유롭게 드로잉
                </div>
                <div style={{ marginBottom: 4 }}>
                  <strong style={{ color: 'var(--ink)' }}>이동</strong> 선택 안쪽 드래그
                </div>
                <div style={{ marginBottom: 4 }}>
                  <strong style={{ color: 'var(--ink)' }}>크기</strong> □ 핸들 드래그
                </div>
                <div style={{ marginBottom: 4 }}>
                  <strong style={{ color: 'var(--ink)' }}>회전</strong> ● 핸들 드래그
                </div>
                <div style={{ marginBottom: 4 }}>
                  <strong style={{ color: 'var(--ink)' }}>적용</strong> 밖 클릭 or Apply
                </div>
                <div>
                  <strong style={{ color: 'var(--ink)' }}>취소</strong> Esc
                </div>
              </div>
            </div>
          )}
        </aside>

        {/* canvas area */}
        <div className="conti-canvas-area" ref={canvasAreaRef}>
          <div className="conti-canvas-inner">
            {frames.map((f) => (
              <FrameView
                key={f.id}
                ref={(el) => {
                  if (el) frameRefs.current[f.id] = el;
                  else delete frameRefs.current[f.id];
                }}
                frame={f}
                isSelected={f.id === selectedFrameId}
                showDimensions={f.id === selectedFrameId}
                activeTool={activeTool}
                selectionPhase={selectionPhase}
                getBlockBitmap={getBlockBitmapRef.current[f.id]}
                onSelect={setSelectedFrameId}
                onPointerDown={handlePointerDown}
                onPointerMove={handlePointerMove}
                onPointerUp={handlePointerUp}
              />
            ))}
          </div>

          {selectedFrame && (
            <div className="conti-status">
              <span className={`dot ${activeTool === 'lasso' ? 'lasso' : ''}`} />
              <span>{selectedFrame.name}</span>
              <span>·</span>
              <span>{activeTool === 'lasso' ? (hasSelection ? '🟥 selected' : 'lasso') : 'pen'}</span>
              <span>·</span>
              <span>w {selectedFrame.canvasWidth}px</span>
              <span>·</span>
              <span>h {selectedTotalHeight}px</span>
              <span>·</span>
              <span>cuts {selectedCutCount}</span>
            </div>
          )}
        </div>

        {/* right sidebar */}
        <aside className="conti-sidebar right">
          <div className="conti-section">
            <h3>
              blocks <span className="count mono">{selectedFrame?.blocks.length ?? 0}</span>
            </h3>
            {!selectedFrame || selectedFrame.blocks.length === 0 ? (
              <div className="conti-empty">
                {!selectedFrame
                  ? '선택된 frame이 없습니다'
                  : <>왼쪽 프리셋에서<br/>cut / gap을 추가하세요</>}
              </div>
            ) : (
              <div ref={blockListRef}>
                {selectedBlockLayout.map((b) => {
                  const showAbove = dragOverId === b.id && dragOverPos === 'above' && dragId !== b.id;
                  const showBelow = dragOverId === b.id && dragOverPos === 'below' && dragId !== b.id;
                  const isCut = b.type === 'cut';
                  return (
                    <div key={b.id} data-block-id={b.id}>
                      {showAbove && <div className="drop-indicator above" style={{ position:'relative', height:3, background:'var(--accent)', borderRadius:2, margin:'0 0 2px 0' }} />}
                      <div
                        className={`conti-block-row${isCut ? ' has-margin' : ''} ${dragId === b.id ? 'dragging' : ''} ${b.id === activeBlockId ? 'viewport-active' : ''}`}
                      >
                        <button
                          className="conti-drag-handle"
                          onPointerDown={(e) => handleHandlePointerDown(e, b.id)}
                          onPointerMove={handleHandlePointerMove}
                          onPointerUp={handleHandlePointerUp}
                          onPointerCancel={handleHandlePointerUp}
                          title="드래그해서 순서 변경"
                          aria-label="drag to reorder"
                        >
                          <svg width="10" height="16" viewBox="0 0 10 16" fill="currentColor" aria-hidden="true">
                            <circle cx="3" cy="3" r="1.2"/>
                            <circle cx="7" cy="3" r="1.2"/>
                            <circle cx="3" cy="8" r="1.2"/>
                            <circle cx="7" cy="8" r="1.2"/>
                            <circle cx="3" cy="13" r="1.2"/>
                            <circle cx="7" cy="13" r="1.2"/>
                          </svg>
                        </button>
                        <span className={`conti-block-tag ${b.type}`}>
                          {b.type === 'cut' ? `c${String(b.num).padStart(2, '0')}` : 'gap'}
                        </span>
                        <input
                          type="number" min="50" max="5000" step="50"
                          value={b.height}
                          onChange={(e) => updateBlockHeight(b.id, e.target.value)}
                        />
                        <span className="conti-tool-unit mono">px</span>
                        <button className="del" onClick={() => removeBlock(b.id)} title="삭제">×</button>
                      </div>
                      {isCut && (
                        <div className={`conti-block-margin-row${b.id === activeBlockId ? ' viewport-active' : ''}`}>
                          <span className="conti-margin-label">L</span>
                          <input
                            type="number" min="0" max="500" step="2"
                            value={b.marginLeft ?? selectedFrame.sideMargin}
                            onChange={(e) => updateBlockMargin(b.id, 'marginLeft', e.target.value)}
                            title="왼쪽 margin"
                          />
                          <div className="conti-margin-sep" />
                          <input
                            type="number" min="0" max="500" step="2"
                            value={b.marginRight ?? selectedFrame.sideMargin}
                            onChange={(e) => updateBlockMargin(b.id, 'marginRight', e.target.value)}
                            title="오른쪽 margin"
                          />
                          <span className="conti-margin-label">R</span>
                        </div>
                      )}
                      {showBelow && <div className="drop-indicator below" style={{ position:'relative', height:3, background:'var(--accent)', borderRadius:2, margin:'2px 0 0 0' }} />}
                    </div>
                  );
                })}
              </div>
            )}
          </div>
        </aside>
      </div>
    </div>
  );
}
