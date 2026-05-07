import React, {
  useState, useRef, useLayoutEffect, useMemo, useCallback,
  forwardRef, useImperativeHandle,
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

// Per-block bitmap cache: each block's offscreen canvas is taller than the
// block itself so strokes that extend slightly outside still fit. y=0 in the
// stroke's local coords lands at y=BITMAP_Y_PADDING in the bitmap canvas.
const BITMAP_Y_PADDING = 200;
const BITMAP_GROW_CHUNK = 400; // round up bitmap growth in chunks
const DPR_CAP = 2;
const RDP_EPSILON = 0.5; // px, point simplification tolerance

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

// Same association rule as before — cut + 200px halo wins over gap.
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

// Compute a stroke's axis-aligned bounding box (in whatever coords its
// points use — we store strokes in block-local coords).
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

// Iterative Ramer–Douglas–Peucker. Drops collinear points within `epsilon`,
// usually cutting raw pointer samples by 60–80% with no visible change.
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

// Apply stroke style + draw onto a 2D context. `yShift` is added to every
// point's y — used both for blitting block-local strokes onto a bitmap (which
// has BITMAP_Y_PADDING headroom) and for any one-off frame-coord renders.
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

// Per-block offscreen bitmap. Coordinates: a stroke's local y of 0 maps to
// canvas y = BITMAP_Y_PADDING. Width = frame.canvasWidth. Height grows on
// demand if a stroke extends beyond the current bitmap.
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

// Blit `src` bitmap onto `dst` (used to copy contents into a resized bitmap).
const blitBitmap = (srcEntry, dstCtx) => {
  // Both bitmaps are dpr-scaled; drawImage with the logical size handles it.
  dstCtx.drawImage(
    srcEntry.canvas,
    0, 0,
    srcEntry.logicalWidth, srcEntry.logicalHeight,
  );
};

const makeStarterFrame = (name, opts = {}) => ({
  id: newId(),
  name,
  canvasWidth: opts.canvasWidth ?? 690,
  sideMargin: opts.sideMargin ?? 38,
  blocks: opts.blocks ?? [
    { id: newId(), type: 'cut', height: 600 },
    { id: newId(), type: 'gap', height: 200 },
    { id: newId(), type: 'cut', height: 800 },
  ],
});

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
  gap: 24px;
}
.conti-brand { display: flex; align-items: center; gap: 10px; }
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

.conti-tools { display: flex; align-items: center; gap: 18px; flex: 1; }
.conti-tool { display: flex; align-items: center; gap: 8px; }
.conti-tool-label {
  font-family: 'JetBrains Mono', monospace;
  font-size: 10px; letter-spacing: 0.08em;
  color: var(--muted); text-transform: uppercase;
}
.conti-tool input[type="range"] {
  -webkit-appearance: none; appearance: none;
  width: 110px; height: 4px;
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
  width: 60px; padding: 4px 6px;
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

.conti-actions { display: flex; align-items: center; gap: 6px; }
.conti-icon-btn {
  display: flex; align-items: center; gap: 6px;
  padding: 6px 10px;
  font-family: 'JetBrains Mono', monospace;
  font-size: 11px; letter-spacing: 0.04em;
  color: var(--ink-2);
  background: transparent;
  border: 1px solid transparent;
  border-radius: 5px;
  transition: all 0.12s ease;
  text-transform: lowercase;
}
.conti-icon-btn:hover:not(:disabled) { background: var(--bg-panel); border-color: var(--line); }
.conti-icon-btn:active:not(:disabled) { transform: translateY(1px); }
.conti-icon-btn:disabled { opacity: 0.35; cursor: not-allowed; }
.conti-icon-btn.active { background: var(--ink); color: var(--paper); border-color: var(--ink); }
.conti-icon-btn.danger:hover:not(:disabled) { color: var(--accent); border-color: var(--accent); }

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
  cursor: crosshair;
}

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

/* status */
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

@media (max-width: 900px) {
  .conti-sidebar.right { display: none; }
}
@media (max-width: 700px) {
  .conti-sidebar { width: 200px; flex: 0 0 200px; }
  .conti-tool input[type="range"] { width: 80px; }
}
`;

// ---------- FrameView ----------
// Renders a single frame: label + stage (cut/gap blocks + canvas overlay) +
// optional dimension labels. Owns its own canvas element.
//
// Rendering model: strokes are not redrawn here. The parent maintains a
// per-block offscreen bitmap with the strokes already painted, and exposes
// it via `getBlockBitmap(blockId)`. FrameView's redraw just composites those
// bitmaps onto the visible canvas at each block's current top. This makes
// redraw cost O(blocks), not O(strokes) — so layout edits stay snappy even
// with 100k+ strokes.
const FrameView = forwardRef(function FrameView(
  {
    frame, isSelected, showDimensions, drawWithFinger,
    getBlockBitmap,
    onSelect,
    onPointerDown, onPointerMove, onPointerUp,
  },
  ref,
) {
  const canvasRef = useRef(null);
  const dprRef = useRef(1);

  const totalHeight = useMemo(
    () => frame.blocks.reduce((s, b) => s + b.height, 0),
    [frame.blocks],
  );
  const cutWidth = Math.max(50, frame.canvasWidth - 2 * frame.sideMargin);

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

    // Composite each block's pre-rendered bitmap at its current top. The
    // bitmap is taller than the block by 2*BITMAP_Y_PADDING (padding above
    // and below) so strokes can extend past block edges naturally.
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

  // Sync canvas size + redraw before paint, so stroke positions never lag
  // behind block layout changes.
  useLayoutEffect(() => {
    const c = canvasRef.current;
    if (!c) return;
    const dpr = Math.min(window.devicePixelRatio || 1, DPR_CAP);
    dprRef.current = dpr;
    c.width = Math.max(1, frame.canvasWidth * dpr);
    c.height = Math.max(1, totalHeight * dpr);
    c.style.width = `${frame.canvasWidth}px`;
    c.style.height = `${totalHeight}px`;
    const ctx = c.getContext('2d');
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.scale(dpr, dpr);
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    redraw();
  }, [frame.canvasWidth, totalHeight, redraw]);

  useImperativeHandle(ref, () => ({ redraw }), [redraw]);

  const handleDown = (e) => {
    if (e.pointerType === 'touch' && !drawWithFinger) return;
    onSelect(frame.id);
    onPointerDown(e, frame.id, canvasRef.current);
  };

  return (
    <div className={`conti-frame ${isSelected ? 'selected' : ''}`}>
      <div className="conti-frame-label" onClick={() => onSelect(frame.id)}>
        {frame.name}
      </div>
      <div
        className="conti-frame-stage"
        style={{ width: `${frame.canvasWidth}px`, height: `${totalHeight}px` }}
      >
        {blockLayout.map((b) => (
          <div
            key={`bg-${b.id}`}
            className={`conti-block ${b.type}`}
            style={{
              top: `${b.top}px`,
              left: b.type === 'cut' ? `${frame.sideMargin}px` : '0px',
              width: b.type === 'cut' ? `${cutWidth}px` : `${frame.canvasWidth}px`,
              height: `${b.height}px`,
            }}
          />
        ))}
        <canvas
          ref={canvasRef}
          className="conti-frame-canvas"
          style={{ touchAction: drawWithFinger ? 'none' : 'pan-y pan-x' }}
          onPointerDown={handleDown}
          onPointerMove={(e) => onPointerMove(e, canvasRef.current)}
          onPointerUp={(e) => onPointerUp(e, canvasRef.current)}
          onPointerCancel={(e) => onPointerUp(e, canvasRef.current)}
          onPointerLeave={(e) => onPointerUp(e, canvasRef.current)}
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

  // Per-frame drawing state. New schema (block-local + cached bitmaps):
  //   strokesByFrameRef.current[frameId] = {
  //     byBlock: { [blockId]: Stroke[] },   // points are block-local
  //     bitmaps: { [blockId]: BitmapEntry } // pre-rendered, lazy-allocated
  //     history: [{ blockId }]               // for undo, latest at end
  //   }
  // Storing strokes block-local lets resize/reorder be O(1) — only block
  // tops change, the bitmaps composite at new positions automatically.
  const strokesByFrameRef = useRef({});
  const ensureFrameStore = useCallback((fid) => {
    if (!strokesByFrameRef.current[fid]) {
      strokesByFrameRef.current[fid] = { byBlock: {}, bitmaps: {}, history: [] };
    }
    return strokesByFrameRef.current[fid];
  }, []);
  for (const f of frames) ensureFrameStore(f.id);

  // Pen state — global across frames.
  const [penSize, setPenSize] = useState(4);
  const [penOpacity, setPenOpacity] = useState(100);
  const [drawWithFinger, setDrawWithFinger] = useState(true);

  // Drawing in-progress state.
  const drawingRef = useRef(null); // { frameId } | null
  const currentStrokeRef = useRef(null);

  // Imperative handles to each FrameView so we can trigger redraws when
  // strokes change (since strokes live in a ref, not state).
  const frameRefs = useRef({});

  // ---------- block bitmap management ----------
  // Lazy-allocate / grow / clear / rebuild per-block offscreen bitmaps.
  // All bitmap canvases are dpr-scaled and use logical (CSS-px) drawing
  // coordinates; the y origin in those logical coords is shifted by
  // BITMAP_Y_PADDING so strokes that extend slightly above the block top
  // (negative local y) still fit.
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
      // Re-allocate at new size and copy old contents over.
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

  // Fully rebuild a block's bitmap from its stroke list (used after undo,
  // since strokes draw additively and we can't subtract one).
  const rebuildBlockBitmap = useCallback((frameId, block, frameWidth) => {
    const store = ensureFrameStore(frameId);
    const strokes = store.byBlock[block.id] || [];
    let maxY = 0;
    for (const s of strokes) {
      if (s.bbox && s.bbox.maxY > maxY) maxY = s.bbox.maxY;
    }
    const entry = ensureBlockBitmap(frameId, block, frameWidth, maxY);
    clearBlockBitmap(frameId, block.id);
    for (const s of strokes) renderStrokeToCtx(entry.ctx, s, BITMAP_Y_PADDING);
  }, [ensureFrameStore, ensureBlockBitmap, clearBlockBitmap]);

  // Stable getter for FrameView so React doesn't see a new function every
  // render. The closure reads from the ref, which is always current.
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

  // ---------- pointer / drawing ----------
  const getCanvasPoint = (e, canvasEl, frame) => {
    const rect = canvasEl.getBoundingClientRect();
    const totalHeight = frame.blocks.reduce((s, b) => s + b.height, 0);
    const sx = frame.canvasWidth / rect.width;
    const sy = totalHeight / rect.height;
    return {
      x: (e.clientX - rect.left) * sx,
      y: (e.clientY - rect.top) * sy,
    };
  };

  const handlePointerDown = (e, frameId, canvasEl) => {
    e.preventDefault();
    const frame = frames.find((f) => f.id === frameId);
    if (!frame || !canvasEl) return;
    try { canvasEl.setPointerCapture(e.pointerId); } catch (_) {}
    const p = getCanvasPoint(e, canvasEl, frame);
    drawingRef.current = { frameId };
    currentStrokeRef.current = {
      points: [p],
      size: penSize,
      opacity: penOpacity / 100,
    };
    const ctx = canvasEl.getContext('2d');
    ctx.fillStyle = `rgba(15, 15, 15, ${penOpacity / 100})`;
    ctx.beginPath();
    ctx.arc(p.x, p.y, penSize / 2, 0, Math.PI * 2);
    ctx.fill();
  };

  const handlePointerMove = (e, canvasEl) => {
    if (!drawingRef.current || !canvasEl) return;
    e.preventDefault();
    const frame = frames.find((f) => f.id === drawingRef.current.frameId);
    if (!frame) return;
    const p = getCanvasPoint(e, canvasEl, frame);
    const s = currentStrokeRef.current;
    const last = s.points[s.points.length - 1];
    s.points.push(p);
    const ctx = canvasEl.getContext('2d');
    ctx.strokeStyle = `rgba(15, 15, 15, ${s.opacity})`;
    ctx.lineWidth = s.size;
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    ctx.beginPath();
    ctx.moveTo(last.x, last.y);
    ctx.lineTo(p.x, p.y);
    ctx.stroke();
  };

  const handlePointerUp = (e, canvasEl) => {
    if (!drawingRef.current) return;
    const drawState = drawingRef.current;
    drawingRef.current = null;
    if (canvasEl) {
      try { canvasEl.releasePointerCapture(e.pointerId); } catch (_) {}
    }
    const liveStroke = currentStrokeRef.current;
    currentStrokeRef.current = null;
    if (!liveStroke) return;

    const frame = frames.find((f) => f.id === drawState.frameId);
    if (!frame) return;

    // Find owner block using the same association rule as before. Strokes
    // are stored block-local so resize/reorder doesn't have to touch them.
    const oldTops = computeBlockTops(frame.blocks);
    const ownerId = findStrokeBlockId(liveStroke, frame.blocks, oldTops);
    if (ownerId == null) return;
    const ownerBlock = frame.blocks.find((b) => b.id === ownerId);
    if (!ownerBlock) return;
    const ownerTop = oldTops[ownerId];

    // Convert points to block-local coords + simplify (RDP). Simplification
    // typically removes 60–80% of pointer samples without visible change,
    // dramatically reducing memory and undo-rebuild cost at scale.
    const localPoints = liveStroke.points.map((p) => ({ x: p.x, y: p.y - ownerTop }));
    const simplified = rdpSimplify(localPoints, RDP_EPSILON);
    const stored = {
      points: simplified,
      size: liveStroke.size,
      opacity: liveStroke.opacity,
      bbox: computeBbox(simplified),
    };

    const store = ensureFrameStore(drawState.frameId);
    if (!store.byBlock[ownerId]) store.byBlock[ownerId] = [];
    store.byBlock[ownerId].push(stored);
    store.history.push({ blockId: ownerId });

    // Append to the block's offscreen bitmap. The live stroke is already
    // visible on the main canvas (drawn incrementally during the drag), so
    // the user sees no change here — this just makes the next redraw cheap.
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
    // If canvasWidth changes, every block bitmap for that frame becomes the
    // wrong width. Rebuild them at the new width before committing the
    // state change so the next composite draws cleanly. (sideMargin is
    // visual-only — bitmaps are full canvas width.)
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
    setFrames((arr) => arr.map((f) =>
      f.id === selectedFrameId
        ? { ...f, blocks: [...f.blocks, { id: newId(), type: 'cut', height }] }
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

    // Reassign orphaned strokes to the closest remaining block, replicating
    // the old behavior (where strokes kept their absolute frame y after a
    // block was removed, and got re-associated by proximity on next layout
    // change). We do it eagerly here so bitmaps stay consistent.
    if (removedBlock && removedStrokes.length > 0 && newBlocks.length > 0) {
      const newTops = computeBlockTops(newBlocks);
      const dirty = new Set();
      for (const s of removedStrokes) {
        // Project stroke back into frame coords (using the just-removed
        // block's old top), then find which surviving block claims it.
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
        };
        if (!store.byBlock[newOwner]) store.byBlock[newOwner] = [];
        store.byBlock[newOwner].push(reStored);
        dirty.add(newOwner);
      }
      // Rebuild the bitmaps of any blocks that received strokes.
      for (const bid of dirty) {
        const blk = newBlocks.find((b) => b.id === bid);
        if (blk) rebuildBlockBitmap(selectedFrameId, blk, selectedFrame.canvasWidth);
      }
    }

    delete store.byBlock[blockId];
    delete store.bitmaps[blockId];
    // History entries for the removed block are now meaningless — drop them.
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

    // No stroke coordinates to rewrite — strokes are stored block-local, and
    // a height change just shifts subsequent block tops. The canvas will be
    // re-composited on the next render with bitmaps at their new positions.
    setFrames((arr) => arr.map((f) =>
      f.id === selectedFrameId
        ? { ...f, blocks: f.blocks.map((b) => (b.id === blockId ? { ...b, height: h } : b)) }
        : f
    ));
  };

  // ---------- block drag-reorder ----------
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
          // Reorder is essentially free — strokes are block-local, so we
          // just commit the new order and the next composite picks up the
          // bitmaps at their new tops.
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

  // ---------- undo / clear (selected frame only) ----------
  const undo = () => {
    if (!selectedFrame) return;
    const store = ensureFrameStore(selectedFrameId);
    if (store.history.length === 0) return;
    const last = store.history.pop();
    const list = store.byBlock[last.blockId];
    if (list && list.length > 0) list.pop();
    // Strokes are additive on the bitmap, so we have to rebuild from the
    // remaining strokes in just this one block (cost O(strokes-in-block)).
    const block = selectedFrame.blocks.find((b) => b.id === last.blockId);
    if (block) rebuildBlockBitmap(selectedFrameId, block, selectedFrame.canvasWidth);
    frameRefs.current[selectedFrameId]?.redraw();
  };

  const clearAll = () => {
    if (!selectedFrame) return;
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
            <div className="conti-brand-version">conti.v0.5</div>
          </div>
        </div>

        <div className="conti-tools">
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
        </div>

        <div className="conti-actions">
          <button
            className={`conti-icon-btn ${drawWithFinger ? 'active' : ''}`}
            onClick={() => setDrawWithFinger((v) => !v)}
            title="finger draw 켜면 손가락으로도 그려짐 / 끄면 손가락은 스크롤만"
          >
            {drawWithFinger ? '✓ ' : ''}finger draw
          </button>
          <button className="conti-icon-btn" onClick={undo} disabled={!selectedFrame}>↶ undo</button>
          <button className="conti-icon-btn danger" onClick={clearAll} disabled={!selectedFrame}>clear all</button>
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
                onClick={() => setSelectedFrameId(f.id)}
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
        </aside>

        {/* canvas area */}
        <div className="conti-canvas-area">
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
                drawWithFinger={drawWithFinger}
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
              <span className="dot" />
              <span>{selectedFrame.name}</span>
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
                  return (
                    <div
                      key={b.id}
                      data-block-id={b.id}
                      className={`conti-block-row ${dragId === b.id ? 'dragging' : ''}`}
                    >
                      {showAbove && <div className="drop-indicator above" />}
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
                      {showBelow && <div className="drop-indicator below" />}
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
