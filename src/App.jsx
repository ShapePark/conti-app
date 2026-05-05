import React, { useState, useRef, useEffect, useLayoutEffect, useMemo, useCallback } from 'react';

// ---------- constants ----------
let _id = 0;
const newId = () => ++_id;

const PEN_MIN = 0.1;
const PEN_MAX = 1000;
// Logarithmic mapping so the slider is usable across 4 orders of magnitude.
const sliderToSize = (s) => PEN_MIN * Math.pow(PEN_MAX / PEN_MIN, s / 100);
const sizeToSlider = (sz) => 100 * Math.log(sz / PEN_MIN) / Math.log(PEN_MAX / PEN_MIN);

const DEFAULT_VERTICAL_SIZES = [200, 300, 400, 600, 800, 1000, 1200];
const DEFAULT_GAP_SIZES = [200, 400, 600, 800, 1000];

// Halo (in px) above and below each cut, used to decide which cut a stroke
// "belongs to" when reordering blocks. Strokes drawn in this halo (i.e. in
// nearby gaps) follow the cut they're closest to.
const CUT_STROKE_HALO = 200;

// id -> top y position of each block, given an ordered block list
const computeBlockTops = (arr) => {
  const tops = {};
  let y = 0;
  for (const b of arr) {
    tops[b.id] = y;
    y += b.height;
  }
  return tops;
};

// Decide which block "owns" a stroke. Cuts (with halo) win over gaps; if
// multiple cut halos overlap, the stroke goes to the cut whose center is
// closest to the stroke's median y. Falls back to the gap that contains the
// median y. Returns null if nothing matches (shouldn't happen with normal use).
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
      if (dist < bestCutDist) {
        bestCutDist = dist;
        bestCutId = b.id;
      }
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

// ---------- styles ----------
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
.conti-root .mono { font-family: 'JetBrains Mono', ui-monospace, monospace; font-feature-settings: "ss01"; }
.conti-root button { font-family: inherit; cursor: pointer; border: none; background: none; color: inherit; }
.conti-root input { font-family: inherit; }

/* ---------- topbar ---------- */
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
  cursor: pointer;
  border: 2px solid var(--paper);
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
.conti-pen-dot {
  border-radius: 50%;
  background: var(--ink);
}

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
.conti-icon-btn:hover { background: var(--bg-panel); border-color: var(--line); }
.conti-icon-btn:active { transform: translateY(1px); }
.conti-icon-btn.active { background: var(--ink); color: var(--paper); border-color: var(--ink); }
.conti-icon-btn.danger:hover { color: var(--accent); border-color: var(--accent); }

/* ---------- main layout ---------- */
.conti-main { display: flex; flex: 1; min-height: 0; }

/* ---------- sidebar ---------- */
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

.conti-preset-grid {
  display: grid; grid-template-columns: 1fr 1fr; gap: 6px;
}
.conti-preset {
  padding: 10px 8px;
  background: var(--paper);
  border: 1px solid var(--line);
  border-radius: 5px;
  font-family: 'JetBrains Mono', monospace;
  font-size: 11px;
  color: var(--ink);
  text-align: left;
  transition: all 0.12s ease;
  display: flex; flex-direction: column; gap: 2px;
}
.conti-preset:hover { background: var(--ink); color: var(--paper); border-color: var(--ink); }
.conti-preset:hover .preset-sub { color: var(--paper); opacity: 0.6; }
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
  width: 70px;
  padding: 4px 6px;
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

/* ---------- canvas area ---------- */
.conti-canvas-area {
  flex: 1; min-width: 0;
  background:
    radial-gradient(circle at 1px 1px, var(--line) 1px, transparent 0) 0 0 / 24px 24px,
    var(--bg-canvas-area);
  overflow: auto;
  position: relative;
}
.conti-canvas-area::before {
  content: ''; position: sticky; top: 0; left: 0;
  display: block; height: 0;
}

.conti-stage {
  margin: 56px auto 200px auto;
  position: relative;
  background: var(--gap);
  box-shadow:
    0 1px 2px rgba(0,0,0,0.04),
    0 4px 12px rgba(0,0,0,0.06),
    0 16px 40px rgba(0,0,0,0.08);
}

.conti-block {
  position: absolute;
  pointer-events: none;
}
.conti-block.cut { background: var(--cut); }
.conti-block.gap { background: var(--gap); }

.conti-canvas {
  position: absolute; top: 0; left: 0;
  display: block;
  cursor: crosshair;
}

/* ---------- dimension labels (right side of canvas) ---------- */
.conti-dim {
  position: absolute;
  display: flex; align-items: center;
  pointer-events: none;
  white-space: nowrap;
}
.conti-dim-bracket {
  width: 12px; flex-shrink: 0;
  position: relative;
  height: 100%;
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
.conti-dim-size {
  font-weight: 600; color: var(--ink);
}
.conti-dim.gap .conti-dim-bracket::before,
.conti-dim.gap .conti-dim-bracket::after,
.conti-dim.gap .vline {
  background: var(--muted);
}
.conti-dim.gap .conti-dim-size { color: var(--muted); }

/* ---------- right sidebar block list ---------- */
.conti-block-row {
  position: relative;
  display: flex; align-items: center; gap: 6px;
  padding: 6px 8px;
  background: var(--paper);
  border: 1px solid var(--line);
  border-radius: 5px;
  margin-bottom: 4px;
  transition: border-color 0.12s ease, opacity 0.15s ease, transform 0.12s ease;
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

/* ---------- footer status ---------- */
.conti-status {
  position: absolute; bottom: 12px; left: 50%;
  transform: translateX(-50%);
  display: flex; gap: 16px;
  padding: 6px 12px;
  background: rgba(22, 20, 15, 0.85);
  color: var(--paper);
  font-family: 'JetBrains Mono', monospace;
  font-size: 10px; letter-spacing: 0.06em;
  border-radius: 999px;
  backdrop-filter: blur(8px);
  -webkit-backdrop-filter: blur(8px);
  pointer-events: none;
}
.conti-status .dot { width: 6px; height: 6px; background: #6fc275; border-radius: 50%; align-self: center; }

/* iPad / narrow */
@media (max-width: 900px) {
  .conti-sidebar.right { display: none; }
}
@media (max-width: 700px) {
  .conti-sidebar { width: 200px; flex: 0 0 200px; }
  .conti-tool input[type="range"] { width: 80px; }
}
`;

// ---------- main component ----------
export default function ContiProgram() {
  // canvas system
  const [canvasWidth, setCanvasWidth] = useState(690);
  const [sideMargin, setSideMargin] = useState(38);
  const [verticalSizes] = useState(DEFAULT_VERTICAL_SIZES);
  const [gapSizes] = useState(DEFAULT_GAP_SIZES);

  // blocks
  const [blocks, setBlocks] = useState(() => [
    { id: newId(), type: 'cut', height: 600 },
    { id: newId(), type: 'gap', height: 200 },
    { id: newId(), type: 'cut', height: 400 },
    { id: newId(), type: 'gap', height: 400 },
    { id: newId(), type: 'cut', height: 800 },
    { id: newId(), type: 'gap', height: 200 },
    { id: newId(), type: 'cut', height: 1000 },
  ]);

  // pen
  const [penSize, setPenSize] = useState(4);
  const [penOpacity, setPenOpacity] = useState(100);
  const [drawWithFinger, setDrawWithFinger] = useState(true);

  // refs
  const canvasRef = useRef(null);
  const containerRef = useRef(null);
  const strokesRef = useRef([]);
  const currentStrokeRef = useRef(null);
  const isDrawingRef = useRef(false);
  const dprRef = useRef(1);

  // derived
  const cutWidth = Math.max(50, canvasWidth - 2 * sideMargin);
  const totalHeight = blocks.reduce((s, b) => s + b.height, 0);

  const blockLayout = useMemo(() => {
    let y = 0;
    let cutCounter = 0;
    let gapCounter = 0;
    return blocks.map((b) => {
      const item = { ...b, top: y };
      if (b.type === 'cut') { cutCounter += 1; item.num = cutCounter; }
      else { gapCounter += 1; item.num = gapCounter; }
      y += b.height;
      return item;
    });
  }, [blocks]);

  // ---------- drawing ----------
  const drawStroke = useCallback((ctx, stroke) => {
    if (!stroke.points || stroke.points.length === 0) return;
    ctx.strokeStyle = `rgba(15, 15, 15, ${stroke.opacity})`;
    ctx.fillStyle = `rgba(15, 15, 15, ${stroke.opacity})`;
    ctx.lineWidth = stroke.size;
    if (stroke.points.length === 1) {
      ctx.beginPath();
      ctx.arc(stroke.points[0].x, stroke.points[0].y, stroke.size / 2, 0, Math.PI * 2);
      ctx.fill();
      return;
    }
    ctx.beginPath();
    ctx.moveTo(stroke.points[0].x, stroke.points[0].y);
    for (let i = 1; i < stroke.points.length; i++) {
      ctx.lineTo(stroke.points[i].x, stroke.points[i].y);
    }
    ctx.stroke();
  }, []);

  const redrawAll = useCallback(() => {
    const c = canvasRef.current;
    if (!c) return;
    const ctx = c.getContext('2d');
    const dpr = dprRef.current;
    ctx.clearRect(0, 0, c.width / dpr, c.height / dpr);
    for (const stroke of strokesRef.current) {
      drawStroke(ctx, stroke);
    }
  }, [drawStroke]);

  // setup canvas dimensions on size change.
  // useLayoutEffect (not useEffect) so the canvas is resized + redrawn in
  // the same paint cycle as the block layout — otherwise strokes appear to
  // jump from old to new positions for one frame on height changes.
  useLayoutEffect(() => {
    const c = canvasRef.current;
    if (!c) return;
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    dprRef.current = dpr;
    c.width = Math.max(1, canvasWidth * dpr);
    c.height = Math.max(1, totalHeight * dpr);
    c.style.width = `${canvasWidth}px`;
    c.style.height = `${totalHeight}px`;
    const ctx = c.getContext('2d');
    ctx.setTransform(1, 0, 0, 1, 0, 0); // reset
    ctx.scale(dpr, dpr);
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    redrawAll();
  }, [canvasWidth, totalHeight, redrawAll]);

  const getCanvasPoint = (e) => {
    const rect = canvasRef.current.getBoundingClientRect();
    const sx = canvasWidth / rect.width;
    const sy = totalHeight / rect.height;
    return { x: (e.clientX - rect.left) * sx, y: (e.clientY - rect.top) * sy };
  };

  const handlePointerDown = (e) => {
    if (e.pointerType === 'touch' && !drawWithFinger) return;
    e.preventDefault();
    try { canvasRef.current.setPointerCapture(e.pointerId); } catch (_) {}
    const p = getCanvasPoint(e);
    isDrawingRef.current = true;
    currentStrokeRef.current = {
      points: [p],
      size: penSize,
      opacity: penOpacity / 100,
    };
    const ctx = canvasRef.current.getContext('2d');
    drawStroke(ctx, currentStrokeRef.current);
  };

  const handlePointerMove = (e) => {
    if (!isDrawingRef.current) return;
    e.preventDefault();
    const p = getCanvasPoint(e);
    const s = currentStrokeRef.current;
    const last = s.points[s.points.length - 1];
    s.points.push(p);
    const ctx = canvasRef.current.getContext('2d');
    ctx.strokeStyle = `rgba(15, 15, 15, ${s.opacity})`;
    ctx.lineWidth = s.size;
    ctx.beginPath();
    ctx.moveTo(last.x, last.y);
    ctx.lineTo(p.x, p.y);
    ctx.stroke();
  };

  const handlePointerUp = (e) => {
    if (!isDrawingRef.current) return;
    isDrawingRef.current = false;
    try { canvasRef.current.releasePointerCapture(e.pointerId); } catch (_) {}
    if (currentStrokeRef.current) {
      strokesRef.current.push(currentStrokeRef.current);
      currentStrokeRef.current = null;
    }
  };

  // ---------- block actions ----------
  const addCut = (height) => setBlocks((b) => [...b, { id: newId(), type: 'cut', height }]);
  const addGap = (height) => setBlocks((b) => [...b, { id: newId(), type: 'gap', height }]);
  const removeBlock = (id) => setBlocks((b) => b.filter((x) => x.id !== id));
  const updateBlockHeight = (id, value) => {
    const h = Math.max(50, Math.min(5000, parseInt(value, 10) || 200));
    const target = blocks.find((x) => x.id === id);
    if (!target || target.height === h) return;

    // Same association rule as drag-reorder: every stroke is owned by some
    // block (cut + 200px halo first, gap fallback). When this block's height
    // change shifts the top of any subsequent block, that block's strokes
    // shift by the same delta.
    const oldTops = computeBlockTops(blocks);
    const next = blocks.map((x) => (x.id === id ? { ...x, height: h } : x));
    const newTops = computeBlockTops(next);

    for (const stroke of strokesRef.current) {
      const blockId = findStrokeBlockId(stroke, blocks, oldTops);
      if (blockId === null) continue;
      const delta = (newTops[blockId] ?? 0) - (oldTops[blockId] ?? 0);
      if (delta === 0) continue;
      for (const p of stroke.points) p.y += delta;
    }

    setBlocks(next);
    // useLayoutEffect on totalHeight will resize the canvas and redraw,
    // synchronously before the next paint, so no flicker.
  };
  const moveBlock = (id, dir) => {
    setBlocks((b) => {
      const i = b.findIndex((x) => x.id === id);
      if (i < 0) return b;
      const j = i + dir;
      if (j < 0 || j >= b.length) return b;
      const next = [...b];
      [next[i], next[j]] = [next[j], next[i]];
      return next;
    });
  };

  // ---------- drag-and-drop reordering ----------
  const [dragId, setDragId] = useState(null);
  const [dragOverId, setDragOverId] = useState(null);
  const [dragOverPos, setDragOverPos] = useState(null); // 'above' | 'below'
  const blockListRef = useRef(null);

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
    // outside any row — clamp to first / last
    const first = rows[0]?.getBoundingClientRect();
    const last = rows[rows.length - 1]?.getBoundingClientRect();
    if (first && clientY < first.top) {
      return { id: parseInt(rows[0].getAttribute('data-block-id'), 10), pos: 'above' };
    }
    if (last && clientY > last.bottom) {
      return { id: parseInt(rows[rows.length - 1].getAttribute('data-block-id'), 10), pos: 'below' };
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
    if (dragId === null) return;
    try { e.currentTarget.releasePointerCapture(e.pointerId); } catch (_) {}
    if (dragOverId !== null && dragOverId !== dragId) {
      const fromIdx = blocks.findIndex((x) => x.id === dragId);
      const overIdx = blocks.findIndex((x) => x.id === dragOverId);
      if (fromIdx >= 0 && overIdx >= 0) {
        // Build the new order
        const next = [...blocks];
        const [removed] = next.splice(fromIdx, 1);
        let insertIdx = next.findIndex((x) => x.id === dragOverId);
        if (dragOverPos === 'below') insertIdx += 1;
        next.splice(insertIdx, 0, removed);

        // Detect actual change (drop-just-above-next or drop-just-below-prev are no-ops)
        const sameOrder = next.length === blocks.length && next.every((b, i) => b.id === blocks[i].id);
        if (!sameOrder) {
          // Compute each block's top y in old vs new layout, then shift every
          // stroke by the delta of the block it "belongs to".
          const oldTops = computeBlockTops(blocks);
          const newTops = computeBlockTops(next);
          for (const stroke of strokesRef.current) {
            const blockId = findStrokeBlockId(stroke, blocks, oldTops);
            if (blockId === null) continue;
            const delta = (newTops[blockId] ?? 0) - (oldTops[blockId] ?? 0);
            if (delta === 0) continue;
            for (const p of stroke.points) p.y += delta;
          }
          redrawAll();
          setBlocks(next);
        }
      }
    }
    setDragId(null);
    setDragOverId(null);
    setDragOverPos(null);
  };

  const undo = () => {
    if (strokesRef.current.length === 0) return;
    strokesRef.current.pop();
    redrawAll();
  };

  const clearAll = () => {
    if (!window.confirm('모든 드로잉을 지웁니다. 계속하시겠습니까?')) return;
    strokesRef.current = [];
    redrawAll();
  };

  // ---------- render ----------
  // pen preview circle clamped to fit container
  const previewSize = Math.max(2, Math.min(34, penSize));

  return (
    <div className="conti-root">
      <style>{STYLES}</style>

      {/* TOP BAR */}
      <header className="conti-topbar">
        <div className="conti-brand">
          <div className="conti-brand-mark" />
          <div>
            <div className="conti-brand-name">콘티 프로그램</div>
            <div className="conti-brand-version">conti.v0.1</div>
          </div>
        </div>

        <div className="conti-tools">
          {/* SIZE */}
          <div className="conti-tool">
            <span className="conti-tool-label">size</span>
            <input
              type="range"
              min="0" max="100" step="0.5"
              value={sizeToSlider(penSize)}
              onChange={(e) => setPenSize(Math.round(sliderToSize(parseFloat(e.target.value)) * 10) / 10)}
            />
            <input
              className="conti-num"
              type="number"
              min={PEN_MIN}
              max={PEN_MAX}
              step="0.1"
              value={penSize}
              onChange={(e) => {
                const v = parseFloat(e.target.value);
                if (Number.isFinite(v)) setPenSize(Math.max(PEN_MIN, Math.min(PEN_MAX, v)));
              }}
            />
            <span className="conti-tool-unit">px</span>
          </div>

          {/* OPACITY */}
          <div className="conti-tool">
            <span className="conti-tool-label">opacity</span>
            <input
              type="range"
              min="0" max="100" step="1"
              value={penOpacity}
              onChange={(e) => setPenOpacity(parseInt(e.target.value, 10))}
            />
            <input
              className="conti-num"
              type="number"
              min="0" max="100" step="1"
              value={penOpacity}
              onChange={(e) => {
                const v = parseInt(e.target.value, 10);
                if (Number.isFinite(v)) setPenOpacity(Math.max(0, Math.min(100, v)));
              }}
            />
            <span className="conti-tool-unit">%</span>
          </div>

          {/* PEN PREVIEW */}
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
            title="finger draw 켜면 손가락으로도 그려짐 / 끄면 손가락은 스크롤만, 애플펜슬·마우스로만 그림"
          >
            {drawWithFinger ? '✓ ' : ''}finger draw
          </button>
          <button className="conti-icon-btn" onClick={undo}>↶ undo</button>
          <button className="conti-icon-btn danger" onClick={clearAll}>clear all</button>
        </div>
      </header>

      <div className="conti-main">
        {/* LEFT SIDEBAR */}
        <aside className="conti-sidebar">
          <div className="conti-section">
            <h3>가로 system</h3>
            <div className="conti-config-row">
              <label>canvas</label>
              <input
                type="number" min="200" max="2000" step="2"
                value={canvasWidth}
                onChange={(e) => {
                  const v = parseInt(e.target.value, 10);
                  if (Number.isFinite(v)) setCanvasWidth(Math.max(200, Math.min(2000, v)));
                }}
              />
            </div>
            <div className="conti-config-row">
              <label>side margin</label>
              <input
                type="number" min="0" max="500" step="2"
                value={sideMargin}
                onChange={(e) => {
                  const v = parseInt(e.target.value, 10);
                  if (Number.isFinite(v)) setSideMargin(Math.max(0, Math.min(500, v)));
                }}
              />
            </div>
            <div className="conti-config-row">
              <label>cut width</label>
              <span className="conti-config-readonly">{cutWidth}px</span>
            </div>
          </div>

          <div className="conti-section">
            <h3>cut <span className="count mono">+ height</span></h3>
            <div className="conti-preset-grid">
              {verticalSizes.map((h) => (
                <button key={h} className="conti-preset" onClick={() => addCut(h)}>
                  <span className="conti-preset-num">{h}</span>
                  <span className="conti-preset-sub">+ cut</span>
                </button>
              ))}
            </div>
          </div>

          <div className="conti-section">
            <h3>gap <span className="count mono">200 × n</span></h3>
            <div className="conti-preset-grid">
              {gapSizes.map((h) => (
                <button key={h} className="conti-preset" onClick={() => addGap(h)}>
                  <span className="conti-preset-num">{h}</span>
                  <span className="conti-preset-sub">+ gap</span>
                </button>
              ))}
            </div>
          </div>
        </aside>

        {/* CANVAS AREA */}
        <div className="conti-canvas-area" ref={containerRef}>
          <div
            className="conti-stage"
            style={{ width: `${canvasWidth}px`, height: `${totalHeight}px` }}
          >
            {/* background blocks (cut = filled, gap = blank) */}
            {blockLayout.map((b) => (
              <div
                key={`bg-${b.id}`}
                className={`conti-block ${b.type}`}
                style={{
                  top: `${b.top}px`,
                  left: b.type === 'cut' ? `${sideMargin}px` : '0px',
                  width: b.type === 'cut' ? `${cutWidth}px` : `${canvasWidth}px`,
                  height: `${b.height}px`,
                }}
              />
            ))}

            {/* drawing canvas overlay */}
            <canvas
              ref={canvasRef}
              className="conti-canvas"
              style={{ touchAction: drawWithFinger ? 'none' : 'pan-y' }}
              onPointerDown={handlePointerDown}
              onPointerMove={handlePointerMove}
              onPointerUp={handlePointerUp}
              onPointerCancel={handlePointerUp}
              onPointerLeave={handlePointerUp}
            />

            {/* dimension labels on the right */}
            {blockLayout.map((b) => (
              <div
                key={`dim-${b.id}`}
                className={`conti-dim ${b.type}`}
                style={{
                  top: `${b.top}px`,
                  height: `${b.height}px`,
                  left: `${canvasWidth + 10}px`,
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

          {/* status */}
          <div className="conti-status">
            <span className="dot" />
            <span>w {canvasWidth}px</span>
            <span>·</span>
            <span>h {totalHeight}px</span>
            <span>·</span>
            <span>cuts {blockLayout.filter((b) => b.type === 'cut').length}</span>
            <span>·</span>
            <span>strokes {strokesRef.current.length}</span>
          </div>
        </div>

        {/* RIGHT SIDEBAR — block list */}
        <aside className="conti-sidebar right">
          <div className="conti-section">
            <h3>blocks <span className="count mono">{blocks.length}</span></h3>
            {blocks.length === 0 && (
              <div className="conti-empty">왼쪽 프리셋에서<br/>cut / gap을 추가하세요</div>
            )}
            <div ref={blockListRef}>
              {blockLayout.map((b) => {
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
                      type="number"
                      min="50" max="5000" step="50"
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
          </div>
        </aside>
      </div>
    </div>
  );
}
