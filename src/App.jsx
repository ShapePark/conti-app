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

// ---------- bubble constants ----------
const BUBBLE_TYPES = ['normal', 'thought', 'whisper', 'shout'];
const BUBBLE_TYPE_LABELS = { normal: '일반', thought: '속마음', whisper: '속삭임', shout: 'Shout' };
const BUBBLE_MIN_W = 60;
const BUBBLE_MIN_H = 40;
const TAIL_HANDLE_R = 8;

// ---------- typography presets ----------
const DEFAULT_TYPO_PRESETS = [
  { id: 1, name: 'Shout A',  size: 84, weight: 900 },
  { id: 2, name: 'Shout B',  size: 72, weight: 900 },
  { id: 3, name: 'Body A',   size: 52, weight: 700 },
  { id: 4, name: 'Body B',   size: 40, weight: 500 },
  { id: 5, name: 'Mumble A', size: 24, weight: 400 },
  { id: 6, name: 'Mumble B', size: 16, weight: 400 },
];

// ---------- helpers ----------
const computeBlockTops = (arr) => {
  const tops = {};
  let y = 0;
  for (const b of arr) { tops[b.id] = y; y += b.height; }
  return tops;
};

const findStrokeBlockId = (stroke, arr, tops) => {
  if (!stroke.points || stroke.points.length === 0) return null;
  const sortedY = stroke.points.map((p) => p.y).sort((a, b) => a - b);
  const medianY = sortedY[Math.floor(sortedY.length / 2)];
  let bestCutId = null, bestCutDist = Infinity;
  for (const b of arr) {
    if (b.type !== 'cut') continue;
    const top = tops[b.id], bottom = top + b.height;
    if (medianY >= top - CUT_STROKE_HALO && medianY <= bottom + CUT_STROKE_HALO) {
      const dist = Math.abs(medianY - (top + bottom) / 2);
      if (dist < bestCutDist) { bestCutDist = dist; bestCutId = b.id; }
    }
  }
  if (bestCutId !== null) return bestCutId;
  for (const b of arr) {
    if (b.type !== 'gap') continue;
    const top = tops[b.id], bottom = top + b.height;
    if (medianY >= top && medianY <= bottom) return b.id;
  }
  return null;
};

const findBubbleBlockId = (bubble, arr, tops) => {
  const centerY = bubble.y + bubble.h / 2;
  let bestCutId = null, bestCutDist = Infinity;
  for (const b of arr) {
    if (b.type !== 'cut') continue;
    const top = tops[b.id], bottom = top + b.height;
    if (centerY >= top - CUT_STROKE_HALO && centerY <= bottom + CUT_STROKE_HALO) {
      const dist = Math.abs(centerY - (top + bottom) / 2);
      if (dist < bestCutDist) { bestCutDist = dist; bestCutId = b.id; }
    }
  }
  if (bestCutId !== null) return bestCutId;
  for (const b of arr) {
    if (b.type !== 'gap') continue;
    const top = tops[b.id], bottom = top + b.height;
    if (centerY >= top && centerY <= bottom) return b.id;
  }
  return null;
};

const computeBbox = (points) => {
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  for (const p of points) {
    if (p.x < minX) minX = p.x; if (p.y < minY) minY = p.y;
    if (p.x > maxX) maxX = p.x; if (p.y > maxY) maxY = p.y;
  }
  return { minX, minY, maxX, maxY };
};

const rdpSimplify = (points, epsilon) => {
  if (points.length <= 2) return points;
  const keep = new Uint8Array(points.length);
  keep[0] = 1; keep[points.length - 1] = 1;
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
      if (segLenSq === 0) { d2 = px * px + py * py; }
      else {
        const t = (px * dx + py * dy) / segLenSq;
        const ex = px - t * dx, ey = py - t * dy;
        d2 = ex * ex + ey * ey;
      }
      if (d2 > bestD2) { bestD2 = d2; bestI = i; }
    }
    if (bestI !== -1 && bestD2 > epsilon * epsilon) {
      keep[bestI] = 1;
      stack.push([lo, bestI]); stack.push([bestI, hi]);
    }
  }
  const out = [];
  for (let i = 0; i < points.length; i++) if (keep[i]) out.push(points[i]);
  return out;
};

// ---------- pen color constants ----------
const PEN_COLORS = [
  { id: 'black', hex: '#0F0F0F', label: '기본' },
  { id: 'red',   hex: '#FA3E3E', label: '빨강' },
  { id: 'blue',  hex: '#5769F2', label: '파랑' },
];

const hexToRgba = (hex, opacity) => {
  const h = hex.replace('#', '');
  const r = parseInt(h.slice(0, 2), 16);
  const g = parseInt(h.slice(2, 4), 16);
  const b = parseInt(h.slice(4, 6), 16);
  return `rgba(${r},${g},${b},${opacity})`;
};

const renderStrokeToCtx = (ctx, stroke, yShift = 0) => {
  if (!stroke.points || stroke.points.length === 0) return;
  const colorHex = stroke.color || '#0F0F0F';
  ctx.strokeStyle = hexToRgba(colorHex, stroke.opacity);
  ctx.fillStyle   = hexToRgba(colorHex, stroke.opacity);
  ctx.lineWidth = stroke.size;
  if (stroke.points.length === 1) {
    ctx.beginPath();
    ctx.arc(stroke.points[0].x, stroke.points[0].y + yShift, stroke.size / 2, 0, Math.PI * 2);
    ctx.fill(); return;
  }
  ctx.beginPath();
  ctx.moveTo(stroke.points[0].x, stroke.points[0].y + yShift);
  for (let i = 1; i < stroke.points.length; i++)
    ctx.lineTo(stroke.points[i].x, stroke.points[i].y + yShift);
  ctx.stroke();
};

const createBlockBitmap = (logicalWidth, logicalHeight, dpr) => {
  const canvas = document.createElement('canvas');
  canvas.width = Math.max(1, Math.ceil(logicalWidth * dpr));
  canvas.height = Math.max(1, Math.ceil(logicalHeight * dpr));
  const ctx = canvas.getContext('2d');
  ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.scale(dpr, dpr);
  ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  return { canvas, ctx, logicalWidth, logicalHeight, dpr };
};

const blitBitmap = (srcEntry, dstCtx) =>
  dstCtx.drawImage(srcEntry.canvas, 0, 0, srcEntry.logicalWidth, srcEntry.logicalHeight);

// ---------- lasso helpers ----------
const pointInPolygon = (px, py, polygon) => {
  if (polygon.length < 3) return false;
  let inside = false;
  for (let i = 0, j = polygon.length - 1; i < polygon.length; j = i++) {
    const xi = polygon[i].x, yi = polygon[i].y, xj = polygon[j].x, yj = polygon[j].y;
    if (((yi > py) !== (yj > py)) && (px < (xj - xi) * (py - yi) / (yj - yi) + xi))
      inside = !inside;
  }
  return inside;
};

const applySelectionTransform = (x, y, cx, cy, tr) => {
  let lx = x - cx, ly = y - cy;
  if (tr.flipH) lx = -lx; if (tr.flipV) ly = -ly;
  lx *= tr.scaleX; ly *= tr.scaleY;
  const cos = Math.cos(tr.angle), sin = Math.sin(tr.angle);
  return { x: lx * cos - ly * sin + cx + tr.tx, y: lx * sin + ly * cos + cy + tr.ty };
};

const getHandlePositions = (bbox, tr) => {
  const { minX, minY, maxX, maxY, cx, cy } = bbox;
  const t = (x, y) => applySelectionTransform(x, y, cx, cy, tr);
  const tl = t(minX, minY), tr2 = t(maxX, minY), br = t(maxX, maxY), bl = t(minX, maxY);
  const tc = { x: (tl.x + tr2.x) / 2, y: (tl.y + tr2.y) / 2 };
  const bc = { x: (bl.x + br.x) / 2, y: (bl.y + br.y) / 2 };
  const lc = { x: (tl.x + bl.x) / 2, y: (tl.y + bl.y) / 2 };
  const rc = { x: (tr2.x + br.x) / 2, y: (tr2.y + br.y) / 2 };
  const outX = tc.x - bc.x, outY = tc.y - bc.y;
  const outLen = Math.sqrt(outX * outX + outY * outY) || 1;
  return { tl, tr: tr2, br, bl, tc, bc, lc, rc,
    rotate: { x: tc.x + (outX / outLen) * ROTATE_HANDLE_DIST, y: tc.y + (outY / outLen) * ROTATE_HANDLE_DIST } };
};

const hitTestHandles = (px, py, handles) => {
  const r2 = HANDLE_HIT_RADIUS * HANDLE_HIT_RADIUS;
  const rot = handles.rotate;
  if ((px - rot.x) ** 2 + (py - rot.y) ** 2 <= r2) return 'rotate';
  for (const name of ['tl', 'tr', 'br', 'bl', 'tc', 'bc', 'lc', 'rc']) {
    const h = handles[name];
    if ((px - h.x) ** 2 + (py - h.y) ** 2 <= r2) return name;
  }
  return null;
};

// ---------- bubble SVG helpers ----------
const getRoundedRectPath = (x, y, w, h, r = 108) => {
  const R = Math.min(r, w / 2, h / 2);
  return `M${x+R},${y} H${x+w-R} Q${x+w},${y} ${x+w},${y+R} V${y+h-R} Q${x+w},${y+h} ${x+w-R},${y+h} H${x+R} Q${x},${y+h} ${x},${y+h-R} V${y+R} Q${x},${y} ${x+R},${y} Z`;
};

const getThoughtBubblePath = (cx, cy, rx, ry) => {
  const n = 52;
  let pts = [];
  for (let i = 0; i < n; i++) {
    const angle = (i / n) * Math.PI * 2 - Math.PI / 2;
    const sc = i % 2 === 0 ? 1.0 : 0.84;
    pts.push(`${cx + rx * sc * Math.cos(angle)},${cy + ry * sc * Math.sin(angle)}`);
  }
  return 'M ' + pts.join(' L ') + ' Z';
};

const getShoutBubblePath = (cx, cy, rx, ry) => {
  const n = 18;
  let pts = [];
  for (let i = 0; i < n; i++) {
    const angle = (i / n) * Math.PI * 2 - Math.PI / 2;
    const sc = i % 2 === 0 ? 1.0 : 0.62;
    pts.push(`${cx + rx * sc * Math.cos(angle)},${cy + ry * sc * Math.sin(angle)}`);
  }
  return 'M ' + pts.join(' L ') + ' Z';
};

const getBubbleEdgePoint = (bubble, tipX, tipY) => {
  const { x, y, w, h } = bubble;
  const cx = x + w / 2, cy = y + h / 2;
  const dx = tipX - cx, dy = tipY - cy;
  if (dx === 0 && dy === 0) return { x: cx, y: y + h };
  const scaleX = (w / 2) / (Math.abs(dx) || 1);
  const scaleY = (h / 2) / (Math.abs(dy) || 1);
  const scale = Math.min(scaleX, scaleY) * 0.94;
  return { x: cx + dx * scale, y: cy + dy * scale };
};

// hitTestBubble: 'center' (inner 70%), 'edge' (outer 30%), or null
const hitTestBubble = (bubble, px, py) => {
  const { x, y, w, h } = bubble;
  if (px < x || px > x + w || py < y || py > y + h) return null;
  const relX = (px - x) / w - 0.5, relY = (py - y) / h - 0.5;
  const d = Math.sqrt(relX * relX + relY * relY) * Math.SQRT2;
  return d <= 0.7 ? 'center' : 'edge';
};

const hitTestTailHandle = (bubble, px, py) => {
  if (!bubble.tailTip) return false;
  const dx = px - bubble.tailTip.x, dy = py - bubble.tailTip.y;
  return dx * dx + dy * dy <= (TAIL_HANDLE_R + 5) ** 2;
};

// ---------- layer & frame factory ----------
const makeLayer = (name, type) => ({
  id: newId(), name, type, visible: true, opacity: 100,
});

const makeStarterFrame = (name, opts = {}) => {
  const sm = opts.sideMargin ?? 38;
  const defaultLayer = makeLayer('Layer 1', 'raster');
  return {
    id: newId(), name,
    canvasWidth: opts.canvasWidth ?? 690,
    sideMargin: sm,
    layers: [defaultLayer],
    activeLayerId: defaultLayer.id,
    blocks: opts.blocks ?? [
      { id: newId(), type: 'cut', height: 600, marginLeft: sm, marginRight: sm },
      { id: newId(), type: 'gap', height: 200 },
      { id: newId(), type: 'cut', height: 800, marginLeft: sm, marginRight: sm },
    ],
  };
};

// ---------- BubbleSVG ----------
const BubbleSVG = React.memo(function BubbleSVG({ bubble, isSelected, isActiveLayer, onPointerDown, typoPreset }) {
  const { type, x, y, w, h, tailTip, text } = bubble;
  const cx = x + w / 2, cy = y + h / 2, rx = w / 2, ry = h / 2;

  // 폰트 크기/굵기: typoPreset이 있으면 적용, 없으면 기존 기본값
  const fontSize = typoPreset ? typoPreset.size : (type === 'shout' ? 18 : 14);
  const fontWeight = typoPreset ? typoPreset.weight : (type === 'shout' ? 700 : 500);

  const renderTail = () => {
    if (!tailTip) return null;
    if (type === 'thought') {
      const dots = 3;
      return Array.from({ length: dots }, (_, i) => {
        const t = (i + 1) / (dots + 1);
        const ex = cx + (tailTip.x - cx) * t;
        const ey = (y + h) + (tailTip.y - (y + h)) * t;
        return <circle key={i} cx={ex} cy={ey} r={Math.max(1.5, 5 - i * 1.2)}
          fill="#fff" stroke="#1a1a1a" strokeWidth={2} />;
      });
    }
    const ep = getBubbleEdgePoint(bubble, tailTip.x, tailTip.y);
    const tdx = ep.x - tailTip.x, tdy = ep.y - tailTip.y;
    const tlen = Math.sqrt(tdx * tdx + tdy * tdy) || 1;
    const hw = type === 'shout' ? 14 : 11;
    const perp = { x: -tdy / tlen, y: tdx / tlen };
    const pts = `${ep.x + perp.x * hw},${ep.y + perp.y * hw} ${ep.x - perp.x * hw},${ep.y - perp.y * hw} ${tailTip.x},${tailTip.y}`;
    const dashProps = type === 'whisper' ? { strokeDasharray: '5,3' } : {};
    return <polygon points={pts} fill="#fff" stroke="#1a1a1a" strokeWidth={2.5} {...dashProps} />;
  };

  const renderShape = () => {
    if (type === 'normal' || type === 'whisper') {
      const path = getRoundedRectPath(x, y, w, h, 108);
      return <>
        <path d={path} fill="#fff" stroke="#1a1a1a" strokeWidth={2.5}
          strokeDasharray={type === 'whisper' ? '7,4' : undefined} />
        {isSelected && <path d={path} fill="none" stroke="#c43a2c" strokeWidth={2} strokeDasharray="5,3" />}
      </>;
    }
    if (type === 'thought') {
      const path = getThoughtBubblePath(cx, cy, rx, ry);
      return <>
        <path d={path} fill="#fff" stroke="#1a1a1a" strokeWidth={2.5} />
        {isSelected && <path d={path} fill="none" stroke="#c43a2c" strokeWidth={2} strokeDasharray="5,3" />}
      </>;
    }
    if (type === 'shout') {
      const path = getShoutBubblePath(cx, cy, rx, ry);
      return <>
        <path d={path} fill="#fff" stroke="#1a1a1a" strokeWidth={3.5} strokeLinejoin="miter" />
        {isSelected && <path d={path} fill="none" stroke="#c43a2c" strokeWidth={2.5} strokeDasharray="5,3" />}
      </>;
    }
  };

  // 텍스트 영역: 타입별 내부 패딩 (shout은 뾰족한 부분 피해서 더 줄임)
  const tpx = type === 'shout' ? w * 0.22 : type === 'thought' ? w * 0.1 : 12;
  const tpy = type === 'shout' ? h * 0.22 : type === 'thought' ? h * 0.1 : 8;

  return (
    <g onPointerDown={isActiveLayer ? onPointerDown : undefined} style={{ cursor: isActiveLayer ? 'default' : 'auto' }}>
      {renderTail()}
      {renderShape()}
      {/* foreignObject covers full bubble box; inner div uses flex to center x AND y */}
      <foreignObject x={x} y={y} width={Math.max(1, w)} height={Math.max(1, h)}
        style={{ pointerEvents: 'none' }}>
        <div xmlns="http://www.w3.org/1999/xhtml" style={{
          width: '100%', height: '100%',
          display: 'flex', alignItems: 'center', justifyContent: 'center',
          padding: `${tpy}px ${tpx}px`,
          boxSizing: 'border-box',
        }}>
          <div style={{
            fontFamily: 'Pretendard, sans-serif',
            fontSize,
            fontWeight,
            color: '#1a1a1a', wordBreak: 'break-word', userSelect: 'none',
            textAlign: 'center', lineHeight: 1.4, whiteSpace: 'pre-wrap',
            width: '100%',
          }}>{text || ''}</div>
        </div>
      </foreignObject>
      {isSelected && tailTip && (
        <circle cx={tailTip.x} cy={tailTip.y} r={TAIL_HANDLE_R}
          fill="#c43a2c" stroke="#fff" strokeWidth={2} style={{ cursor: 'crosshair' }} />
      )}
      {isSelected && !tailTip && (
        <circle cx={cx} cy={y + h + 22} r={TAIL_HANDLE_R}
          fill="#fff" stroke="#c43a2c" strokeWidth={2} strokeDasharray="3,2"
          style={{ cursor: 'crosshair' }} />
      )}
    </g>
  );
});

// ---------- LayerRow ----------
const LayerRow = ({ layer, isActive, canMergeDown, onActivate, onToggleVisible,
  onOpacityChange, onRename, onDuplicate, onMergeDown, onDelete, onDragHandlePointerDown, isDragging }) => {
  const [expanded, setExpanded] = useState(false);

  return (
    <div className={`layer-row ${isActive ? 'active' : ''} ${layer.type === 'vector' ? 'vector-layer' : ''} ${isDragging ? 'dragging' : ''}`}
      onClick={onActivate}>
      <div className="layer-row-top">
        {/* 드래그 핸들 */}
        <button
          className="layer-drag-handle"
          onPointerDown={onDragHandlePointerDown}
          onClick={e => e.stopPropagation()}
          title="드래그해서 순서 변경"
        >
          <svg width="10" height="16" viewBox="0 0 10 16" fill="currentColor">
            <circle cx="3" cy="3" r="1.2"/><circle cx="7" cy="3" r="1.2"/>
            <circle cx="3" cy="8" r="1.2"/><circle cx="7" cy="8" r="1.2"/>
            <circle cx="3" cy="13" r="1.2"/><circle cx="7" cy="13" r="1.2"/>
          </svg>
        </button>
        <button className={`layer-eye-btn ${!layer.visible ? 'hidden' : ''}`}
          onClick={e => { e.stopPropagation(); onToggleVisible(); }} title={layer.visible ? '숨기기' : '표시'}>
          {layer.visible ? '👁' : '🚫'}
        </button>
        <span className={`layer-type-badge ${layer.type}`}>{layer.type === 'raster' ? 'R' : 'V'}</span>
        <input className="layer-name-input" value={layer.name}
          onClick={e => e.stopPropagation()} onChange={e => onRename(e.target.value)} />
        <button className="layer-eye-btn" style={{ fontSize: 10 }}
          onClick={e => { e.stopPropagation(); setExpanded(v => !v); }}>⋯</button>
      </div>
      <div className="layer-row-opacity" onClick={e => e.stopPropagation()}>
        <span className="layer-opacity-label">op</span>
        <input type="range" min="0" max="100" step="1" className="layer-opacity-slider"
          value={layer.opacity} onChange={e => onOpacityChange(parseInt(e.target.value, 10))} />
        <span className="layer-opacity-num">{layer.opacity}%</span>
      </div>
      {expanded && (
        <div className="layer-actions-row" onClick={e => e.stopPropagation()}>
          <button className="layer-action-btn" onClick={onDuplicate}>copy</button>
          <button className="layer-action-btn" onClick={onMergeDown}
            disabled={!canMergeDown} title={canMergeDown ? '아래 래스터 레이어와 병합' : '아래 래스터 레이어 없음'}>
            merge↓
          </button>
          <button className="layer-action-btn danger" onClick={onDelete}>del</button>
        </div>
      )}
    </div>
  );
};

// ---------- CSS ----------
const STYLES = `
@import url('https://cdn.jsdelivr.net/gh/orioncactus/pretendard@v1.3.9/dist/web/static/pretendard.min.css');
@import url('https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@400;500;600&display=swap');

.conti-root {
  --bg: #f3f0e8; --bg-panel: #ebe6d9; --bg-canvas-area: #ddd8c8;
  --paper: #fdfbf5; --cut: #ffffff; --gap: #d9d9d9;
  --ink: #16140f; --ink-2: #3a3631; --muted: #837e72; --line: #cac3b1;
  --accent: #c43a2c; --accent-soft: #f1ddd9;
  --layer-raster: #3a7bd5; --layer-vector: #6a3ad5;
  position: fixed; inset: 0; display: flex; flex-direction: column;
  font-family: 'Pretendard', -apple-system, system-ui, sans-serif;
  color: var(--ink); background: var(--bg); user-select: none; -webkit-user-select: none; overflow: hidden;
}
.conti-root *, .conti-root *::before, .conti-root *::after { box-sizing: border-box; }
.conti-root .mono { font-family: 'JetBrains Mono', ui-monospace, monospace; }
.conti-root button { font-family: inherit; cursor: pointer; border: none; background: none; color: inherit; }
.conti-root input { font-family: inherit; }

/* topbar */
.conti-topbar {
  display: flex; align-items: center; height: 56px; flex: 0 0 56px;
  padding: 0 18px; background: var(--bg); border-bottom: 1px solid var(--line); gap: 16px; overflow: hidden;
}
.conti-brand { display: flex; align-items: center; gap: 10px; flex-shrink: 0; }
.conti-brand-mark { width: 22px; height: 22px; border-radius: 50%; background: var(--ink); position: relative; }
.conti-brand-mark::after {
  content: ''; position: absolute; top: 6px; left: 6px; width: 10px; height: 10px; border-radius: 50%; background: var(--paper);
}
.conti-brand-name { font-weight: 700; font-size: 15px; letter-spacing: -0.01em; }
.conti-brand-version { font-family: 'JetBrains Mono', monospace; font-size: 10px; color: var(--muted); margin-top: 1px; }

.conti-tool { display: flex; align-items: center; gap: 8px; flex-shrink: 0; }
.conti-tool-sep { width: 1px; height: 24px; background: var(--line); flex-shrink: 0; }
.conti-tool-label { font-family: 'JetBrains Mono', monospace; font-size: 10px; letter-spacing: 0.08em; color: var(--muted); text-transform: uppercase; flex-shrink: 0; }
.conti-tool input[type="range"] {
  -webkit-appearance: none; appearance: none; width: 100px; height: 4px; background: var(--line); border-radius: 999px; outline: none;
}
.conti-tool input[type="range"]::-webkit-slider-thumb {
  -webkit-appearance: none; appearance: none; width: 14px; height: 14px;
  background: var(--ink); border-radius: 50%; cursor: pointer; border: 2px solid var(--paper); box-shadow: 0 0 0 1px var(--ink);
}
.conti-num {
  width: 56px; padding: 4px 6px; font-family: 'JetBrains Mono', monospace; font-size: 12px;
  background: var(--paper); border: 1px solid var(--line); border-radius: 4px; text-align: right; color: var(--ink);
}
.conti-num:focus { outline: none; border-color: var(--ink); }
.conti-tool-unit { font-family: 'JetBrains Mono', monospace; font-size: 11px; color: var(--muted); margin-left: -4px; }
.conti-pen-preview {
  width: 38px; height: 38px; display: flex; align-items: center; justify-content: center;
  background: var(--paper); border: 1px solid var(--line); border-radius: 50%; flex-shrink: 0;
}
.conti-pen-dot { border-radius: 50%; }

/* pen color picker */
.conti-color-picker {
  display: flex; align-items: center; gap: 6px;
}
.conti-color-btn {
  width: 22px; height: 22px; border-radius: 50%; border: 2px solid transparent;
  cursor: pointer; flex-shrink: 0; transition: all 0.12s ease; padding: 0;
  box-shadow: 0 0 0 1px rgba(0,0,0,0.15);
}
.conti-color-btn:hover { transform: scale(1.15); }
.conti-color-btn.active {
  border-color: var(--ink); box-shadow: 0 0 0 1px rgba(0,0,0,0.15), 0 0 0 3px var(--paper), 0 0 0 4.5px var(--ink);
}
.conti-actions { display: flex; align-items: center; gap: 6px; flex-shrink: 0; }
.conti-icon-btn {
  display: flex; align-items: center; gap: 5px; padding: 5px 9px;
  font-family: 'JetBrains Mono', monospace; font-size: 11px; letter-spacing: 0.04em;
  color: var(--ink-2); background: transparent; border: 1px solid transparent; border-radius: 5px;
  transition: all 0.12s ease; text-transform: lowercase; white-space: nowrap; flex-shrink: 0;
}
.conti-icon-btn:hover:not(:disabled) { background: var(--bg-panel); border-color: var(--line); }
.conti-icon-btn:active:not(:disabled) { transform: translateY(1px); }
.conti-icon-btn:disabled { opacity: 0.35; cursor: not-allowed; }
.conti-icon-btn.active { background: var(--ink); color: var(--paper); border-color: var(--ink); }
.conti-icon-btn.danger:hover:not(:disabled) { color: var(--accent); border-color: var(--accent); }
.conti-icon-btn.accent { background: var(--accent); color: var(--paper); border-color: var(--accent); }

/* selection bar */
.conti-sel-bar {
  display: flex; align-items: center; gap: 4px; padding: 3px 8px;
  background: var(--accent-soft); border: 1px solid rgba(196,58,44,0.25); border-radius: 6px; flex-shrink: 0;
}
.conti-sel-bar .conti-sel-label {
  font-family: 'JetBrains Mono', monospace; font-size: 10px; letter-spacing: 0.1em;
  color: var(--accent); text-transform: uppercase; margin-right: 4px;
}
/* bubble bar */
.conti-bubble-bar {
  display: flex; align-items: center; gap: 4px; padding: 3px 8px;
  background: rgba(106,58,213,0.08); border: 1px solid rgba(106,58,213,0.22); border-radius: 6px; flex-shrink: 0;
}
.conti-bubble-bar .conti-bubble-label {
  font-family: 'JetBrains Mono', monospace; font-size: 10px; letter-spacing: 0.1em;
  color: var(--layer-vector); text-transform: uppercase; margin-right: 4px;
}
.conti-bubble-type-btn {
  padding: 3px 9px; border-radius: 4px; font-size: 11px; font-family: 'Pretendard', sans-serif;
  border: 1px solid rgba(106,58,213,0.3); color: #4a2ab0; background: transparent; transition: all 0.1s;
}
.conti-bubble-type-btn.active { background: var(--layer-vector); color: #fff; border-color: var(--layer-vector); }
.conti-bubble-type-btn:hover:not(.active) { background: rgba(106,58,213,0.12); }

/* main */
.conti-main { display: flex; flex: 1; min-height: 0; }

/* sidebar */
.conti-sidebar {
  width: 240px; flex: 0 0 240px; background: var(--bg-panel); border-right: 1px solid var(--line);
  overflow-y: auto; padding: 20px 18px;
}
.conti-sidebar.right { border-right: none; border-left: 1px solid var(--line); width: 248px; flex: 0 0 248px; }
.conti-section { margin-bottom: 24px; }
.conti-section h3 {
  font-family: 'JetBrains Mono', monospace; font-size: 10px; letter-spacing: 0.14em;
  color: var(--muted); text-transform: uppercase; margin: 0 0 10px 0;
  display: flex; align-items: center; justify-content: space-between;
}
.conti-section h3 .count { color: var(--ink); }
.conti-section h3::before {
  content: ''; flex: 0 0 6px; height: 6px; background: var(--accent); border-radius: 50%; margin-right: 8px;
}
.conti-preset-grid { display: grid; grid-template-columns: 1fr 1fr; gap: 6px; }
.conti-preset {
  padding: 10px 8px; background: var(--paper); border: 1px solid var(--line); border-radius: 5px;
  font-family: 'JetBrains Mono', monospace; font-size: 11px; color: var(--ink); text-align: left;
  transition: all 0.12s ease; display: flex; flex-direction: column; gap: 2px;
}
.conti-preset:hover:not(:disabled) { background: var(--ink); color: var(--paper); border-color: var(--ink); }
.conti-preset:hover:not(:disabled) .conti-preset-sub { color: var(--paper); opacity: 0.6; }
.conti-preset:disabled { opacity: 0.4; cursor: not-allowed; }
.conti-preset-num { font-weight: 600; font-size: 13px; }
.conti-preset-sub { font-size: 9px; color: var(--muted); letter-spacing: 0.06em; text-transform: uppercase; }
.conti-config-row {
  display: flex; align-items: center; justify-content: space-between;
  padding: 8px 0; border-bottom: 1px dashed var(--line);
}
.conti-config-row:last-child { border-bottom: none; }
.conti-config-row label { font-family: 'JetBrains Mono', monospace; font-size: 11px; color: var(--muted); }
.conti-config-row input {
  width: 70px; padding: 4px 6px; font-family: 'JetBrains Mono', monospace; font-size: 12px;
  background: var(--paper); border: 1px solid var(--line); border-radius: 4px; text-align: right; color: var(--ink);
}
.conti-config-row input:focus { outline: none; border-color: var(--ink); }
.conti-config-readonly { font-family: 'JetBrains Mono', monospace; font-size: 12px; color: var(--ink); font-weight: 600; }

/* frame list */
.conti-frame-row {
  display: flex; align-items: center; gap: 4px; padding: 6px 8px; background: var(--paper);
  border: 1px solid var(--line); border-radius: 5px; margin-bottom: 4px; cursor: pointer; transition: all 0.12s ease;
}
.conti-frame-row:hover { border-color: var(--ink-2); }
.conti-frame-row.active { background: var(--ink); border-color: var(--ink); }
.conti-frame-row.active input { color: var(--paper); }
.conti-frame-row.active .del { color: rgba(255,255,255,0.6); }
.conti-frame-row input {
  flex: 1; min-width: 0; padding: 2px 4px; font-family: 'Pretendard', sans-serif; font-size: 12px;
  background: transparent; border: 1px solid transparent; border-radius: 3px; color: var(--ink); cursor: text;
}
.conti-frame-row input:focus { outline: none; border-color: var(--line); background: var(--paper); color: var(--ink) !important; }
.conti-frame-row .del {
  width: 22px; height: 22px; display: flex; align-items: center; justify-content: center;
  font-size: 14px; color: var(--muted); border-radius: 3px; flex-shrink: 0; transition: all 0.12s ease;
}
.conti-frame-row .del:hover:not(:disabled) { background: var(--accent-soft); color: var(--accent); }
.conti-frame-row .del:disabled { opacity: 0.3; cursor: not-allowed; }
.conti-add-btn {
  width: 100%; padding: 10px; margin-top: 4px; font-family: 'JetBrains Mono', monospace; font-size: 11px;
  color: var(--muted); background: transparent; border: 1px dashed var(--line); border-radius: 5px;
  transition: all 0.12s ease; letter-spacing: 0.04em;
}
.conti-add-btn:hover { color: var(--ink); border-color: var(--ink); border-style: solid; background: var(--paper); }

/* canvas */
.conti-canvas-area {
  flex: 1; min-width: 0;
  background: radial-gradient(circle at 1px 1px, var(--line) 1px, transparent 0) 0 0 / 24px 24px, var(--bg-canvas-area);
  overflow: auto; position: relative;
}
.conti-canvas-inner {
  display: flex; align-items: flex-start; gap: 140px; padding: 56px 100px 200px 100px;
  width: max-content; min-width: 100%;
}
.conti-frame { position: relative; flex-shrink: 0; display: flex; flex-direction: column; }
.conti-frame-label {
  font-family: 'JetBrains Mono', monospace; font-size: 12px; color: var(--muted);
  padding: 0 0 8px 2px; cursor: pointer; user-select: none; letter-spacing: 0.04em; transition: color 0.12s ease;
}
.conti-frame-label:hover { color: var(--ink-2); }
.conti-frame.selected .conti-frame-label { color: var(--accent); font-weight: 600; }
.conti-frame-stage {
  position: relative; background: var(--gap);
  box-shadow: 0 1px 2px rgba(0,0,0,0.04), 0 4px 12px rgba(0,0,0,0.06), 0 16px 40px rgba(0,0,0,0.08);
  transition: outline 0.12s ease;
}
.conti-frame.selected .conti-frame-stage { outline: 2px solid var(--accent); outline-offset: 4px; }
.conti-block { position: absolute; pointer-events: none; }
.conti-block.cut { background: var(--cut); }
.conti-block.gap { background: var(--gap); }
.conti-frame-canvas { position: absolute; top: 0; left: 0; display: block; pointer-events: none; }
.conti-frame-overlay { position: absolute; top: 0; left: 0; display: block; z-index: 5; }
.conti-frame-overlay.tool-pen { cursor: crosshair; }
.conti-frame-overlay.tool-lasso { cursor: cell; }
.conti-frame-overlay.tool-lasso-selected { cursor: move; }
.conti-frame-overlay.tool-vector { cursor: default; }
.conti-bubble-svg { position: absolute; top: 0; left: 0; overflow: visible; pointer-events: none; }
.conti-bubble-svg.interactive { pointer-events: all; z-index: 6; }

/* dimension */
.conti-dim { position: absolute; display: flex; align-items: center; pointer-events: none; white-space: nowrap; }
.conti-dim-bracket { width: 12px; flex-shrink: 0; position: relative; height: 100%; }
.conti-dim-bracket::before, .conti-dim-bracket::after {
  content: ''; position: absolute; left: 0; width: 12px; height: 1px; background: var(--accent);
}
.conti-dim-bracket::before { top: 0; } .conti-dim-bracket::after { bottom: 0; }
.conti-dim-bracket .vline { position: absolute; left: 0; top: 0; bottom: 0; width: 1px; background: var(--accent); }
.conti-dim-text { margin-left: 8px; font-family: 'JetBrains Mono', monospace; font-size: 11px; display: flex; flex-direction: column; gap: 1px; }
.conti-dim-kind { font-size: 9px; letter-spacing: 0.08em; color: var(--muted); text-transform: uppercase; }
.conti-dim-size { font-weight: 600; color: var(--ink); }
.conti-dim.gap .conti-dim-bracket::before, .conti-dim.gap .conti-dim-bracket::after,
.conti-dim.gap .vline { background: var(--muted); }
.conti-dim.gap .conti-dim-size { color: var(--muted); }

/* ===== LAYER PANEL ===== */
.layer-add-row { display: flex; gap: 6px; margin-bottom: 10px; }
.layer-add-btn {
  flex: 1; padding: 6px 8px; font-size: 10px; letter-spacing: 0.06em;
  font-family: 'JetBrains Mono', monospace; text-transform: uppercase;
  border: 1px dashed var(--line); border-radius: 4px; color: var(--muted); background: transparent; transition: all 0.12s;
}
.layer-add-btn:hover { color: var(--ink); border-color: var(--ink); border-style: solid; background: var(--paper); }
.layer-add-btn.vector { border-color: rgba(106,58,213,0.4); color: var(--layer-vector); }
.layer-add-btn.vector:hover { background: rgba(106,58,213,0.08); border-color: var(--layer-vector); border-style: solid; }

.layer-row {
  display: flex; flex-direction: column; padding: 7px 8px; background: var(--paper);
  border: 1px solid var(--line); border-radius: 6px; margin-bottom: 4px; cursor: pointer; transition: all 0.12s ease;
}
.layer-row:hover { border-color: var(--ink-2); }
.layer-row.active { border-color: var(--accent); box-shadow: inset 3px 0 0 var(--accent); background: var(--accent-soft); }
.layer-row.active.vector-layer { border-color: var(--layer-vector); box-shadow: inset 3px 0 0 var(--layer-vector); background: rgba(106,58,213,0.06); }
.layer-row.dragging { opacity: 0.35; border-style: dashed; border-color: var(--layer-vector); }
.layer-row-top { display: flex; align-items: center; gap: 6px; }
.layer-drag-handle {
  width: 14px; height: 22px; display: flex; align-items: center; justify-content: center;
  flex-shrink: 0; color: var(--muted); cursor: grab; border-radius: 3px; touch-action: none;
  transition: color 0.12s ease, background 0.12s ease;
}
.layer-drag-handle:hover { color: var(--ink); background: var(--bg-panel); }
.layer-drag-handle:active { cursor: grabbing; }
.layer-drop-indicator {
  height: 3px; background: var(--layer-vector); border-radius: 2px; margin: 1px 0; position: relative;
}
.layer-drop-indicator::before, .layer-drop-indicator::after {
  content: ''; position: absolute; top: 50%; transform: translateY(-50%);
  width: 6px; height: 6px; border-radius: 50%; background: var(--layer-vector);
}
.layer-drop-indicator::before { left: -3px; }
.layer-drop-indicator::after { right: -3px; }
.layer-eye-btn {
  width: 20px; height: 20px; display: flex; align-items: center; justify-content: center;
  font-size: 12px; border-radius: 3px; flex-shrink: 0; color: var(--ink); transition: all 0.1s;
}
.layer-eye-btn:hover { background: var(--bg-panel); }
.layer-eye-btn.hidden { color: var(--muted); }
.layer-type-badge {
  font-family: 'JetBrains Mono', monospace; font-size: 8px; letter-spacing: 0.06em;
  text-transform: uppercase; padding: 2px 4px; border-radius: 3px; flex-shrink: 0;
}
.layer-type-badge.raster { background: rgba(58,123,213,0.15); color: var(--layer-raster); }
.layer-type-badge.vector { background: rgba(106,58,213,0.15); color: var(--layer-vector); }
.layer-name-input {
  flex: 1; min-width: 0; padding: 2px 4px; font-size: 12px; background: transparent;
  border: 1px solid transparent; border-radius: 3px; color: var(--ink); font-family: 'Pretendard', sans-serif;
}
.layer-name-input:focus { outline: none; border-color: var(--line); background: var(--paper); }
.layer-row-opacity {
  display: flex; align-items: center; gap: 6px; margin-top: 6px;
}
.layer-opacity-label {
  font-family: 'JetBrains Mono', monospace; font-size: 9px; color: var(--muted);
  letter-spacing: 0.06em; text-transform: uppercase; flex-shrink: 0; width: 14px;
}
.layer-opacity-slider {
  -webkit-appearance: none; appearance: none; flex: 1; height: 3px;
  background: var(--line); border-radius: 999px; outline: none;
}
.layer-opacity-slider::-webkit-slider-thumb {
  -webkit-appearance: none; appearance: none; width: 12px; height: 12px;
  background: var(--ink); border-radius: 50%; cursor: pointer; border: 2px solid var(--paper); box-shadow: 0 0 0 1px var(--ink);
}
.layer-opacity-num { font-family: 'JetBrains Mono', monospace; font-size: 10px; color: var(--muted); flex-shrink: 0; width: 28px; text-align: right; }
.layer-actions-row { display: flex; gap: 3px; margin-top: 5px; }
.layer-action-btn {
  flex: 1; padding: 3px 4px; font-size: 9px; letter-spacing: 0.04em;
  font-family: 'JetBrains Mono', monospace; text-transform: uppercase;
  border: 1px solid var(--line); border-radius: 3px; color: var(--muted); background: transparent; transition: all 0.1s;
}
.layer-action-btn:hover { color: var(--ink); border-color: var(--ink-2); background: var(--bg-panel); }
.layer-action-btn:disabled { opacity: 0.3; cursor: not-allowed; }
.layer-action-btn.danger:hover { color: var(--accent); border-color: var(--accent); }

/* bubble editor */
.bubble-editor {
  padding: 10px; background: rgba(106,58,213,0.06);
  border: 1px solid rgba(106,58,213,0.2); border-radius: 6px; margin-bottom: 8px;
}
.bubble-editor-label {
  font-family: 'JetBrains Mono', monospace; font-size: 9px; letter-spacing: 0.1em;
  text-transform: uppercase; color: var(--layer-vector); margin-bottom: 8px;
}

/* typo preset selector (in bubble editor) */
.typo-preset-label {
  font-family: 'JetBrains Mono', monospace; font-size: 9px; letter-spacing: 0.08em;
  text-transform: uppercase; color: var(--muted); margin-bottom: 5px;
}
.typo-preset-grid {
  display: grid; grid-template-columns: 1fr 1fr 1fr; gap: 4px; margin-bottom: 8px;
}
.typo-preset-btn {
  display: flex; flex-direction: column; align-items: center; justify-content: center;
  padding: 5px 4px; border-radius: 5px; gap: 1px;
  border: 1px solid rgba(106,58,213,0.25); background: transparent;
  transition: all 0.12s; cursor: pointer;
}
.typo-preset-btn:hover { background: rgba(106,58,213,0.1); border-color: var(--layer-vector); }
.typo-preset-btn.active { background: var(--layer-vector); border-color: var(--layer-vector); }
.typo-preset-btn.active .typo-preset-name,
.typo-preset-btn.active .typo-preset-size { color: #fff; }
.typo-preset-name {
  font-family: 'Pretendard', sans-serif; font-size: 10px; font-weight: 600;
  color: var(--ink-2); letter-spacing: -0.01em;
}
.typo-preset-size {
  font-family: 'JetBrains Mono', monospace; font-size: 9px; color: var(--muted);
}

/* typo system settings (in left sidebar) */
.typo-system-list { display: flex; flex-direction: column; gap: 4px; }
.typo-system-row {
  display: flex; align-items: center; gap: 5px;
  padding: 5px 7px; background: var(--paper);
  border: 1px solid var(--line); border-radius: 5px;
}
.typo-system-index {
  font-size: 9px; color: var(--muted); flex-shrink: 0; width: 10px; text-align: center;
}
.typo-system-name {
  flex: 1; min-width: 0; padding: 2px 4px; font-size: 11px;
  font-family: 'Pretendard', sans-serif; background: transparent;
  border: 1px solid transparent; border-radius: 3px; color: var(--ink);
}
.typo-system-name:focus { outline: none; border-color: var(--line); background: var(--bg-panel); }
.typo-system-size-wrap { display: flex; align-items: center; gap: 1px; flex-shrink: 0; }
.typo-system-size {
  width: 38px; padding: 2px 4px; font-family: 'JetBrains Mono', monospace; font-size: 11px;
  background: var(--bg-panel); border: 1px solid var(--line); border-radius: 3px;
  text-align: right; color: var(--ink);
}
.typo-system-size:focus { outline: none; border-color: var(--ink); }
.typo-system-pt {
  font-family: 'JetBrains Mono', monospace; font-size: 9px; color: var(--muted); flex-shrink: 0;
}
.typo-system-weight {
  width: 46px; padding: 2px 3px; font-family: 'JetBrains Mono', monospace; font-size: 10px;
  background: var(--bg-panel); border: 1px solid var(--line); border-radius: 3px;
  color: var(--ink); flex-shrink: 0; appearance: none; text-align: center; cursor: pointer;
}
.typo-system-weight:focus { outline: none; border-color: var(--ink); }
.bubble-text-input {
  width: 100%; padding: 6px 8px; font-family: 'Pretendard', sans-serif; font-size: 12px;
  background: var(--paper); border: 1px solid var(--line); border-radius: 4px;
  color: var(--ink); resize: vertical; min-height: 60px; user-select: text;
}
.bubble-text-input:focus { outline: none; border-color: var(--layer-vector); }
.bubble-del-btn {
  width: 100%; padding: 6px; margin-top: 6px; font-size: 11px;
  font-family: 'JetBrains Mono', monospace; letter-spacing: 0.04em;
  border: 1px solid var(--line); border-radius: 4px; color: var(--muted); background: transparent; transition: all 0.1s;
}
.bubble-del-btn:hover { color: var(--accent); border-color: var(--accent); }

/* block list */
.conti-block-row {
  position: relative; display: flex; align-items: center; gap: 6px; padding: 6px 8px;
  background: var(--paper); border: 1px solid var(--line); border-radius: 5px; margin-bottom: 4px;
  transition: border-color 0.12s ease, opacity 0.15s ease;
}
.conti-block-row:hover { border-color: var(--ink-2); }
.conti-block-row.dragging { opacity: 0.35; border-color: var(--accent); border-style: dashed; }
.conti-drag-handle {
  width: 14px; height: 22px; display: flex; align-items: center; justify-content: center;
  flex-shrink: 0; color: var(--muted); cursor: grab; border-radius: 3px; touch-action: none; transition: color 0.12s ease, background 0.12s ease;
}
.conti-drag-handle:hover { color: var(--ink); background: var(--bg-panel); }
.conti-drag-handle:active { cursor: grabbing; }
.conti-block-tag {
  font-family: 'JetBrains Mono', monospace; font-size: 9px; letter-spacing: 0.06em;
  text-transform: uppercase; padding: 2px 5px; border-radius: 3px; flex-shrink: 0;
}
.conti-block-tag.cut { background: var(--ink); color: var(--paper); }
.conti-block-tag.gap { background: var(--accent-soft); color: var(--accent); }
.conti-block-row input {
  width: 100%; min-width: 0; flex: 1; padding: 2px 4px; font-family: 'JetBrains Mono', monospace; font-size: 11px;
  background: transparent; border: 1px solid transparent; border-radius: 3px; text-align: right; color: var(--ink);
}
.conti-block-row input:focus { outline: none; border-color: var(--line); background: var(--bg-panel); }
.conti-block-row .del {
  width: 22px; height: 22px; display: flex; align-items: center; justify-content: center;
  font-size: 14px; color: var(--muted); border-radius: 3px; flex-shrink: 0; transition: all 0.12s ease;
}
.conti-block-row .del:hover { background: var(--accent-soft); color: var(--accent); }
.conti-block-row.has-margin { border-radius: 5px 5px 0 0; margin-bottom: 0; }
.conti-block-margin-row {
  display: flex; align-items: center; gap: 4px; padding: 4px 8px 6px 8px;
  margin-top: -6px; margin-bottom: 4px; background: var(--bg-panel);
  border: 1px solid var(--line); border-top: none; border-radius: 0 0 5px 5px;
}
.conti-margin-label {
  font-family: 'JetBrains Mono', monospace; font-size: 9px; letter-spacing: 0.06em;
  color: var(--muted); text-transform: uppercase; flex-shrink: 0; width: 10px; text-align: center;
}
.conti-margin-sep { flex: 1; height: 1px; background: var(--line); }
.conti-block-margin-row input {
  width: 42px; padding: 2px 4px; font-family: 'JetBrains Mono', monospace; font-size: 10px;
  background: var(--paper); border: 1px solid var(--line); border-radius: 3px; text-align: right; color: var(--ink); flex-shrink: 0;
}
.conti-block-margin-row input:focus { outline: none; border-color: var(--ink); }
.conti-empty {
  padding: 18px 12px; text-align: center; font-size: 12px; color: var(--muted);
  border: 1px dashed var(--line); border-radius: 5px;
}
.conti-status {
  position: fixed; bottom: 12px; left: 50%; transform: translateX(-50%);
  display: flex; gap: 16px; padding: 6px 14px;
  background: rgba(22,20,15,0.85); color: var(--paper);
  font-family: 'JetBrains Mono', monospace; font-size: 10px; letter-spacing: 0.06em;
  border-radius: 999px; backdrop-filter: blur(8px); -webkit-backdrop-filter: blur(8px);
  pointer-events: none; z-index: 10;
}
.conti-status .dot { width: 6px; height: 6px; background: #6fc275; border-radius: 50%; align-self: center; }
.conti-status .dot.lasso { background: var(--accent); }
.conti-status .dot.vector { background: var(--layer-vector); }

/* viewport-active */
.conti-block-row.viewport-active {
  border-color: var(--accent); background: var(--accent-soft); box-shadow: inset 3px 0 0 var(--accent);
}
.conti-block-row.viewport-active .conti-block-tag.cut { background: var(--accent); }
.conti-block-row.viewport-active .conti-block-tag.gap { background: var(--accent); color: var(--paper); }
.conti-block-row.viewport-active input { color: var(--accent); font-weight: 600; }
.conti-block-margin-row.viewport-active {
  border-color: var(--accent); background: color-mix(in srgb, var(--accent-soft) 60%, var(--bg-panel));
  box-shadow: inset 3px 0 0 var(--accent);
}

@media (max-width: 900px) { .conti-sidebar.right { display: none; } }
@media (max-width: 700px) { .conti-sidebar { width: 200px; flex: 0 0 200px; } .conti-tool input[type="range"] { width: 70px; } }
`;

// ---------- FrameView ----------
const FrameView = forwardRef(function FrameView({
  frame, isSelected, showDimensions, activeTool, selectionPhase,
  getLayerBitmap, bubblesByLayer, selectedBubble, activeLayerType,
  typoPresets,
  onSelect, onPointerDown, onPointerMove, onPointerUp,
  onBubbleOverlayPointerDown, onBubbleOverlayPointerMove, onBubbleOverlayPointerUp,
}, ref) {
  const canvasRef = useRef(null);
  const overlayRef = useRef(null);
  const dprRef = useRef(1);

  const totalHeight = useMemo(() => frame.blocks.reduce((s, b) => s + b.height, 0), [frame.blocks]);

  const blockLayout = useMemo(() => {
    let y = 0, cutCounter = 0, gapCounter = 0;
    return frame.blocks.map(b => {
      const item = { ...b, top: y };
      if (b.type === 'cut') { cutCounter++; item.num = cutCounter; }
      else { gapCounter++; item.num = gapCounter; }
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
    for (const layer of frame.layers) {
      if (!layer.visible || layer.type !== 'raster') continue;
      ctx.save();
      ctx.globalAlpha = layer.opacity / 100;
      let y = 0;
      for (const b of frame.blocks) {
        const entry = getLayerBitmap(layer.id, b.id);
        if (entry) ctx.drawImage(entry.canvas, 0, 0, entry.canvas.width, entry.canvas.height,
          0, y - BITMAP_Y_PADDING, entry.logicalWidth, entry.logicalHeight);
        y += b.height;
      }
      ctx.restore();
    }
  }, [frame.blocks, frame.layers, getLayerBitmap]);

  useLayoutEffect(() => {
    const dpr = Math.min(window.devicePixelRatio || 1, DPR_CAP);
    dprRef.current = dpr;
    const c = canvasRef.current;
    if (c) {
      c.width = Math.max(1, frame.canvasWidth * dpr);
      c.height = Math.max(1, totalHeight * dpr);
      c.style.width = `${frame.canvasWidth}px`;
      c.style.height = `${totalHeight}px`;
      const ctx = c.getContext('2d');
      ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.scale(dpr, dpr);
      ctx.lineCap = 'round'; ctx.lineJoin = 'round';
    }
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
      oc.getContext('2d').clearRect(0, 0, oc.width, oc.height);
    },
  }), [redraw]);

  const isActiveFrame = isSelected;
  const fActiveLayer = frame.layers.find(l => l.id === frame.activeLayerId);
  const fActiveLayerType = fActiveLayer?.type || 'raster';
  const isVectorActive = fActiveLayerType === 'vector' && isActiveFrame;

  let overlayCursorClass = 'tool-pen';
  if (isVectorActive) {
    overlayCursorClass = 'tool-vector';
  } else if (activeTool === 'lasso') {
    overlayCursorClass = (['selected', 'dragging', 'resizing', 'rotating'].includes(selectionPhase))
      ? 'tool-lasso-selected' : 'tool-lasso';
  }

  const visibleVectorLayers = frame.layers.filter(l => l.visible && l.type === 'vector');

  return (
    <div className={`conti-frame ${isSelected ? 'selected' : ''}`} data-frame-id={frame.id}>
      <div className="conti-frame-label" onClick={() => onSelect(frame.id)}>{frame.name}</div>
      <div className="conti-frame-stage" style={{ width: `${frame.canvasWidth}px`, height: `${totalHeight}px` }}>
        {blockLayout.map(b => {
          const ml = b.type === 'cut' ? (b.marginLeft ?? frame.sideMargin) : 0;
          const mr = b.type === 'cut' ? (b.marginRight ?? frame.sideMargin) : 0;
          const bw = b.type === 'cut' ? Math.max(10, frame.canvasWidth - ml - mr) : frame.canvasWidth;
          return (
            <div key={b.id} className={`conti-block ${b.type}`}
              style={{ top: `${b.top}px`, left: `${ml}px`, width: `${bw}px`, height: `${b.height}px` }} />
          );
        })}
        <canvas ref={canvasRef} className="conti-frame-canvas" style={{ touchAction: 'none' }} />

        {/* Vector bubble SVG layers */}
        {visibleVectorLayers.map(layer => {
          const isThisLayerActive = layer.id === frame.activeLayerId && isActiveFrame;
          const layerBubbles = bubblesByLayer[layer.id] || [];
          return (
            <svg key={layer.id}
              className={`conti-bubble-svg ${isThisLayerActive ? 'interactive' : ''}`}
              width={frame.canvasWidth} height={totalHeight}
              style={{ opacity: layer.opacity / 100 }}>
              {layerBubbles.map(bubble => (
                <BubbleSVG key={bubble.id} bubble={bubble}
                  isSelected={selectedBubble?.bubbleId === bubble.id && selectedBubble?.frameId === frame.id}
                  isActiveLayer={isThisLayerActive}
                  typoPreset={bubble.typoPresetId != null
                    ? (typoPresets || []).find(p => p.id === bubble.typoPresetId) || null
                    : null}
                  onPointerDown={e => {
                    e.stopPropagation();
                    onBubbleOverlayPointerDown(e, frame.id, overlayRef.current, bubble);
                  }}
                />
              ))}
            </svg>
          );
        })}

        {/* Overlay canvas */}
        <canvas
          ref={overlayRef}
          className={`conti-frame-overlay ${overlayCursorClass}`}
          style={{ touchAction: 'none', zIndex: isVectorActive ? 7 : 5 }}
          onPointerDown={e => {
            onSelect(frame.id);
            if (isVectorActive) onBubbleOverlayPointerDown(e, frame.id, overlayRef.current, null);
            else onPointerDown(e, frame.id, overlayRef.current);
          }}
          onPointerMove={e => {
            if (isVectorActive) onBubbleOverlayPointerMove(e, frame.id, overlayRef.current);
            else onPointerMove(e, overlayRef.current);
          }}
          onPointerUp={e => {
            if (isVectorActive) onBubbleOverlayPointerUp(e, frame.id, overlayRef.current);
            else onPointerUp(e, overlayRef.current);
          }}
          onPointerCancel={e => {
            if (isVectorActive) onBubbleOverlayPointerUp(e, frame.id, overlayRef.current);
            else onPointerUp(e, overlayRef.current);
          }}
          onPointerLeave={e => {
            if (isVectorActive) onBubbleOverlayPointerUp(e, frame.id, overlayRef.current);
            else onPointerUp(e, overlayRef.current);
          }}
        />

        {showDimensions && blockLayout.map(b => (
          <div key={`dim-${b.id}`} className={`conti-dim ${b.type}`}
            style={{ top: `${b.top}px`, height: `${b.height}px`, left: `${frame.canvasWidth + 10}px` }}>
            <div className="conti-dim-bracket"><div className="vline" /></div>
            <div className="conti-dim-text">
              <span className="conti-dim-kind">{b.type === 'cut' ? `cut ${String(b.num).padStart(2,'0')}` : 'gap'}</span>
              <span className="conti-dim-size">{b.height}px</span>
            </div>
          </div>
        ))}
      </div>
    </div>
  );
});

// ===================================================================
//  MAIN COMPONENT
// ===================================================================
export default function ContiProgram() {
  const [frames, setFrames] = useState(() => [makeStarterFrame('Frame 1')]);
  const [selectedFrameId, setSelectedFrameId] = useState(() => frames[0].id);
  const selectedFrame = frames.find(f => f.id === selectedFrameId) || null;
  const activeLayer = selectedFrame?.layers.find(l => l.id === selectedFrame.activeLayerId) || null;
  const activeLayerType = activeLayer?.type || 'raster';

  // Per-frame, per-layer stroke storage
  // strokesByFrameRef.current[frameId][layerId] = { byBlock, bitmaps, history }
  const strokesByFrameRef = useRef({});
  const ensureLayerStore = useCallback((frameId, layerId) => {
    if (!strokesByFrameRef.current[frameId]) strokesByFrameRef.current[frameId] = {};
    if (!strokesByFrameRef.current[frameId][layerId])
      strokesByFrameRef.current[frameId][layerId] = { byBlock: {}, bitmaps: {}, history: [] };
    return strokesByFrameRef.current[frameId][layerId];
  }, []);

  for (const f of frames) for (const l of f.layers) ensureLayerStore(f.id, l.id);

  const getActiveRasterLayerId = useCallback(frame => {
    const l = frame.layers.find(x => x.id === frame.activeLayerId);
    return l?.type === 'raster' ? l.id : null;
  }, []);

  // Pen
  const [penSize, setPenSize] = useState(4);
  const [penOpacity, setPenOpacity] = useState(100);
  const [penColor, setPenColor] = useState('#0F0F0F');

  // Tool
  const [activeTool, setActiveTool] = useState('pen');
  const [hasSelection, setHasSelection] = useState(false);
  const [hasClipboard, setHasClipboard] = useState(false);
  const [selectionPhase, setSelectionPhase] = useState('idle');

  // Bubbles: { [layerId]: [bubble] }
  const [bubblesByLayer, setBubblesByLayer] = useState({});
  const [selectedBubble, setSelectedBubble] = useState(null); // {frameId, layerId, bubbleId}
  const [activeBubbleType, setActiveBubbleType] = useState('normal');

  // Typography presets (사용자가 편집 가능한 6개)
  const [typoPresets, setTypoPresets] = useState(DEFAULT_TYPO_PRESETS);

  const bubbleInterRef = useRef({ mode: null, frameId: null, layerId: null, bubbleId: null, startX: 0, startY: 0, origBubble: null });

  const drawingRef = useRef(null);
  const currentStrokeRef = useRef(null);

  const lassoRef = useRef({
    phase: 'idle', frameId: null, layerId: null,
    lassoPoints: [], selectedItems: [], bbox: null,
    transform: { tx: 0, ty: 0, scaleX: 1, scaleY: 1, angle: 0, flipH: false, flipV: false },
    dragStart: null, origTransform: null, dragHandle: null, origHandleDist: null,
  });

  const clipboardRef = useRef(null);
  const canvasAreaRef = useRef(null);
  const activeTouchPointersRef = useRef(new Map());
  const panStateRef = useRef(null);
  // two-finger tap → undo: tracks whether the 2-finger gesture moved (pan) or stayed (tap)
  const twoFingerTapRef = useRef({ active: false, startMap: null, moved: false });
  const frameRefs = useRef({});

  const selectAndScrollToFrame = useCallback(frameId => {
    setSelectedFrameId(frameId);
    const area = canvasAreaRef.current;
    if (!area) return;
    const el = area.querySelector(`[data-frame-id="${frameId}"]`);
    if (!el) return;
    const areaRect = area.getBoundingClientRect();
    const elRect = el.getBoundingClientRect();
    area.scrollTo({ left: area.scrollLeft + elRect.left - areaRect.left - 80, top: 0, behavior: 'smooth' });
  }, []);

  // ---------- bitmap management ----------
  const getBitmapDpr = useCallback(() => Math.min(window.devicePixelRatio || 1, DPR_CAP), []);

  const ensureBlockBitmap = useCallback((frameId, layerId, block, frameWidth, neededLocalMaxY) => {
    const store = ensureLayerStore(frameId, layerId);
    const dpr = getBitmapDpr();
    const required = Math.max(block.height, neededLocalMaxY ?? 0) + 2 * BITMAP_Y_PADDING;
    const targetH = Math.ceil(required / BITMAP_GROW_CHUNK) * BITMAP_GROW_CHUNK;
    let entry = store.bitmaps[block.id];
    if (!entry) { entry = createBlockBitmap(frameWidth, targetH, dpr); store.bitmaps[block.id] = entry; }
    else if (entry.logicalWidth !== frameWidth || entry.logicalHeight < required) {
      const next = createBlockBitmap(frameWidth, Math.max(targetH, entry.logicalHeight), dpr);
      blitBitmap(entry, next.ctx); store.bitmaps[block.id] = next; entry = next;
    }
    return entry;
  }, [ensureLayerStore, getBitmapDpr]);

  const clearBlockBitmap = useCallback((frameId, layerId, blockId) => {
    const entry = ensureLayerStore(frameId, layerId).bitmaps[blockId];
    if (!entry) return;
    entry.ctx.save(); entry.ctx.setTransform(1,0,0,1,0,0);
    entry.ctx.clearRect(0, 0, entry.canvas.width, entry.canvas.height);
    entry.ctx.restore();
  }, [ensureLayerStore]);

  const rebuildBlockBitmap = useCallback((frameId, layerId, block, frameWidth) => {
    const store = ensureLayerStore(frameId, layerId);
    const strokes = store.byBlock[block.id] || [];
    let maxY = 0;
    for (const s of strokes) if (!s.hidden && s.bbox?.maxY > maxY) maxY = s.bbox.maxY;
    const entry = ensureBlockBitmap(frameId, layerId, block, frameWidth, maxY);
    clearBlockBitmap(frameId, layerId, block.id);
    for (const s of strokes) if (!s.hidden) renderStrokeToCtx(entry.ctx, s, BITMAP_Y_PADDING);
  }, [ensureLayerStore, ensureBlockBitmap, clearBlockBitmap]);

  // ===================================================================
  //  UNDO — remove the last drawn stroke from the active raster layer
  // ===================================================================
  const undoLastStroke = useCallback(() => {
    if (!selectedFrame) return;
    const activeLayerId = getActiveRasterLayerId(selectedFrame);
    if (!activeLayerId) return;
    const store = ensureLayerStore(selectedFrameId, activeLayerId);
    if (!store.history.length) return;
    const { layerId, blockId } = store.history.pop();
    const arr = store.byBlock[blockId];
    if (arr && arr.length > 0) arr.pop();
    const block = selectedFrame.blocks.find(b => b.id === blockId);
    if (block) rebuildBlockBitmap(selectedFrameId, layerId, block, selectedFrame.canvasWidth);
    frameRefs.current[selectedFrameId]?.redraw();
  }, [selectedFrame, selectedFrameId, getActiveRasterLayerId, ensureLayerStore, rebuildBlockBitmap]);

  const getLayerBitmapRef = useRef({});
  for (const f of frames) {
    if (!getLayerBitmapRef.current[f.id]) {
      const fid = f.id;
      getLayerBitmapRef.current[fid] = (layerId, blockId) => {
        const fStore = strokesByFrameRef.current[fid];
        return fStore?.[layerId]?.bitmaps[blockId] || null;
      };
    }
  }

  // ---------- block-row drag ----------
  const [dragId, setDragId] = useState(null);
  const [dragOverId, setDragOverId] = useState(null);
  const [dragOverPos, setDragOverPos] = useState(null);
  const blockListRef = useRef(null);
  const [activeBlockId, setActiveBlockId] = useState(null);

  // ---------- layer-row drag ----------
  const [layerDragId, setLayerDragId] = useState(null);
  const [layerDragOverId, setLayerDragOverId] = useState(null);
  const [layerDragOverPos, setLayerDragOverPos] = useState(null);
  const layerListRef = useRef(null);

  // ---------- coord helper ----------
  const getCanvasPoint = (e, canvasEl, frame) => {
    const rect = canvasEl.getBoundingClientRect();
    const totalH = frame.blocks.reduce((s, b) => s + b.height, 0);
    return {
      x: (e.clientX - rect.left) * (frame.canvasWidth / rect.width),
      y: (e.clientY - rect.top) * (totalH / rect.height),
    };
  };

  // ===================================================================
  //  BUBBLE helpers
  // ===================================================================
  const updateBubble = useCallback((layerId, bubbleId, changes) => {
    setBubblesByLayer(prev => ({
      ...prev,
      [layerId]: (prev[layerId] || []).map(b => b.id === bubbleId ? { ...b, ...changes } : b),
    }));
  }, []);

  const deleteBubble = useCallback((layerId, bubbleId) => {
    setBubblesByLayer(prev => ({ ...prev, [layerId]: (prev[layerId] || []).filter(b => b.id !== bubbleId) }));
    setSelectedBubble(null);
  }, []);

  const addBubble = useCallback((layerId, x, y, w, h, type) => {
    const bubble = { id: newId(), type, x, y, w: Math.max(BUBBLE_MIN_W, w), h: Math.max(BUBBLE_MIN_H, h), text: '', tailTip: null };
    setBubblesByLayer(prev => ({ ...prev, [layerId]: [...(prev[layerId] || []), bubble] }));
    return bubble.id;
  }, []);

  // ===================================================================
  //  BUBBLE pointer handlers
  // ===================================================================
  // bubbleHit: existing bubble object or null (clicking empty space)
  const handleBubbleOverlayPointerDown = useCallback((e, frameId, overlayEl, bubbleHit) => {
    if (e.pointerType === 'touch') {
      activeTouchPointersRef.current.set(e.pointerId, { x: e.clientX, y: e.clientY });
      if (activeTouchPointersRef.current.size >= 2) {
        if (!panStateRef.current) {
          const pts = [...activeTouchPointersRef.current.values()];
          panStateRef.current = { lastX: pts.reduce((s,p)=>s+p.x,0)/pts.length, lastY: pts.reduce((s,p)=>s+p.y,0)/pts.length };
        }
        if (activeTouchPointersRef.current.size === 2) {
          twoFingerTapRef.current = {
            active: true,
            startMap: new Map([...activeTouchPointersRef.current.entries()].map(([k,v]) => [k, { x: v.x, y: v.y }])),
            moved: false,
          };
        }
        try { overlayEl?.releasePointerCapture(e.pointerId); } catch(_) {}
        return;
      }
    }
    e.preventDefault();
    const frame = frames.find(f => f.id === frameId);
    if (!frame) return;
    const p = getCanvasPoint(e, overlayEl, frame);
    const activeVLayerId = frame.activeLayerId;
    const layer = frame.layers.find(l => l.id === activeVLayerId);
    if (!layer || layer.type !== 'vector') return;

    // Priority 1: explicit bubbleHit (from SVG element pointer events)
    if (bubbleHit) {
      setSelectedBubble({ frameId, layerId: activeVLayerId, bubbleId: bubbleHit.id });
      // Check tail handle
      if (hitTestTailHandle(bubbleHit, p.x, p.y)) {
        bubbleInterRef.current = { mode: 'tail', frameId, layerId: activeVLayerId, bubbleId: bubbleHit.id, startX: p.x, startY: p.y, origBubble: { ...bubbleHit } };
        try { overlayEl.setPointerCapture(e.pointerId); } catch(_) {}
        return;
      }
      // Check add-tail indicator
      if (!bubbleHit.tailTip) {
        const icx = bubbleHit.x + bubbleHit.w / 2, icy = bubbleHit.y + bubbleHit.h + 22;
        if ((p.x-icx)**2 + (p.y-icy)**2 <= (TAIL_HANDLE_R+5)**2) {
          bubbleInterRef.current = { mode: 'tail', frameId, layerId: activeVLayerId, bubbleId: bubbleHit.id, startX: p.x, startY: p.y, origBubble: { ...bubbleHit } };
          try { overlayEl.setPointerCapture(e.pointerId); } catch(_) {}
          return;
        }
      }
      const hit = hitTestBubble(bubbleHit, p.x, p.y);
      const mode = hit === 'center' ? 'move' : 'resize';
      bubbleInterRef.current = { mode, frameId, layerId: activeVLayerId, bubbleId: bubbleHit.id, startX: p.x, startY: p.y, origBubble: { ...bubbleHit } };
      try { overlayEl.setPointerCapture(e.pointerId); } catch(_) {}
      return;
    }

    // Priority 2: hit-test all bubbles on this layer (canvas overlay clicked)
    const layerBubbles = bubblesByLayer[activeVLayerId] || [];
    for (let i = layerBubbles.length - 1; i >= 0; i--) {
      const bubble = layerBubbles[i];
      if (hitTestTailHandle(bubble, p.x, p.y)) {
        setSelectedBubble({ frameId, layerId: activeVLayerId, bubbleId: bubble.id });
        bubbleInterRef.current = { mode: 'tail', frameId, layerId: activeVLayerId, bubbleId: bubble.id, startX: p.x, startY: p.y, origBubble: { ...bubble } };
        try { overlayEl.setPointerCapture(e.pointerId); } catch(_) {}
        return;
      }
      if (!bubble.tailTip && selectedBubble?.bubbleId === bubble.id) {
        const icx = bubble.x + bubble.w / 2, icy = bubble.y + bubble.h + 22;
        if ((p.x-icx)**2 + (p.y-icy)**2 <= (TAIL_HANDLE_R+5)**2) {
          bubbleInterRef.current = { mode: 'tail', frameId, layerId: activeVLayerId, bubbleId: bubble.id, startX: p.x, startY: p.y, origBubble: { ...bubble } };
          try { overlayEl.setPointerCapture(e.pointerId); } catch(_) {}
          return;
        }
      }
      const hit = hitTestBubble(bubble, p.x, p.y);
      if (hit) {
        setSelectedBubble({ frameId, layerId: activeVLayerId, bubbleId: bubble.id });
        bubbleInterRef.current = { mode: hit === 'center' ? 'move' : 'resize', frameId, layerId: activeVLayerId, bubbleId: bubble.id, startX: p.x, startY: p.y, origBubble: { ...bubble } };
        try { overlayEl.setPointerCapture(e.pointerId); } catch(_) {}
        return;
      }
    }

    // Empty: start creating
    setSelectedBubble(null);
    bubbleInterRef.current = { mode: 'create', frameId, layerId: activeVLayerId, bubbleId: null, startX: p.x, startY: p.y, origBubble: null };
    try { overlayEl.setPointerCapture(e.pointerId); } catch(_) {}
  }, [frames, bubblesByLayer, selectedBubble]);

  const handleBubbleOverlayPointerMove = useCallback((e, frameId, overlayEl) => {
    if (e.pointerType === 'touch') {
      if (activeTouchPointersRef.current.has(e.pointerId))
        activeTouchPointersRef.current.set(e.pointerId, { x: e.clientX, y: e.clientY });
      if (activeTouchPointersRef.current.size >= 2) {
        if (twoFingerTapRef.current.active && !twoFingerTapRef.current.moved) {
          const TAP_THRESHOLD = 15;
          for (const [pid, pos] of activeTouchPointersRef.current.entries()) {
            const start = twoFingerTapRef.current.startMap?.get(pid);
            if (start && (Math.abs(pos.x - start.x) > TAP_THRESHOLD || Math.abs(pos.y - start.y) > TAP_THRESHOLD)) {
              twoFingerTapRef.current.moved = true; break;
            }
          }
        }
        if (panStateRef.current && canvasAreaRef.current) {
          const pts = [...activeTouchPointersRef.current.values()];
          const avgX = pts.reduce((s,p)=>s+p.x,0)/pts.length;
          const avgY = pts.reduce((s,p)=>s+p.y,0)/pts.length;
          canvasAreaRef.current.scrollLeft -= avgX - panStateRef.current.lastX;
          canvasAreaRef.current.scrollTop -= avgY - panStateRef.current.lastY;
          panStateRef.current = { lastX: avgX, lastY: avgY };
        }
        return;
      }
    }
    const inter = bubbleInterRef.current;
    if (!inter.mode) return;
    e.preventDefault();
    const frame = frames.find(f => f.id === frameId);
    if (!frame) return;
    const p = getCanvasPoint(e, overlayEl, frame);
    const { mode, layerId, bubbleId, startX, startY, origBubble } = inter;

    if (mode === 'create') {
      const fref = frameRefs.current[frameId];
      if (!fref) return;
      const oc = fref.getOverlayCanvas(), dpr = fref.getDpr();
      if (!oc) return;
      const ctx = oc.getContext('2d');
      ctx.clearRect(0, 0, oc.width, oc.height);
      ctx.save(); ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      const rx = Math.min(startX, p.x), ry = Math.min(startY, p.y);
      const rw = Math.abs(p.x - startX), rh = Math.abs(p.y - startY);
      ctx.strokeStyle = 'rgba(106,58,213,0.7)'; ctx.lineWidth = 1.5; ctx.setLineDash([5,3]);
      ctx.strokeRect(rx, ry, rw, rh); ctx.setLineDash([]); ctx.restore();
      return;
    }
    if (mode === 'move' && bubbleId) {
      updateBubble(layerId, bubbleId, {
        x: origBubble.x + (p.x - startX), y: origBubble.y + (p.y - startY),
        tailTip: origBubble.tailTip ? { x: origBubble.tailTip.x + (p.x - startX), y: origBubble.tailTip.y + (p.y - startY) } : null,
      });
      return;
    }
    if (mode === 'resize' && bubbleId) {
      const { x, y, w, h } = origBubble;
      const ox = startX < x + w / 2 ? x + w : x;
      const oy = startY < y + h / 2 ? y + h : y;
      updateBubble(layerId, bubbleId, {
        x: Math.min(ox, p.x), y: Math.min(oy, p.y),
        w: Math.max(BUBBLE_MIN_W, Math.abs(p.x - ox)),
        h: Math.max(BUBBLE_MIN_H, Math.abs(p.y - oy)),
      });
      return;
    }
    if (mode === 'tail' && bubbleId) {
      updateBubble(layerId, bubbleId, { tailTip: { x: p.x, y: p.y } });
    }
  }, [frames, updateBubble]);

  const handleBubbleOverlayPointerUp = useCallback((e, frameId, overlayEl) => {
    if (e.pointerType === 'touch') {
      activeTouchPointersRef.current.delete(e.pointerId);
      if (activeTouchPointersRef.current.size === 1 && twoFingerTapRef.current.active && !twoFingerTapRef.current.moved) {
        twoFingerTapRef.current = { active: false, startMap: null, moved: false };
        undoLastStroke();
        panStateRef.current = null;
        return;
      }
      if (activeTouchPointersRef.current.size === 0) twoFingerTapRef.current = { active: false, startMap: null, moved: false };
      if (activeTouchPointersRef.current.size < 2) panStateRef.current = null;
    }
    const inter = bubbleInterRef.current;
    if (inter.mode === 'create') {
      const frame = frames.find(f => f.id === frameId);
      if (frame && overlayEl) {
        const p = getCanvasPoint(e, overlayEl, frame);
        const w = Math.abs(p.x - inter.startX), h = Math.abs(p.y - inter.startY);
        if (w >= BUBBLE_MIN_W && h >= BUBBLE_MIN_H) {
          const bx = Math.min(inter.startX, p.x), by = Math.min(inter.startY, p.y);
          const newBubbleId = addBubble(inter.layerId, bx, by, w, h, activeBubbleType);
          setSelectedBubble({ frameId, layerId: inter.layerId, bubbleId: newBubbleId });
        }
        frameRefs.current[frameId]?.clearOverlay();
      }
    }
    try { overlayEl?.releasePointerCapture(e.pointerId); } catch(_) {}
    bubbleInterRef.current = { mode: null, frameId: null, layerId: null, bubbleId: null, startX: 0, startY: 0, origBubble: null };
  }, [frames, addBubble, activeBubbleType]);

  // ===================================================================
  //  LASSO overlay rendering
  // ===================================================================
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
    ctx.save(); ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.lineCap = 'round'; ctx.lineJoin = 'round';

    if (phase === 'drawing' && lassoPoints.length > 1) {
      ctx.strokeStyle = LASSO_COLOR; ctx.lineWidth = 1.5; ctx.setLineDash([5,3]); ctx.globalAlpha = 0.85;
      ctx.beginPath(); ctx.moveTo(lassoPoints[0].x, lassoPoints[0].y);
      for (let i = 1; i < lassoPoints.length; i++) ctx.lineTo(lassoPoints[i].x, lassoPoints[i].y);
      ctx.stroke(); ctx.setLineDash([]); ctx.globalAlpha = 1;
    }

    if (bbox && ['selected','dragging','resizing','rotating'].includes(phase)) {
      const { cx, cy } = bbox;
      for (const item of selectedItems) {
        const pts = item.framePoints.map(p => applySelectionTransform(p.x, p.y, cx, cy, transform));
        ctx.strokeStyle = hexToRgba(item.stroke.color || '#0F0F0F', item.stroke.opacity);
        ctx.fillStyle   = hexToRgba(item.stroke.color || '#0F0F0F', item.stroke.opacity);
        ctx.lineWidth = item.stroke.size;
        if (pts.length === 1) { ctx.beginPath(); ctx.arc(pts[0].x, pts[0].y, item.stroke.size/2, 0, Math.PI*2); ctx.fill(); }
        else { ctx.beginPath(); ctx.moveTo(pts[0].x, pts[0].y); for (let i=1;i<pts.length;i++) ctx.lineTo(pts[i].x, pts[i].y); ctx.stroke(); }
      }
      const handles = getHandlePositions(bbox, transform);
      const corners = [handles.tl, handles.tr, handles.br, handles.bl];
      ctx.strokeStyle = LASSO_COLOR; ctx.lineWidth = 1.5; ctx.setLineDash([5,3]); ctx.globalAlpha = 0.9;
      ctx.beginPath(); ctx.moveTo(corners[0].x, corners[0].y);
      for (let i=1;i<corners.length;i++) ctx.lineTo(corners[i].x, corners[i].y);
      ctx.closePath(); ctx.stroke(); ctx.setLineDash([]); ctx.globalAlpha = 1;
      ctx.strokeStyle = LASSO_COLOR; ctx.lineWidth = 1; ctx.globalAlpha = 0.5;
      ctx.beginPath(); ctx.moveTo(handles.tc.x, handles.tc.y); ctx.lineTo(handles.rotate.x, handles.rotate.y); ctx.stroke(); ctx.globalAlpha = 1;
      for (const hid of ['tl','tr','br','bl','tc','bc','lc','rc']) {
        const h = handles[hid], hs = HANDLE_SIZE;
        ctx.fillStyle = '#fff'; ctx.strokeStyle = LASSO_COLOR; ctx.lineWidth = 1.5;
        ctx.beginPath(); ctx.rect(h.x-hs/2, h.y-hs/2, hs, hs); ctx.fill(); ctx.stroke();
      }
      const r = handles.rotate;
      ctx.fillStyle = LASSO_COLOR; ctx.strokeStyle = '#fff'; ctx.lineWidth = 1.5;
      ctx.beginPath(); ctx.arc(r.x, r.y, HANDLE_SIZE/2+2, 0, Math.PI*2); ctx.fill(); ctx.stroke();
    }
    ctx.restore();
  };

  // ===================================================================
  //  LASSO: select strokes in polygon
  // ===================================================================
  const selectStrokesInLasso = (frameId) => {
    const lasso = lassoRef.current;
    const frame = frames.find(f => f.id === frameId);
    if (!frame) return;
    const layerId = lasso.layerId;
    const store = ensureLayerStore(frameId, layerId);
    const tops = computeBlockTops(frame.blocks);
    const selectedItems = [], dirtyBlocks = new Set();

    for (const block of frame.blocks) {
      const blockTop = tops[block.id];
      for (const stroke of (store.byBlock[block.id] || [])) {
        if (stroke.hidden) continue;
        const centX = (stroke.bbox.minX + stroke.bbox.maxX) / 2;
        const centY = (stroke.bbox.minY + stroke.bbox.maxY) / 2 + blockTop;
        if (pointInPolygon(centX, centY, lasso.lassoPoints)) {
          selectedItems.push({ stroke, blockId: block.id, layerId, blockTop, framePoints: stroke.points.map(p => ({ x: p.x, y: p.y + blockTop })) });
          stroke.hidden = true; dirtyBlocks.add(block.id);
        }
      }
    }

    if (selectedItems.length === 0) {
      lasso.phase = 'idle'; frameRefs.current[frameId]?.clearOverlay();
      setHasSelection(false); setSelectionPhase('idle'); return;
    }

    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    for (const item of selectedItems) for (const p of item.framePoints) {
      if (p.x < minX) minX = p.x; if (p.y < minY) minY = p.y;
      if (p.x > maxX) maxX = p.x; if (p.y > maxY) maxY = p.y;
    }
    const maxSz = Math.max(...selectedItems.map(i => i.stroke.size / 2));
    minX -= maxSz; minY -= maxSz; maxX += maxSz; maxY += maxSz;

    lasso.selectedItems = selectedItems;
    lasso.bbox = { minX, minY, maxX, maxY, cx: (minX+maxX)/2, cy: (minY+maxY)/2 };
    lasso.transform = { tx:0, ty:0, scaleX:1, scaleY:1, angle:0, flipH:false, flipV:false };
    lasso.phase = 'selected';

    for (const blockId of dirtyBlocks) {
      const block = frame.blocks.find(b => b.id === blockId);
      if (block) rebuildBlockBitmap(frameId, layerId, block, frame.canvasWidth);
    }
    frameRefs.current[frameId]?.redraw();
    setHasSelection(true); setSelectionPhase('selected');
    renderSelectionOverlay(frameId);
  };

  // ===================================================================
  //  LASSO: apply
  // ===================================================================
  const applyLassoSelection = (frameId, frame) => {
    const lasso = lassoRef.current;
    if (!lasso.selectedItems?.length) { cancelLassoSelection(frameId, frame); return; }
    const { bbox, transform, selectedItems } = lasso;
    const { cx, cy } = bbox;
    const tops = computeBlockTops(frame.blocks);
    const dirtyByLayer = {};

    for (const item of selectedItems) {
      const store = ensureLayerStore(frameId, item.layerId);
      const origArr = store.byBlock[item.blockId];
      if (origArr) { const idx = origArr.indexOf(item.stroke); if (idx >= 0) origArr.splice(idx, 1); }
      if (!dirtyByLayer[item.layerId]) dirtyByLayer[item.layerId] = new Set();
      dirtyByLayer[item.layerId].add(item.blockId);

      const newFramePts = item.framePoints.map(p => applySelectionTransform(p.x, p.y, cx, cy, transform));
      const centX = newFramePts.reduce((s,p)=>s+p.x,0)/newFramePts.length;
      const centY = newFramePts.reduce((s,p)=>s+p.y,0)/newFramePts.length;
      const newBlockId = findStrokeBlockId({ points: [{x:centX,y:centY}] }, frame.blocks, tops);
      if (newBlockId == null) continue;
      const newBlockTop = tops[newBlockId];
      const newLocalPts = newFramePts.map(p => ({ x: p.x, y: p.y - newBlockTop }));
      const newStroke = { points: newLocalPts, size: item.stroke.size, opacity: item.stroke.opacity, bbox: computeBbox(newLocalPts), hidden: false };
      if (!store.byBlock[newBlockId]) store.byBlock[newBlockId] = [];
      store.byBlock[newBlockId].push(newStroke);
      store.history.push({ layerId: item.layerId, blockId: newBlockId });
      dirtyByLayer[item.layerId].add(newBlockId);
    }

    for (const [layerId, blockIds] of Object.entries(dirtyByLayer))
      for (const blockId of blockIds) {
        const block = frame.blocks.find(b => b.id === blockId);
        if (block) rebuildBlockBitmap(frameId, layerId, block, frame.canvasWidth);
      }
    frameRefs.current[frameId]?.redraw();
    lasso.phase = 'idle'; lasso.selectedItems = []; lasso.bbox = null; lasso.frameId = null;
    frameRefs.current[frameId]?.clearOverlay();
    setHasSelection(false); setSelectionPhase('idle');
  };

  // ===================================================================
  //  LASSO: cancel
  // ===================================================================
  const cancelLassoSelection = (frameId, frame) => {
    const lasso = lassoRef.current;
    const dirtyByLayer = {};
    for (const item of lasso.selectedItems || []) {
      item.stroke.hidden = false;
      if (!dirtyByLayer[item.layerId]) dirtyByLayer[item.layerId] = new Set();
      dirtyByLayer[item.layerId].add(item.blockId);
    }
    const fr = frame || frames.find(f => f.id === frameId);
    for (const [layerId, blockIds] of Object.entries(dirtyByLayer))
      for (const blockId of blockIds) {
        const block = fr?.blocks.find(b => b.id === blockId);
        if (block) rebuildBlockBitmap(frameId, layerId, block, fr.canvasWidth);
      }
    frameRefs.current[frameId]?.redraw();
    lasso.phase = 'idle'; lasso.selectedItems = []; lasso.bbox = null; lasso.frameId = null;
    frameRefs.current[frameId]?.clearOverlay();
    setHasSelection(false); setSelectionPhase('idle');
  };

  // ===================================================================
  //  LASSO: copy / paste / flip / rotate / delete
  // ===================================================================
  const copySelection = () => {
    const lasso = lassoRef.current;
    if (!lasso.selectedItems?.length) return;
    const { bbox, transform, selectedItems } = lasso;
    const { cx, cy } = bbox;
    clipboardRef.current = selectedItems.map(item => ({
      size: item.stroke.size, opacity: item.stroke.opacity, color: item.stroke.color || '#0F0F0F', layerId: item.layerId,
      framePoints: item.framePoints.map(p => applySelectionTransform(p.x, p.y, cx, cy, transform)),
    }));
    setHasClipboard(true);
  };

  const pasteSelection = () => {
    const cb = clipboardRef.current;
    if (!cb?.length || !selectedFrame) return;
    const activeLayerId = getActiveRasterLayerId(selectedFrame);
    if (!activeLayerId) return;
    const OFFSET = 24;
    const store = ensureLayerStore(selectedFrameId, activeLayerId);
    const tops = computeBlockTops(selectedFrame.blocks);
    const dirty = new Set();
    for (const item of cb) {
      const offsetPts = item.framePoints.map(p => ({ x: p.x + OFFSET, y: p.y + OFFSET }));
      const centX = offsetPts.reduce((s,p)=>s+p.x,0)/offsetPts.length;
      const centY = offsetPts.reduce((s,p)=>s+p.y,0)/offsetPts.length;
      const blockId = findStrokeBlockId({ points: [{x:centX,y:centY}] }, selectedFrame.blocks, tops);
      if (blockId == null) continue;
      const blockTop = tops[blockId];
      const localPts = offsetPts.map(p => ({ x: p.x, y: p.y - blockTop }));
      const newStroke = { points: localPts, size: item.size, opacity: item.opacity, color: item.color || '#0F0F0F', bbox: computeBbox(localPts), hidden: false };
      if (!store.byBlock[blockId]) store.byBlock[blockId] = [];
      store.byBlock[blockId].push(newStroke);
      store.history.push({ layerId: activeLayerId, blockId });
      dirty.add(blockId);
    }
    for (const blockId of dirty) {
      const block = selectedFrame.blocks.find(b => b.id === blockId);
      if (block) rebuildBlockBitmap(selectedFrameId, activeLayerId, block, selectedFrame.canvasWidth);
    }
    frameRefs.current[selectedFrameId]?.redraw();
  };

  const flipSelection = (axis) => {
    const lasso = lassoRef.current;
    if (!['selected','dragging','resizing','rotating'].includes(lasso.phase)) return;
    lasso.transform = axis === 'h' ? { ...lasso.transform, flipH: !lasso.transform.flipH } : { ...lasso.transform, flipV: !lasso.transform.flipV };
    renderSelectionOverlay(lasso.frameId);
  };

  const rotateSelectionDeg = (deg) => {
    const lasso = lassoRef.current;
    if (!['selected','dragging','resizing','rotating'].includes(lasso.phase)) return;
    lasso.transform = { ...lasso.transform, angle: lasso.transform.angle + deg * Math.PI / 180 };
    renderSelectionOverlay(lasso.frameId);
  };

  const deleteSelection = () => {
    const lasso = lassoRef.current;
    if (!lasso.selectedItems?.length) return;
    const frameId = lasso.frameId;
    const frame = frames.find(f => f.id === frameId);
    const dirtyByLayer = {};
    for (const item of lasso.selectedItems) {
      const store = ensureLayerStore(frameId, item.layerId);
      const arr = store.byBlock[item.blockId];
      if (arr) { const idx = arr.indexOf(item.stroke); if (idx >= 0) arr.splice(idx, 1); }
      if (!dirtyByLayer[item.layerId]) dirtyByLayer[item.layerId] = new Set();
      dirtyByLayer[item.layerId].add(item.blockId);
    }
    for (const [layerId, blockIds] of Object.entries(dirtyByLayer))
      for (const blockId of blockIds) {
        const block = frame?.blocks.find(b => b.id === blockId);
        if (block) rebuildBlockBitmap(frameId, layerId, block, frame.canvasWidth);
      }
    frameRefs.current[frameId]?.redraw();
    lasso.phase = 'idle'; lasso.selectedItems = []; lasso.bbox = null; lasso.frameId = null;
    frameRefs.current[frameId]?.clearOverlay();
    setHasSelection(false); setSelectionPhase('idle');
  };

  // ===================================================================
  //  LASSO pointer handlers
  // ===================================================================
  const handleLassoPointerDown = (e, frameId, overlayEl) => {
    if (e.pointerType === 'touch') {
      activeTouchPointersRef.current.set(e.pointerId, { x: e.clientX, y: e.clientY });
      if (activeTouchPointersRef.current.size >= 2) {
        const lasso = lassoRef.current;
        if (lasso.phase === 'drawing') { lasso.phase = 'idle'; frameRefs.current[frameId]?.clearOverlay(); setSelectionPhase('idle'); }
        if (!panStateRef.current) {
          const pts = [...activeTouchPointersRef.current.values()];
          panStateRef.current = { lastX: pts.reduce((s,p)=>s+p.x,0)/pts.length, lastY: pts.reduce((s,p)=>s+p.y,0)/pts.length };
        }
        if (activeTouchPointersRef.current.size === 2) {
          twoFingerTapRef.current = {
            active: true,
            startMap: new Map([...activeTouchPointersRef.current.entries()].map(([k,v]) => [k, { x: v.x, y: v.y }])),
            moved: false,
          };
        }
        try { overlayEl?.releasePointerCapture(e.pointerId); } catch(_) {} return;
      }
    }
    e.preventDefault();
    const frame = frames.find(f => f.id === frameId);
    if (!frame || !overlayEl) return;
    const p = getCanvasPoint(e, overlayEl, frame);
    const lasso = lassoRef.current;
    const activeLayerId = getActiveRasterLayerId(frame);
    if (!activeLayerId) return;

    if (lasso.frameId && lasso.frameId !== frameId && ['selected','dragging','resizing','rotating'].includes(lasso.phase)) {
      const prevFrame = frames.find(f => f.id === lasso.frameId);
      if (prevFrame) applyLassoSelection(lasso.frameId, prevFrame);
    }

    if (lasso.frameId === frameId && ['selected','dragging','resizing','rotating'].includes(lasso.phase)) {
      const handles = getHandlePositions(lasso.bbox, lasso.transform);
      const hitHandle = hitTestHandles(p.x, p.y, handles);
      if (hitHandle === 'rotate') {
        lasso.phase = 'rotating'; lasso.dragStart = p; lasso.origTransform = { ...lasso.transform };
        setSelectionPhase('rotating'); try { overlayEl.setPointerCapture(e.pointerId); } catch(_) {} return;
      }
      if (hitHandle) {
        lasso.phase = 'resizing'; lasso.dragHandle = hitHandle; lasso.dragStart = p; lasso.origTransform = { ...lasso.transform };
        const { cx, cy } = lasso.bbox;
        const cxT = cx + lasso.transform.tx, cyT = cy + lasso.transform.ty;
        lasso.origHandleDist = { x: handles[hitHandle].x - cxT, y: handles[hitHandle].y - cyT };
        setSelectionPhase('resizing'); try { overlayEl.setPointerCapture(e.pointerId); } catch(_) {} return;
      }
      if (pointInPolygon(p.x, p.y, [handles.tl, handles.tr, handles.br, handles.bl])) {
        lasso.phase = 'dragging'; lasso.dragStart = p; lasso.origTransform = { ...lasso.transform };
        setSelectionPhase('dragging'); try { overlayEl.setPointerCapture(e.pointerId); } catch(_) {} return;
      }
      applyLassoSelection(frameId, frame);
    }

    lasso.phase = 'drawing'; lasso.frameId = frameId; lasso.layerId = activeLayerId;
    lasso.lassoPoints = [p]; lasso.selectedItems = []; lasso.bbox = null;
    lasso.transform = { tx:0,ty:0,scaleX:1,scaleY:1,angle:0,flipH:false,flipV:false };
    setSelectionPhase('drawing');
    try { overlayEl.setPointerCapture(e.pointerId); } catch(_) {}
    renderSelectionOverlay(frameId);
  };

  const handleLassoPointerMove = (e, overlayEl) => {
    if (e.pointerType === 'touch') {
      if (activeTouchPointersRef.current.has(e.pointerId))
        activeTouchPointersRef.current.set(e.pointerId, { x: e.clientX, y: e.clientY });
      if (activeTouchPointersRef.current.size >= 2) {
        if (twoFingerTapRef.current.active && !twoFingerTapRef.current.moved) {
          const TAP_THRESHOLD = 15;
          for (const [pid, pos] of activeTouchPointersRef.current.entries()) {
            const start = twoFingerTapRef.current.startMap?.get(pid);
            if (start && (Math.abs(pos.x - start.x) > TAP_THRESHOLD || Math.abs(pos.y - start.y) > TAP_THRESHOLD)) {
              twoFingerTapRef.current.moved = true; break;
            }
          }
        }
        if (panStateRef.current && canvasAreaRef.current) {
          const pts = [...activeTouchPointersRef.current.values()];
          const avgX = pts.reduce((s,p)=>s+p.x,0)/pts.length;
          const avgY = pts.reduce((s,p)=>s+p.y,0)/pts.length;
          canvasAreaRef.current.scrollLeft -= avgX - panStateRef.current.lastX;
          canvasAreaRef.current.scrollTop -= avgY - panStateRef.current.lastY;
          panStateRef.current = { lastX: avgX, lastY: avgY };
        }
        return;
      }
    }
    const lasso = lassoRef.current;
    if (lasso.phase === 'idle' || !overlayEl) return;
    e.preventDefault();
    const frame = frames.find(f => f.id === lasso.frameId);
    if (!frame) return;
    const p = getCanvasPoint(e, overlayEl, frame);

    if (lasso.phase === 'drawing') { lasso.lassoPoints.push(p); renderSelectionOverlay(lasso.frameId); return; }
    if (lasso.phase === 'dragging') {
      lasso.transform = { ...lasso.origTransform, tx: lasso.origTransform.tx+(p.x-lasso.dragStart.x), ty: lasso.origTransform.ty+(p.y-lasso.dragStart.y) };
      renderSelectionOverlay(lasso.frameId); return;
    }
    if (lasso.phase === 'resizing') {
      const { cx, cy } = lasso.bbox;
      const cxT = cx+lasso.origTransform.tx, cyT = cy+lasso.origTransform.ty;
      const hid = lasso.dragHandle, { origHandleDist } = lasso;
      const dx = p.x - cxT, dy = p.y - cyT;
      let newScaleX = lasso.origTransform.scaleX, newScaleY = lasso.origTransform.scaleY;
      if (['tl','tr','bl','br'].includes(hid)) {
        if (Math.abs(origHandleDist.x) > 1) newScaleX = Math.max(0.05, Math.abs(dx)/Math.abs(origHandleDist.x)) * Math.sign(lasso.origTransform.scaleX);
        if (Math.abs(origHandleDist.y) > 1) newScaleY = Math.max(0.05, Math.abs(dy)/Math.abs(origHandleDist.y)) * Math.sign(lasso.origTransform.scaleY);
      } else if (['tc','bc'].includes(hid)) {
        if (Math.abs(origHandleDist.y) > 1) newScaleY = Math.max(0.05, Math.abs(dy)/Math.abs(origHandleDist.y)) * Math.sign(lasso.origTransform.scaleY);
      } else if (['lc','rc'].includes(hid)) {
        if (Math.abs(origHandleDist.x) > 1) newScaleX = Math.max(0.05, Math.abs(dx)/Math.abs(origHandleDist.x)) * Math.sign(lasso.origTransform.scaleX);
      }
      lasso.transform = { ...lasso.origTransform, scaleX: newScaleX, scaleY: newScaleY };
      renderSelectionOverlay(lasso.frameId); return;
    }
    if (lasso.phase === 'rotating') {
      const { cx, cy } = lasso.bbox;
      const cxT = cx+lasso.origTransform.tx, cyT = cy+lasso.origTransform.ty;
      lasso.transform = { ...lasso.origTransform,
        angle: lasso.origTransform.angle + Math.atan2(p.y-cyT,p.x-cxT) - Math.atan2(lasso.dragStart.y-cyT,lasso.dragStart.x-cxT) };
      renderSelectionOverlay(lasso.frameId);
    }
  };

  const handleLassoPointerUp = (e, overlayEl) => {
    if (e.pointerType === 'touch') {
      activeTouchPointersRef.current.delete(e.pointerId);
      if (activeTouchPointersRef.current.size === 1 && twoFingerTapRef.current.active && !twoFingerTapRef.current.moved) {
        twoFingerTapRef.current = { active: false, startMap: null, moved: false };
        undoLastStroke();
        panStateRef.current = null;
        return;
      }
      if (activeTouchPointersRef.current.size === 0) twoFingerTapRef.current = { active: false, startMap: null, moved: false };
      if (activeTouchPointersRef.current.size < 2) panStateRef.current = null;
    }
    const lasso = lassoRef.current;
    if (lasso.phase === 'drawing') {
      try { overlayEl?.releasePointerCapture(e.pointerId); } catch(_) {}
      if (lasso.lassoPoints.length >= 3) selectStrokesInLasso(lasso.frameId);
      else { lasso.phase = 'idle'; frameRefs.current[lasso.frameId]?.clearOverlay(); setSelectionPhase('idle'); }
      return;
    }
    if (['dragging','resizing','rotating'].includes(lasso.phase)) {
      try { overlayEl?.releasePointerCapture(e.pointerId); } catch(_) {}
      lasso.phase = 'selected'; setSelectionPhase('selected');
      renderSelectionOverlay(lasso.frameId);
    }
  };

  // ===================================================================
  //  Tool switch / keyboard
  // ===================================================================
  const switchTool = (tool) => {
    if (tool === activeTool) return;
    if (activeTool === 'lasso') {
      const lasso = lassoRef.current;
      if (lasso.phase !== 'idle' && lasso.frameId) {
        const fr = frames.find(f => f.id === lasso.frameId);
        if (['selected','dragging','resizing','rotating'].includes(lasso.phase)) { if (fr) applyLassoSelection(lasso.frameId, fr); }
        else cancelLassoSelection(lasso.frameId, fr);
      }
    }
    setActiveTool(tool);
  };

  useEffect(() => {
    const onKey = (e) => {
      const tag = document.activeElement.tagName;
      // Ctrl+Z / Cmd+Z → undo last stroke (only when not typing)
      if ((e.ctrlKey || e.metaKey) && e.key === 'z' && !e.shiftKey) {
        if (!['INPUT', 'TEXTAREA'].includes(tag)) {
          e.preventDefault();
          undoLastStroke();
          return;
        }
      }
      const lasso = lassoRef.current;
      if (e.key === 'Escape') {
        if (selectedBubble) { setSelectedBubble(null); return; }
        if (lasso.phase !== 'idle' && lasso.frameId) {
          const fr = frames.find(f => f.id === lasso.frameId);
          if (['selected','dragging','resizing','rotating'].includes(lasso.phase)) applyLassoSelection(lasso.frameId, fr);
          else cancelLassoSelection(lasso.frameId, fr);
        }
      }
      if ((e.key === 'Delete' || e.key === 'Backspace') && selectedBubble
        && !['INPUT','TEXTAREA'].includes(document.activeElement.tagName)) {
        deleteBubble(selectedBubble.layerId, selectedBubble.bubbleId);
      }
    };
    window.addEventListener('keydown', onKey);
    return () => window.removeEventListener('keydown', onKey);
  });

  // ===================================================================
  //  Pen pointer handlers
  // ===================================================================
  const handlePointerDown = (e, frameId, overlayEl) => {
    if (activeTool === 'lasso') { handleLassoPointerDown(e, frameId, overlayEl); return; }
    if (e.pointerType === 'touch') {
      activeTouchPointersRef.current.set(e.pointerId, { x: e.clientX, y: e.clientY });
      if (activeTouchPointersRef.current.size >= 2) {
        if (drawingRef.current) { const cid = drawingRef.current.frameId; drawingRef.current = null; currentStrokeRef.current = null; frameRefs.current[cid]?.redraw(); }
        if (!panStateRef.current) {
          const pts = [...activeTouchPointersRef.current.values()];
          panStateRef.current = { lastX: pts.reduce((s,p)=>s+p.x,0)/pts.length, lastY: pts.reduce((s,p)=>s+p.y,0)/pts.length };
        }
        // Record two-finger gesture start for tap-undo detection (only when exactly 2 fingers)
        if (activeTouchPointersRef.current.size === 2) {
          twoFingerTapRef.current = {
            active: true,
            startMap: new Map([...activeTouchPointersRef.current.entries()].map(([k,v]) => [k, { x: v.x, y: v.y }])),
            moved: false,
          };
        }
        try { overlayEl?.releasePointerCapture(e.pointerId); } catch(_) {} return;
      }
    }
    e.preventDefault();
    const frame = frames.find(f => f.id === frameId);
    if (!frame || !overlayEl) return;
    const activeLayerId = getActiveRasterLayerId(frame);
    if (!activeLayerId) return;
    try { overlayEl.setPointerCapture(e.pointerId); } catch(_) {}
    const p = getCanvasPoint(e, overlayEl, frame);
    drawingRef.current = { frameId, layerId: activeLayerId };
    currentStrokeRef.current = { points: [p], size: penSize, opacity: penOpacity / 100, color: penColor };
    const mc = frameRefs.current[frameId]?.getMainCanvas();
    if (mc) {
      const ctx = mc.getContext('2d');
      ctx.fillStyle = hexToRgba(penColor, penOpacity / 100);
      ctx.beginPath(); ctx.arc(p.x, p.y, penSize/2, 0, Math.PI*2); ctx.fill();
    }
  };

  const handlePointerMove = (e, overlayEl) => {
    if (activeTool === 'lasso') { handleLassoPointerMove(e, overlayEl); return; }
    if (e.pointerType === 'touch') {
      if (activeTouchPointersRef.current.has(e.pointerId))
        activeTouchPointersRef.current.set(e.pointerId, { x: e.clientX, y: e.clientY });
      if (activeTouchPointersRef.current.size >= 2) {
        // Detect if this is a pan (moved) vs a tap (stationary)
        if (twoFingerTapRef.current.active && !twoFingerTapRef.current.moved) {
          const TAP_THRESHOLD = 15;
          for (const [pid, pos] of activeTouchPointersRef.current.entries()) {
            const start = twoFingerTapRef.current.startMap?.get(pid);
            if (start && (Math.abs(pos.x - start.x) > TAP_THRESHOLD || Math.abs(pos.y - start.y) > TAP_THRESHOLD)) {
              twoFingerTapRef.current.moved = true; break;
            }
          }
        }
        if (panStateRef.current && canvasAreaRef.current) {
          const pts = [...activeTouchPointersRef.current.values()];
          const avgX = pts.reduce((s,p)=>s+p.x,0)/pts.length;
          const avgY = pts.reduce((s,p)=>s+p.y,0)/pts.length;
          canvasAreaRef.current.scrollLeft -= avgX - panStateRef.current.lastX;
          canvasAreaRef.current.scrollTop -= avgY - panStateRef.current.lastY;
          panStateRef.current = { lastX: avgX, lastY: avgY };
        }
        return;
      }
    }
    if (!drawingRef.current || !overlayEl) return;
    e.preventDefault();
    const frame = frames.find(f => f.id === drawingRef.current.frameId);
    if (!frame) return;
    const p = getCanvasPoint(e, overlayEl, frame);
    const s = currentStrokeRef.current;
    const last = s.points[s.points.length - 1];
    s.points.push(p);
    const mc = frameRefs.current[drawingRef.current.frameId]?.getMainCanvas();
    if (mc) {
      const ctx = mc.getContext('2d');
      ctx.strokeStyle = hexToRgba(s.color || '#0F0F0F', s.opacity); ctx.lineWidth = s.size;
      ctx.beginPath(); ctx.moveTo(last.x, last.y); ctx.lineTo(p.x, p.y); ctx.stroke();
    }
  };

  const handlePointerUp = (e, overlayEl) => {
    if (activeTool === 'lasso') { handleLassoPointerUp(e, overlayEl); return; }
    if (e.pointerType === 'touch') {
      activeTouchPointersRef.current.delete(e.pointerId);
      // Two-finger tap (no significant movement) → undo last stroke
      if (activeTouchPointersRef.current.size === 1 && twoFingerTapRef.current.active && !twoFingerTapRef.current.moved) {
        twoFingerTapRef.current = { active: false, startMap: null, moved: false };
        undoLastStroke();
        if (activeTouchPointersRef.current.size < 2) panStateRef.current = null;
        return;
      }
      if (activeTouchPointersRef.current.size === 0) twoFingerTapRef.current = { active: false, startMap: null, moved: false };
      if (activeTouchPointersRef.current.size < 2) panStateRef.current = null;
    }
    const drawState = drawingRef.current, liveStroke = currentStrokeRef.current;
    drawingRef.current = null; currentStrokeRef.current = null;
    if (!drawState || !liveStroke || liveStroke.points.length === 0) return;
    const frame = frames.find(f => f.id === drawState.frameId);
    if (!frame) return;
    const tops = computeBlockTops(frame.blocks);
    const ownerId = findStrokeBlockId(liveStroke, frame.blocks, tops);
    if (ownerId == null) { frameRefs.current[drawState.frameId]?.redraw(); return; }
    const ownerBlock = frame.blocks.find(b => b.id === ownerId);
    const ownerTop = tops[ownerId];
    const localPoints = liveStroke.points.map(p => ({ x: p.x, y: p.y - ownerTop }));
    const simplified = rdpSimplify(localPoints, RDP_EPSILON);
    const stored = { points: simplified, size: liveStroke.size, opacity: liveStroke.opacity, bbox: computeBbox(simplified), hidden: false };
    const store = ensureLayerStore(drawState.frameId, drawState.layerId);
    if (!store.byBlock[ownerId]) store.byBlock[ownerId] = [];
    store.byBlock[ownerId].push(stored);
    store.history.push({ layerId: drawState.layerId, blockId: ownerId });
    const entry = ensureBlockBitmap(drawState.frameId, drawState.layerId, ownerBlock, frame.canvasWidth, stored.bbox.maxY);
    renderStrokeToCtx(entry.ctx, stored, BITMAP_Y_PADDING);
  };

  // ===================================================================
  //  Frame management
  // ===================================================================
  const addFrame = () => {
    const tmpl = selectedFrame || frames[frames.length - 1];
    const f = makeStarterFrame(`Frame ${frames.length + 1}`, { canvasWidth: tmpl?.canvasWidth ?? 690, sideMargin: tmpl?.sideMargin ?? 38 });
    for (const l of f.layers) ensureLayerStore(f.id, l.id);
    setFrames(arr => [...arr, f]);
    setSelectedFrameId(f.id);
  };

  const countStrokesInFrame = frameId => {
    const fStore = strokesByFrameRef.current[frameId];
    if (!fStore) return 0;
    return Object.values(fStore).reduce((n, ls) => n + Object.values(ls.byBlock).reduce((m, arr) => m + arr.length, 0), 0);
  };

  const removeFrame = id => {
    if (frames.length <= 1) return;
    const lasso = lassoRef.current;
    if (lasso.frameId === id && lasso.phase !== 'idle') cancelLassoSelection(id, frames.find(f => f.id === id));
    const target = frames.find(f => f.id === id);
    const sc = countStrokesInFrame(id);
    if (!window.confirm(sc > 0 ? `"${target?.name}" 삭제 시 ${sc}개 stroke도 함께 사라집니다. 계속하시겠습니까?` : `"${target?.name}" 을(를) 삭제합니다. 계속하시겠습니까?`)) return;
    delete strokesByFrameRef.current[id];
    delete frameRefs.current[id];
    delete getLayerBitmapRef.current[id];
    setFrames(arr => {
      const next = arr.filter(f => f.id !== id);
      if (id === selectedFrameId) {
        const idx = arr.findIndex(f => f.id === id);
        const newSel = next[Math.max(0, Math.min(idx, next.length - 1))];
        if (newSel) setSelectedFrameId(newSel.id);
      }
      return next;
    });
  };

  const renameFrame = (id, name) => setFrames(arr => arr.map(f => f.id === id ? { ...f, name } : f));

  const updateFrameDim = (id, key, value) => {
    if (key === 'canvasWidth') {
      const frame = frames.find(f => f.id === id);
      if (frame && frame.canvasWidth !== value) {
        const fStore = strokesByFrameRef.current[id] || {};
        for (const layer of frame.layers)
          if (layer.type === 'raster')
            for (const b of frame.blocks) rebuildBlockBitmap(id, layer.id, b, value);
      }
    }
    setFrames(arr => arr.map(f => f.id === id ? { ...f, [key]: value } : f));
  };

  // ===================================================================
  //  Layer management
  // ===================================================================
  const addRasterLayer = () => {
    if (!selectedFrame) return;
    const nl = makeLayer(`Layer ${selectedFrame.layers.length + 1}`, 'raster');
    ensureLayerStore(selectedFrameId, nl.id);
    setFrames(arr => arr.map(f => f.id === selectedFrameId ? { ...f, layers: [...f.layers, nl], activeLayerId: nl.id } : f));
  };

  const addVectorLayer = () => {
    if (!selectedFrame) return;
    const vCount = selectedFrame.layers.filter(l => l.type === 'vector').length;
    const nl = makeLayer(`Bubble ${vCount + 1}`, 'vector');
    setFrames(arr => arr.map(f => f.id === selectedFrameId ? { ...f, layers: [...f.layers, nl], activeLayerId: nl.id } : f));
  };

  const setActiveLayer = layerId => {
    if (!selectedFrame) return;
    if (selectedBubble && selectedBubble.layerId !== layerId) setSelectedBubble(null);
    setFrames(arr => arr.map(f => f.id === selectedFrameId ? { ...f, activeLayerId: layerId } : f));
  };

  const toggleLayerVisible = layerId => {
    setFrames(arr => arr.map(f => f.id === selectedFrameId
      ? { ...f, layers: f.layers.map(l => l.id === layerId ? { ...l, visible: !l.visible } : l) }
      : f));
    setTimeout(() => frameRefs.current[selectedFrameId]?.redraw(), 0);
  };

  const setLayerOpacity = (layerId, opacity) => {
    setFrames(arr => arr.map(f => f.id === selectedFrameId
      ? { ...f, layers: f.layers.map(l => l.id === layerId ? { ...l, opacity } : l) }
      : f));
    setTimeout(() => frameRefs.current[selectedFrameId]?.redraw(), 0);
  };

  const renameLayer = (layerId, name) => {
    setFrames(arr => arr.map(f => f.id === selectedFrameId
      ? { ...f, layers: f.layers.map(l => l.id === layerId ? { ...l, name } : l) }
      : f));
  };

  const duplicateLayer = layerId => {
    if (!selectedFrame) return;
    const srcLayer = selectedFrame.layers.find(l => l.id === layerId);
    if (!srcLayer) return;
    const nl = { ...srcLayer, id: newId(), name: srcLayer.name + ' copy' };
    if (srcLayer.type === 'raster') {
      ensureLayerStore(selectedFrameId, nl.id);
      const srcStore = ensureLayerStore(selectedFrameId, layerId);
      const dstStore = ensureLayerStore(selectedFrameId, nl.id);
      for (const blockId in srcStore.byBlock)
        dstStore.byBlock[blockId] = srcStore.byBlock[blockId].map(s => ({ ...s, points: [...s.points] }));
      for (const block of selectedFrame.blocks)
        rebuildBlockBitmap(selectedFrameId, nl.id, block, selectedFrame.canvasWidth);
    } else {
      const srcBubbles = bubblesByLayer[layerId] || [];
      setBubblesByLayer(prev => ({ ...prev, [nl.id]: srcBubbles.map(b => ({ ...b, id: newId(), tailTip: b.tailTip ? { ...b.tailTip } : null })) }));
    }
    const idx = selectedFrame.layers.findIndex(l => l.id === layerId);
    const newLayers = [...selectedFrame.layers];
    newLayers.splice(idx + 1, 0, nl);
    setFrames(arr => arr.map(f => f.id === selectedFrameId ? { ...f, layers: newLayers, activeLayerId: nl.id } : f));
    setTimeout(() => frameRefs.current[selectedFrameId]?.redraw(), 0);
  };

  const mergeLayerDown = layerId => {
    if (!selectedFrame) return;
    const idx = selectedFrame.layers.findIndex(l => l.id === layerId);
    if (idx <= 0) return;
    const srcLayer = selectedFrame.layers[idx];
    const dstLayer = selectedFrame.layers[idx - 1];
    if (srcLayer.type !== 'raster' || dstLayer.type !== 'raster') { alert('두 래스터 레이어 사이에서만 병합이 가능합니다.'); return; }
    const srcStore = ensureLayerStore(selectedFrameId, layerId);
    const dstStore = ensureLayerStore(selectedFrameId, dstLayer.id);
    for (const blockId in srcStore.byBlock) {
      if (!dstStore.byBlock[blockId]) dstStore.byBlock[blockId] = [];
      for (const s of srcStore.byBlock[blockId]) {
        dstStore.byBlock[blockId].push({ ...s });
        dstStore.history.push({ layerId: dstLayer.id, blockId });
      }
    }
    for (const block of selectedFrame.blocks)
      rebuildBlockBitmap(selectedFrameId, dstLayer.id, block, selectedFrame.canvasWidth);
    delete strokesByFrameRef.current[selectedFrameId][layerId];
    const newLayers = selectedFrame.layers.filter(l => l.id !== layerId);
    setFrames(arr => arr.map(f => f.id === selectedFrameId ? { ...f, layers: newLayers, activeLayerId: dstLayer.id } : f));
    setTimeout(() => frameRefs.current[selectedFrameId]?.redraw(), 0);
  };

  const deleteLayer = layerId => {
    if (!selectedFrame) return;
    if (selectedFrame.layers.length <= 1) { alert('레이어가 최소 1개는 있어야 합니다.'); return; }
    if (!window.confirm('이 레이어를 삭제합니다. 계속하시겠습니까?')) return;
    setBubblesByLayer(prev => { const next = { ...prev }; delete next[layerId]; return next; });
    if (strokesByFrameRef.current[selectedFrameId]) delete strokesByFrameRef.current[selectedFrameId][layerId];
    if (selectedBubble?.layerId === layerId) setSelectedBubble(null);
    const newLayers = selectedFrame.layers.filter(l => l.id !== layerId);
    const newActive = selectedFrame.activeLayerId === layerId ? (newLayers[newLayers.length - 1]?.id ?? null) : selectedFrame.activeLayerId;
    setFrames(arr => arr.map(f => f.id === selectedFrameId ? { ...f, layers: newLayers, activeLayerId: newActive } : f));
    setTimeout(() => frameRefs.current[selectedFrameId]?.redraw(), 0);
  };

  // ===================================================================
  //  Block management
  // ===================================================================
  const addCut = height => {
    if (!selectedFrame) return;
    const sm = selectedFrame.sideMargin;
    setFrames(arr => arr.map(f => f.id === selectedFrameId
      ? { ...f, blocks: [...f.blocks, { id: newId(), type: 'cut', height, marginLeft: sm, marginRight: sm }] }
      : f));
  };

  const addGap = height => {
    if (!selectedFrame) return;
    setFrames(arr => arr.map(f => f.id === selectedFrameId
      ? { ...f, blocks: [...f.blocks, { id: newId(), type: 'gap', height }] }
      : f));
  };

  const removeBlock = blockId => {
    if (!selectedFrame) return;
    const oldTops = computeBlockTops(selectedFrame.blocks);
    const removedBlock = selectedFrame.blocks.find(b => b.id === blockId);
    const removedTop = oldTops[blockId] ?? 0;
    const newBlocks = selectedFrame.blocks.filter(b => b.id !== blockId);
    if (removedBlock && newBlocks.length > 0) {
      const newTops = computeBlockTops(newBlocks);
      const fStore = strokesByFrameRef.current[selectedFrameId] || {};
      for (const [layerId, store] of Object.entries(fStore)) {
        const removedStrokes = store.byBlock[blockId] || [];
        const dirty = new Set();
        for (const s of removedStrokes) {
          const fcp = s.points.map(p => ({ x: p.x, y: p.y + removedTop }));
          const newOwner = findStrokeBlockId({ ...s, points: fcp }, newBlocks, newTops);
          if (newOwner == null) continue;
          const newOwnerTop = newTops[newOwner];
          const reLocal = fcp.map(p => ({ x: p.x, y: p.y - newOwnerTop }));
          const reStored = { points: reLocal, size: s.size, opacity: s.opacity, bbox: computeBbox(reLocal), hidden: false };
          if (!store.byBlock[newOwner]) store.byBlock[newOwner] = [];
          store.byBlock[newOwner].push(reStored);
          dirty.add(newOwner);
        }
        for (const bid of dirty) {
          const blk = newBlocks.find(b => b.id === bid);
          if (blk) rebuildBlockBitmap(selectedFrameId, layerId, blk, selectedFrame.canvasWidth);
        }
        delete store.byBlock[blockId]; delete store.bitmaps[blockId];
        store.history = store.history.filter(h => h.blockId !== blockId);
      }
    }
    setFrames(arr => arr.map(f => f.id === selectedFrameId ? { ...f, blocks: newBlocks } : f));
  };

  const updateBlockHeight = (blockId, value) => {
    if (!selectedFrame) return;
    const h = Math.max(50, Math.min(5000, parseInt(value, 10) || 200));
    const target = selectedFrame.blocks.find(b => b.id === blockId);
    if (!target || target.height === h) return;

    // 변경된 block 아래에 있는 block들의 top이 밀림 → 그 block에 종속된 말풍선도 함께 이동
    const oldTops = computeBlockTops(selectedFrame.blocks);
    const newBlocks = selectedFrame.blocks.map(b => b.id === blockId ? { ...b, height: h } : b);
    const newTops = computeBlockTops(newBlocks);
    const selectedLayerIds = new Set(selectedFrame.layers.map(l => String(l.id)));
    setBubblesByLayer(prev => {
      const updated = { ...prev };
      for (const layerId of Object.keys(updated)) {
        if (!selectedLayerIds.has(layerId)) continue;
        updated[layerId] = (updated[layerId] || []).map(bubble => {
          const ownerBlockId = findBubbleBlockId(bubble, selectedFrame.blocks, oldTops);
          if (ownerBlockId === null) return bubble;
          const dy = (newTops[ownerBlockId] ?? 0) - (oldTops[ownerBlockId] ?? 0);
          if (dy === 0) return bubble;
          return {
            ...bubble,
            y: bubble.y + dy,
            tailTip: bubble.tailTip ? { x: bubble.tailTip.x, y: bubble.tailTip.y + dy } : null,
          };
        });
      }
      return updated;
    });

    setFrames(arr => arr.map(f => f.id === selectedFrameId
      ? { ...f, blocks: f.blocks.map(b => b.id === blockId ? { ...b, height: h } : b) }
      : f));
  };

  const updateBlockMargin = (blockId, side, value) => {
    if (!selectedFrame) return;
    const v = Math.max(0, Math.min(500, parseInt(value, 10)));
    if (!Number.isFinite(v)) return;
    setFrames(arr => arr.map(f => f.id === selectedFrameId
      ? { ...f, blocks: f.blocks.map(b => b.id === blockId ? { ...b, [side]: v } : b) }
      : f));
  };

  // ===================================================================
  //  Viewport-center block tracking
  // ===================================================================
  useEffect(() => {
    const area = canvasAreaRef.current;
    if (!area) return;
    const computeActive = () => {
      if (!selectedFrame) { setActiveBlockId(null); return; }
      const areaRect = area.getBoundingClientRect();
      const centerY = areaRect.top + areaRect.height / 2;
      const rangeHalf = 200;
      const frameEl = area.querySelector(`[data-frame-id="${selectedFrameId}"]`);
      if (!frameEl) { setActiveBlockId(null); return; }
      const stageEl = frameEl.querySelector('.conti-frame-stage');
      if (!stageEl) { setActiveBlockId(null); return; }
      const stageRect = stageEl.getBoundingClientRect();
      let y = 0, bestId = null, bestOverlap = -1;
      for (const b of selectedFrame.blocks) {
        const blockTop = stageRect.top + y, blockBottom = blockTop + b.height;
        const overlap = Math.max(0, Math.min(blockBottom, centerY + rangeHalf) - Math.max(blockTop, centerY - rangeHalf));
        if (overlap > bestOverlap) { bestOverlap = overlap; bestId = b.id; }
        y += b.height;
      }
      setActiveBlockId(bestId);
    };
    area.addEventListener('scroll', computeActive, { passive: true });
    window.addEventListener('resize', computeActive);
    computeActive();
    return () => { area.removeEventListener('scroll', computeActive); window.removeEventListener('resize', computeActive); };
  }, [selectedFrameId, selectedFrame]);

  // ===================================================================
  //  Block-row drag
  // ===================================================================
  const findRowAt = clientY => {
    const list = blockListRef.current;
    if (!list) return { id: null, pos: null };
    const rows = list.querySelectorAll('[data-block-id]');
    for (const el of rows) {
      const r = el.getBoundingClientRect();
      if (clientY >= r.top && clientY <= r.bottom)
        return { id: parseInt(el.getAttribute('data-block-id'), 10), pos: clientY < r.top + r.height / 2 ? 'above' : 'below' };
    }
    if (rows.length > 0) {
      const first = rows[0].getBoundingClientRect(), last = rows[rows.length-1].getBoundingClientRect();
      if (clientY < first.top) return { id: parseInt(rows[0].getAttribute('data-block-id'), 10), pos: 'above' };
      if (clientY > last.bottom) return { id: parseInt(rows[rows.length-1].getAttribute('data-block-id'), 10), pos: 'below' };
    }
    return { id: null, pos: null };
  };

  const handleHandlePointerDown = (e, id) => {
    e.preventDefault(); e.stopPropagation();
    try { e.currentTarget.setPointerCapture(e.pointerId); } catch(_) {}
    setDragId(id); setDragOverId(null); setDragOverPos(null);
  };

  const handleHandlePointerMove = e => {
    if (dragId === null) return;
    e.preventDefault();
    const { id, pos } = findRowAt(e.clientY);
    setDragOverId(id); setDragOverPos(pos);
  };

  const handleHandlePointerUp = e => {
    if (dragId === null || !selectedFrame) { setDragId(null); setDragOverId(null); setDragOverPos(null); return; }
    try { e.currentTarget.releasePointerCapture(e.pointerId); } catch(_) {}
    if (dragOverId !== null && dragOverId !== dragId) {
      const fromIdx = selectedFrame.blocks.findIndex(x => x.id === dragId);
      const overIdx = selectedFrame.blocks.findIndex(x => x.id === dragOverId);
      if (fromIdx >= 0 && overIdx >= 0) {
        const next = [...selectedFrame.blocks];
        const [removed] = next.splice(fromIdx, 1);
        let insertIdx = next.findIndex(x => x.id === dragOverId);
        if (dragOverPos === 'below') insertIdx++;
        next.splice(insertIdx, 0, removed);
        const sameOrder = next.length === selectedFrame.blocks.length && next.every((b,i) => b.id === selectedFrame.blocks[i].id);
        if (!sameOrder) {
          // 말풍선을 해당 block과 함께 이동 (stroke 종속 범위와 동일한 기준)
          const oldTops = computeBlockTops(selectedFrame.blocks);
          const newTops = computeBlockTops(next);
          const selectedLayerIds = new Set(selectedFrame.layers.map(l => String(l.id)));
          setBubblesByLayer(prev => {
            const updated = { ...prev };
            for (const layerId of Object.keys(updated)) {
              if (!selectedLayerIds.has(layerId)) continue;
              updated[layerId] = (updated[layerId] || []).map(bubble => {
                const ownerBlockId = findBubbleBlockId(bubble, selectedFrame.blocks, oldTops);
                if (ownerBlockId === null) return bubble;
                const dy = (newTops[ownerBlockId] ?? 0) - (oldTops[ownerBlockId] ?? 0);
                if (dy === 0) return bubble;
                return {
                  ...bubble,
                  y: bubble.y + dy,
                  tailTip: bubble.tailTip ? { x: bubble.tailTip.x, y: bubble.tailTip.y + dy } : null,
                };
              });
            }
            return updated;
          });
          setFrames(arr => arr.map(f => f.id === selectedFrameId ? { ...f, blocks: next } : f));
        }
      }
    }
    setDragId(null); setDragOverId(null); setDragOverPos(null);
  };

  // ===================================================================
  //  Layer-row drag
  // ===================================================================
  const findLayerRowAt = clientY => {
    const list = layerListRef.current;
    if (!list) return { id: null, pos: null };
    const rows = list.querySelectorAll('[data-layer-id]');
    for (const el of rows) {
      const r = el.getBoundingClientRect();
      if (clientY >= r.top && clientY <= r.bottom)
        return { id: parseInt(el.getAttribute('data-layer-id'), 10), pos: clientY < r.top + r.height / 2 ? 'above' : 'below' };
    }
    if (rows.length > 0) {
      const first = rows[0].getBoundingClientRect(), last = rows[rows.length-1].getBoundingClientRect();
      if (clientY < first.top) return { id: parseInt(rows[0].getAttribute('data-layer-id'), 10), pos: 'above' };
      if (clientY > last.bottom) return { id: parseInt(rows[rows.length-1].getAttribute('data-layer-id'), 10), pos: 'below' };
    }
    return { id: null, pos: null };
  };

  const handleLayerHandlePointerDown = (e, id) => {
    e.preventDefault(); e.stopPropagation();
    try { e.currentTarget.setPointerCapture(e.pointerId); } catch(_) {}
    setLayerDragId(id); setLayerDragOverId(null); setLayerDragOverPos(null);
  };

  const handleLayerHandlePointerMove = e => {
    if (layerDragId === null) return;
    e.preventDefault();
    const { id, pos } = findLayerRowAt(e.clientY);
    setLayerDragOverId(id); setLayerDragOverPos(pos);
  };

  const handleLayerHandlePointerUp = e => {
    if (layerDragId === null || !selectedFrame) {
      setLayerDragId(null); setLayerDragOverId(null); setLayerDragOverPos(null); return;
    }
    try { e.currentTarget.releasePointerCapture(e.pointerId); } catch(_) {}
    // layers are rendered reversed in UI, so drag positions are also reversed
    if (layerDragOverId !== null && layerDragOverId !== layerDragId) {
      const layers = selectedFrame.layers; // bottom→top (index 0 = bottom)
      const fromIdx = layers.findIndex(l => l.id === layerDragId);
      const overIdx = layers.findIndex(l => l.id === layerDragOverId);
      if (fromIdx >= 0 && overIdx >= 0) {
        const next = [...layers];
        const [removed] = next.splice(fromIdx, 1);
        // UI is reversed: 'above' in UI = higher index in array, 'below' = lower index
        let insertIdx = next.findIndex(l => l.id === layerDragOverId);
        // In reversed display: dragging above means higher in stack (higher array index)
        if (layerDragOverPos === 'above') insertIdx += 1;
        next.splice(insertIdx, 0, removed);
        setFrames(arr => arr.map(f => f.id === selectedFrameId ? { ...f, layers: next } : f));
      }
    }
    setLayerDragId(null); setLayerDragOverId(null); setLayerDragOverPos(null);
    setTimeout(() => frameRefs.current[selectedFrameId]?.redraw(), 0);
  };
  const undo = () => {
    if (!selectedFrame || lassoRef.current.phase !== 'idle') return;
    const activeLayerId = getActiveRasterLayerId(selectedFrame);
    if (!activeLayerId) return;
    const store = ensureLayerStore(selectedFrameId, activeLayerId);
    if (!store.history.length) return;
    const last = store.history.pop();
    const list = store.byBlock[last.blockId];
    if (list?.length) list.pop();
    const block = selectedFrame.blocks.find(b => b.id === last.blockId);
    if (block) rebuildBlockBitmap(selectedFrameId, activeLayerId, block, selectedFrame.canvasWidth);
    frameRefs.current[selectedFrameId]?.redraw();
  };

  const clearAll = () => {
    if (!selectedFrame) return;
    if (lassoRef.current.phase !== 'idle' && lassoRef.current.frameId === selectedFrameId)
      cancelLassoSelection(selectedFrameId, selectedFrame);
    if (!window.confirm(`"${selectedFrame.name}"의 모든 드로잉을 지웁니다. 계속하시겠습니까?`)) return;
    const fStore = strokesByFrameRef.current[selectedFrameId] || {};
    for (const ls of Object.values(fStore)) { ls.byBlock = {}; ls.bitmaps = {}; ls.history = []; }
    frameRefs.current[selectedFrameId]?.redraw();
  };

  // ---------- derived ----------
  const previewSize = Math.max(2, Math.min(34, penSize));
  const selectedTotalHeight = selectedFrame?.blocks.reduce((s,b) => s+b.height, 0) ?? 0;
  const selectedCutCount = selectedFrame?.blocks.filter(b => b.type === 'cut').length ?? 0;

  const selectedBlockLayout = useMemo(() => {
    if (!selectedFrame) return [];
    let cutCounter = 0, gapCounter = 0;
    return selectedFrame.blocks.map(b => {
      const item = { ...b };
      if (b.type === 'cut') { cutCounter++; item.num = cutCounter; }
      else { gapCounter++; item.num = gapCounter; }
      return item;
    });
  }, [selectedFrame]);

  const selectedBubbleData = selectedBubble
    ? (bubblesByLayer[selectedBubble.layerId] || []).find(b => b.id === selectedBubble.bubbleId) || null
    : null;

  // ===================================================================
  //  RENDER
  // ===================================================================
  return (
    <div className="conti-root">
      <style>{STYLES}</style>

      <header className="conti-topbar">
        <div className="conti-brand">
          <div className="conti-brand-mark" />
          <div>
            <div className="conti-brand-name">콘티 프로그램</div>
            <div className="conti-brand-version">conti.v10</div>
          </div>
        </div>

        {/* Tool selector (raster only) */}
        {activeLayerType === 'raster' && (
          <div className="conti-tool">
            <button className={`conti-icon-btn ${activeTool === 'pen' ? 'active' : ''}`} onClick={() => switchTool('pen')}>✏ pen</button>
            <button className={`conti-icon-btn ${activeTool === 'lasso' ? 'active' : ''}`} onClick={() => switchTool('lasso')}>⬡ lasso</button>
          </div>
        )}
        <div className="conti-tool-sep" />

        {/* Pen color picker — lasso 툴 영역과 size 슬라이더 사이 */}
        {activeLayerType === 'raster' && activeTool === 'pen' && (
          <div className="conti-tool">
            <span className="conti-tool-label">color</span>
            <div className="conti-color-picker">
              {PEN_COLORS.map(c => (
                <button
                  key={c.id}
                  className={`conti-color-btn ${penColor === c.hex ? 'active' : ''}`}
                  style={{ background: c.hex }}
                  title={c.label}
                  onClick={() => setPenColor(c.hex)}
                />
              ))}
            </div>
          </div>
        )}

        {/* Pen options */}
        {activeLayerType === 'raster' && activeTool === 'pen' && (
          <>
            <div className="conti-tool">
              <span className="conti-tool-label">size</span>
              <input type="range" min="0" max="100" step="0.5" value={sizeToSlider(penSize)}
                onChange={e => setPenSize(Math.round(sliderToSize(parseFloat(e.target.value)) * 10) / 10)} />
              <input className="conti-num" type="number" min={PEN_MIN} max={PEN_MAX} step="0.1" value={penSize}
                onChange={e => { const v = parseFloat(e.target.value); if (Number.isFinite(v)) setPenSize(Math.max(PEN_MIN, Math.min(PEN_MAX, v))); }} />
              <span className="conti-tool-unit">px</span>
            </div>
            <div className="conti-tool">
              <span className="conti-tool-label">opacity</span>
              <input type="range" min="0" max="100" step="1" value={penOpacity}
                onChange={e => setPenOpacity(parseInt(e.target.value, 10))} />
              <input className="conti-num" type="number" min="0" max="100" step="1" value={penOpacity}
                onChange={e => { const v = parseInt(e.target.value, 10); if (Number.isFinite(v)) setPenOpacity(Math.max(0, Math.min(100, v))); }} />
              <span className="conti-tool-unit">%</span>
            </div>
            <div className="conti-pen-preview">
              <div className="conti-pen-dot" style={{ width: `${previewSize}px`, height: `${previewSize}px`, opacity: penOpacity / 100, background: penColor }} />
            </div>
          </>
        )}

        {/* Bubble type selector (vector layer active) */}
        {activeLayerType === 'vector' && (
          <div className="conti-bubble-bar">
            <span className="conti-bubble-label">bubble</span>
            {BUBBLE_TYPES.map(t => (
              <button key={t} className={`conti-bubble-type-btn ${activeBubbleType === t ? 'active' : ''}`}
                onClick={() => setActiveBubbleType(t)}>
                {BUBBLE_TYPE_LABELS[t]}
              </button>
            ))}
          </div>
        )}

        {/* Lasso action bar */}
        {activeLayerType === 'raster' && activeTool === 'lasso' && hasSelection && (
          <div className="conti-sel-bar">
            <span className="conti-sel-label">선택됨</span>
            <button className="conti-icon-btn" onClick={copySelection}>⎘ copy</button>
            <button className="conti-icon-btn" onClick={pasteSelection} disabled={!hasClipboard}>⎗ paste</button>
            <div className="conti-tool-sep" />
            <button className="conti-icon-btn" onClick={() => flipSelection('h')}>↔ flip H</button>
            <button className="conti-icon-btn" onClick={() => flipSelection('v')}>↕ flip V</button>
            <div className="conti-tool-sep" />
            <button className="conti-icon-btn" onClick={() => rotateSelectionDeg(-90)}>↺ 90°</button>
            <button className="conti-icon-btn" onClick={() => rotateSelectionDeg(90)}>↻ 90°</button>
            <div className="conti-tool-sep" />
            <button className="conti-icon-btn" onClick={() => {
              const lasso = lassoRef.current;
              if (lasso.frameId) { const fr = frames.find(f => f.id === lasso.frameId); applyLassoSelection(lasso.frameId, fr); }
            }}>✓ apply</button>
            <button className="conti-icon-btn danger" onClick={deleteSelection}>✕ del</button>
          </div>
        )}
        {activeLayerType === 'raster' && activeTool === 'lasso' && !hasSelection && hasClipboard && (
          <button className="conti-icon-btn" onClick={pasteSelection}>⎗ paste</button>
        )}

        <div style={{ flex: 1 }} />

        <div className="conti-actions">
          {activeLayerType === 'raster' && (
            <button className="conti-icon-btn" onClick={undo}
              disabled={!selectedFrame || lassoRef.current.phase !== 'idle'}>↶ undo</button>
          )}
          <button className="conti-icon-btn danger" onClick={clearAll} disabled={!selectedFrame}>clear all</button>
        </div>
      </header>

      <div className="conti-main">
        {/* LEFT SIDEBAR */}
        <aside className="conti-sidebar">
          <div className="conti-section">
            <h3>frames <span className="count mono">{frames.length}</span></h3>
            {frames.map(f => (
              <div key={f.id} className={`conti-frame-row ${f.id === selectedFrameId ? 'active' : ''}`}
                onClick={() => selectAndScrollToFrame(f.id)}>
                <input value={f.name} onChange={e => renameFrame(f.id, e.target.value)} onClick={e => e.stopPropagation()} />
                <button className="del" onClick={e => { e.stopPropagation(); removeFrame(f.id); }}
                  disabled={frames.length <= 1} title="삭제">×</button>
              </div>
            ))}
            <button className="conti-add-btn" onClick={addFrame}>+ new frame</button>
          </div>

          {selectedFrame && (
            <div className="conti-section">
              <h3>가로 system</h3>
              <div className="conti-config-row">
                <label>canvas</label>
                <input type="number" min="200" max="2000" step="2" value={selectedFrame.canvasWidth}
                  onChange={e => { const v = parseInt(e.target.value, 10); if (Number.isFinite(v)) updateFrameDim(selectedFrameId, 'canvasWidth', Math.max(200, Math.min(2000, v))); }} />
              </div>
              <div className="conti-config-row">
                <label>side margin</label>
                <input type="number" min="0" max="500" step="2" value={selectedFrame.sideMargin}
                  onChange={e => { const v = parseInt(e.target.value, 10); if (Number.isFinite(v)) updateFrameDim(selectedFrameId, 'sideMargin', Math.max(0, Math.min(500, v))); }} />
              </div>
              <div className="conti-config-row">
                <label>cut width</label>
                <span className="conti-config-readonly">{Math.max(50, selectedFrame.canvasWidth - 2 * selectedFrame.sideMargin)}px</span>
              </div>
            </div>
          )}

          <div className="conti-section">
            <h3>cut <span className="count mono">+ height</span></h3>
            <div className="conti-preset-grid">
              {DEFAULT_VERTICAL_SIZES.map(h => (
                <button key={h} className="conti-preset" onClick={() => addCut(h)} disabled={!selectedFrame}>
                  <span className="conti-preset-num">{h}</span>
                  <span className="conti-preset-sub">+ cut</span>
                </button>
              ))}
            </div>
          </div>

          <div className="conti-section">
            <h3>gap <span className="count mono">200 × n</span></h3>
            <div className="conti-preset-grid">
              {DEFAULT_GAP_SIZES.map(h => (
                <button key={h} className="conti-preset" onClick={() => addGap(h)} disabled={!selectedFrame}>
                  <span className="conti-preset-num">{h}</span>
                  <span className="conti-preset-sub">+ gap</span>
                </button>
              ))}
            </div>
          </div>

          {activeLayerType === 'raster' && activeTool === 'lasso' && (
            <div className="conti-section">
              <h3>lasso tips</h3>
              <div style={{ fontSize: 11, color: 'var(--muted)', fontFamily: 'Pretendard, sans-serif', lineHeight: 1.6 }}>
                <div style={{ marginBottom: 4 }}><strong style={{ color: 'var(--ink)' }}>그리기</strong> 영역을 자유롭게 드로잉</div>
                <div style={{ marginBottom: 4 }}><strong style={{ color: 'var(--ink)' }}>이동</strong> 선택 안쪽 드래그</div>
                <div style={{ marginBottom: 4 }}><strong style={{ color: 'var(--ink)' }}>크기</strong> □ 핸들 드래그</div>
                <div style={{ marginBottom: 4 }}><strong style={{ color: 'var(--ink)' }}>회전</strong> ● 핸들 드래그</div>
                <div style={{ marginBottom: 4 }}><strong style={{ color: 'var(--ink)' }}>적용</strong> 밖 클릭 or Apply</div>
                <div><strong style={{ color: 'var(--ink)' }}>취소</strong> Esc</div>
              </div>
            </div>
          )}
          {activeLayerType === 'vector' && (
            <div className="conti-section">
              <h3>bubble tips</h3>
              <div style={{ fontSize: 11, color: 'var(--muted)', fontFamily: 'Pretendard, sans-serif', lineHeight: 1.6 }}>
                <div style={{ marginBottom: 4 }}><strong style={{ color: 'var(--ink)' }}>생성</strong> 빈 공간 드래그</div>
                <div style={{ marginBottom: 4 }}><strong style={{ color: 'var(--ink)' }}>이동</strong> 중앙 70% 드래그</div>
                <div style={{ marginBottom: 4 }}><strong style={{ color: 'var(--ink)' }}>크기</strong> 가장자리 30% 드래그</div>
                <div style={{ marginBottom: 4 }}><strong style={{ color: 'var(--ink)' }}>꼬리</strong> ● 핸들 드래그</div>
                <div><strong style={{ color: 'var(--ink)' }}>삭제</strong> 선택 후 Delete</div>
              </div>
            </div>
          )}

          {/* 타이포 시스템 설정 */}
          <div className="conti-section">
            <h3>타이포 system</h3>
            <div className="typo-system-list">
              {typoPresets.map((p, i) => (
                <div key={p.id} className="typo-system-row">
                  <span className="typo-system-index mono">{i + 1}</span>
                  <input
                    className="typo-system-name"
                    value={p.name}
                    onChange={e => setTypoPresets(prev => prev.map(x => x.id === p.id ? { ...x, name: e.target.value } : x))}
                  />
                  <div className="typo-system-size-wrap">
                    <input
                      className="typo-system-size"
                      type="number" min="6" max="200" step="1"
                      value={p.size}
                      onChange={e => {
                        const v = Math.max(6, Math.min(200, parseInt(e.target.value, 10) || 14));
                        setTypoPresets(prev => prev.map(x => x.id === p.id ? { ...x, size: v } : x));
                      }}
                    />
                    <span className="typo-system-pt">pt</span>
                  </div>
                  <select
                    className="typo-system-weight"
                    value={p.weight}
                    onChange={e => setTypoPresets(prev => prev.map(x => x.id === p.id ? { ...x, weight: parseInt(e.target.value, 10) } : x))}
                  >
                    <option value={400}>400</option>
                    <option value={500}>500</option>
                    <option value={600}>600</option>
                    <option value={700}>700</option>
                    <option value={800}>800</option>
                    <option value={900}>900</option>
                  </select>
                </div>
              ))}
            </div>
          </div>
        </aside>

        {/* CANVAS */}
        <div className="conti-canvas-area" ref={canvasAreaRef}>
          <div className="conti-canvas-inner">
            {frames.map(f => (
              <FrameView
                key={f.id}
                ref={el => { if (el) frameRefs.current[f.id] = el; else delete frameRefs.current[f.id]; }}
                frame={f}
                isSelected={f.id === selectedFrameId}
                showDimensions={f.id === selectedFrameId}
                activeTool={activeTool}
                selectionPhase={selectionPhase}
                getLayerBitmap={getLayerBitmapRef.current[f.id] || (() => null)}
                bubblesByLayer={bubblesByLayer}
                selectedBubble={selectedBubble}
                activeLayerType={f.id === selectedFrameId ? activeLayerType : 'raster'}
                typoPresets={typoPresets}
                onSelect={setSelectedFrameId}
                onPointerDown={handlePointerDown}
                onPointerMove={handlePointerMove}
                onPointerUp={handlePointerUp}
                onBubbleOverlayPointerDown={handleBubbleOverlayPointerDown}
                onBubbleOverlayPointerMove={handleBubbleOverlayPointerMove}
                onBubbleOverlayPointerUp={handleBubbleOverlayPointerUp}
              />
            ))}
          </div>

          {selectedFrame && (
            <div className="conti-status">
              <span className={`dot ${activeLayerType === 'vector' ? 'vector' : activeTool === 'lasso' ? 'lasso' : ''}`} />
              <span>{selectedFrame.name}</span>
              <span>·</span>
              <span>{activeLayerType === 'vector' ? `🗨 ${activeLayer?.name}` : activeTool === 'lasso' ? (hasSelection ? '🟥 selected' : 'lasso') : 'pen'}</span>
              <span>·</span>
              <span>w {selectedFrame.canvasWidth}px</span>
              <span>·</span>
              <span>h {selectedTotalHeight}px</span>
              <span>·</span>
              <span>cuts {selectedCutCount}</span>
            </div>
          )}
        </div>

        {/* RIGHT SIDEBAR */}
        <aside className="conti-sidebar right">
          {/* BUBBLE EDITOR */}
          {selectedBubbleData && (
            <div className="conti-section">
              <h3>말풍선 편집</h3>
              <div className="bubble-editor">
                <div className="bubble-editor-label">
                  {BUBBLE_TYPE_LABELS[selectedBubbleData.type]} · {Math.round(selectedBubbleData.w)}×{Math.round(selectedBubbleData.h)}px
                </div>

                {/* 타이포 프리셋 선택 */}
                <div className="typo-preset-label">텍스트 크기</div>
                <div className="typo-preset-grid">
                  {typoPresets.map(p => {
                    const isActive = selectedBubbleData.typoPresetId === p.id;
                    return (
                      <button
                        key={p.id}
                        className={`typo-preset-btn ${isActive ? 'active' : ''}`}
                        onClick={() => updateBubble(selectedBubble.layerId, selectedBubble.bubbleId, {
                          typoPresetId: isActive ? null : p.id,
                        })}
                        title={`${p.name} · ${p.size}pt`}
                      >
                        <span className="typo-preset-name">{p.name}</span>
                        <span className="typo-preset-size">{p.size}pt</span>
                      </button>
                    );
                  })}
                </div>

                <textarea className="bubble-text-input" placeholder="대사를 입력하세요..."
                  value={selectedBubbleData.text}
                  onChange={e => updateBubble(selectedBubble.layerId, selectedBubble.bubbleId, { text: e.target.value })} />
                <button className="bubble-del-btn"
                  onClick={() => deleteBubble(selectedBubble.layerId, selectedBubble.bubbleId)}>
                  ✕ 말풍선 삭제
                </button>
              </div>
            </div>
          )}

          {/* BLOCKS */}
          <div className="conti-section">
            <h3>blocks <span className="count mono">{selectedFrame?.blocks.length ?? 0}</span></h3>
            {!selectedFrame || selectedFrame.blocks.length === 0 ? (
              <div className="conti-empty">
                {!selectedFrame ? '선택된 frame이 없습니다' : <>왼쪽 프리셋에서<br />cut / gap을 추가하세요</>}
              </div>
            ) : (
              <div ref={blockListRef}>
                {selectedBlockLayout.map(b => {
                  const showAbove = dragOverId === b.id && dragOverPos === 'above' && dragId !== b.id;
                  const showBelow = dragOverId === b.id && dragOverPos === 'below' && dragId !== b.id;
                  const isCut = b.type === 'cut';
                  return (
                    <div key={b.id} data-block-id={b.id}>
                      {showAbove && <div style={{ position:'relative',height:3,background:'var(--accent)',borderRadius:2,margin:'0 0 2px 0' }} />}
                      <div className={`conti-block-row${isCut ? ' has-margin' : ''} ${dragId === b.id ? 'dragging' : ''} ${b.id === activeBlockId ? 'viewport-active' : ''}`}>
                        <button className="conti-drag-handle"
                          onPointerDown={e => handleHandlePointerDown(e, b.id)}
                          onPointerMove={handleHandlePointerMove}
                          onPointerUp={handleHandlePointerUp}
                          onPointerCancel={handleHandlePointerUp}>
                          <svg width="10" height="16" viewBox="0 0 10 16" fill="currentColor">
                            <circle cx="3" cy="3" r="1.2"/><circle cx="7" cy="3" r="1.2"/>
                            <circle cx="3" cy="8" r="1.2"/><circle cx="7" cy="8" r="1.2"/>
                            <circle cx="3" cy="13" r="1.2"/><circle cx="7" cy="13" r="1.2"/>
                          </svg>
                        </button>
                        <span className={`conti-block-tag ${b.type}`}>
                          {b.type === 'cut' ? `c${String(b.num).padStart(2,'0')}` : 'gap'}
                        </span>
                        <input type="number" min="50" max="5000" step="50" value={b.height}
                          onChange={e => updateBlockHeight(b.id, e.target.value)} />
                        <span className="conti-tool-unit mono">px</span>
                        <button className="del" onClick={() => removeBlock(b.id)} title="삭제">×</button>
                      </div>
                      {isCut && (
                        <div className={`conti-block-margin-row${b.id === activeBlockId ? ' viewport-active' : ''}`}>
                          <span className="conti-margin-label">L</span>
                          <input type="number" min="0" max="500" step="2"
                            value={b.marginLeft ?? selectedFrame.sideMargin}
                            onChange={e => updateBlockMargin(b.id, 'marginLeft', e.target.value)} />
                          <div className="conti-margin-sep" />
                          <input type="number" min="0" max="500" step="2"
                            value={b.marginRight ?? selectedFrame.sideMargin}
                            onChange={e => updateBlockMargin(b.id, 'marginRight', e.target.value)} />
                          <span className="conti-margin-label">R</span>
                        </div>
                      )}
                      {showBelow && <div style={{ position:'relative',height:3,background:'var(--accent)',borderRadius:2,margin:'2px 0 0 0' }} />}
                    </div>
                  );
                })}
              </div>
            )}
          </div>

          {/* LAYERS — Blocks 아래에 위치 */}
          <div className="conti-section">
            <h3>layers <span className="count mono">{selectedFrame?.layers.length ?? 0}</span></h3>
            {selectedFrame && (
              <>
                <div className="layer-add-row">
                  <button className="layer-add-btn" onClick={addRasterLayer}>+ raster</button>
                  <button className="layer-add-btn vector" onClick={addVectorLayer}>+ vector</button>
                </div>
                {/* 레이어는 위→아래 순서로 표시 (array 역순) */}
                <div ref={layerListRef}
                  onPointerMove={handleLayerHandlePointerMove}
                  onPointerUp={handleLayerHandlePointerUp}
                  onPointerCancel={handleLayerHandlePointerUp}
                >
                  {[...selectedFrame.layers].reverse().map((layer, revIdx) => {
                    const idx = selectedFrame.layers.length - 1 - revIdx;
                    const belowLayer = idx > 0 ? selectedFrame.layers[idx - 1] : null;
                    const canMergeDown = !!belowLayer && layer.type === 'raster' && belowLayer.type === 'raster';
                    const showAbove = layerDragOverId === layer.id && layerDragOverPos === 'above' && layerDragId !== layer.id;
                    const showBelow = layerDragOverId === layer.id && layerDragOverPos === 'below' && layerDragId !== layer.id;
                    return (
                      <div key={layer.id} data-layer-id={layer.id}>
                        {showAbove && <div className="layer-drop-indicator" />}
                        <LayerRow
                          layer={layer}
                          isActive={layer.id === selectedFrame.activeLayerId}
                          canMergeDown={canMergeDown}
                          isDragging={layerDragId === layer.id}
                          onActivate={() => setActiveLayer(layer.id)}
                          onToggleVisible={() => toggleLayerVisible(layer.id)}
                          onOpacityChange={op => setLayerOpacity(layer.id, op)}
                          onRename={name => renameLayer(layer.id, name)}
                          onDuplicate={() => duplicateLayer(layer.id)}
                          onMergeDown={() => mergeLayerDown(layer.id)}
                          onDelete={() => deleteLayer(layer.id)}
                          onDragHandlePointerDown={e => {
                            handleLayerHandlePointerDown(e, layer.id);
                          }}
                        />
                        {showBelow && <div className="layer-drop-indicator" />}
                      </div>
                    );
                  })}
                </div>
              </>
            )}
          </div>
        </aside>
      </div>
    </div>
  );
}
