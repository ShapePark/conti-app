import React, {
  useState, useRef, useLayoutEffect, useMemo, useCallback,
  useEffect, forwardRef, useImperativeHandle,
} from 'react';

// ---------- ids ----------
let _id = 0;
const newId = () => ++_id;
// 저장된 프로젝트를 불러올 때 ID 충돌을 막기 위해, 기존 데이터의 max id 보다 한 칸 위로 _id 카운터를 끌어올린다.
const bumpIdTo = (n) => { if (Number.isFinite(n) && n > _id) _id = n; };

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

// ===================================================================
//  NUMBER INPUT WITH DRAFT — controlled input that allows intermediate
//  typing states (e.g. "3" while typing "300") without clamping mid-input.
//  onCommit(stringValue) is called onBlur or on Enter key.
// ===================================================================
const NumberInputWithDraft = ({ value, min, max, step, onCommit, className, style }) => {
  const [draft, setDraft] = useState(String(value));
  const focusedRef = useRef(false);

  // Sync from parent only when not focused (e.g. stepper buttons changed value externally)
  useEffect(() => {
    if (!focusedRef.current) setDraft(String(value));
  }, [value]);

  const commit = (raw) => {
    onCommit(raw);
    // After commit, reflect the parent's clamped value on next render via useEffect
  };

  return (
    <input
      type="number"
      min={min} max={max} step={step}
      className={className}
      style={style}
      value={draft}
      onChange={e => setDraft(e.target.value)}
      onFocus={() => { focusedRef.current = true; }}
      onBlur={e => { focusedRef.current = false; commit(e.target.value); }}
      onKeyDown={e => { if (e.key === 'Enter') { e.currentTarget.blur(); } }}
    />
  );
};

// ===================================================================
//  PROJECT STORAGE — IndexedDB primary, localStorage fallback
//  (iPad Safari, desktop browsers, WKWebView App Store apps 모두 호환)
// ===================================================================
// ---------- gradient (per-block) ----------
// gradient = {
//   start: { x: 0..1, y: 0..1 },   // normalized within the block (cut area for cuts, full width for gaps)
//   end:   { x: 0..1, y: 0..1 },
//   stops: [{ offset: 0..1, value: 0..255 }, ...]   // value = grayscale brightness (255 = #FFFFFF, 0 = #000000)
// }
const GRADIENT_HANDLE_SIZE = 14;
const GRADIENT_HANDLE_HIT = 18;
const GRADIENT_LINE_COLOR = '#3b8efe';

const makeDefaultGradient = () => ({
  start: { x: 0.5, y: 0 },
  end:   { x: 0.5, y: 1 },
  stops: [
    { id: newId(), offset: 0, value: 217 }, // #D9D9D9
    { id: newId(), offset: 1, value: 71 },  // #474747
  ],
});

const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));
const clamp01 = (v) => clamp(v, 0, 1);
const clampGray = (v) => clamp(Math.round(v), 0, 255);

const grayToHex = (v) => {
  const n = clampGray(v);
  const h = n.toString(16).padStart(2, '0').toUpperCase();
  return `${h}${h}${h}`;
};

const grayToRgbStr = (v) => {
  const n = clampGray(v);
  return `rgb(${n},${n},${n})`;
};

const hexToGray = (input) => {
  if (input == null) return null;
  let s = String(input).replace('#', '').trim();
  if (s.length === 3) s = s.split('').map(c => c + c).join('');
  if (!/^[0-9a-fA-F]{6}$/.test(s)) return null;
  const r = parseInt(s.slice(0, 2), 16);
  const g = parseInt(s.slice(2, 4), 16);
  const b = parseInt(s.slice(4, 6), 16);
  return Math.round((r + g + b) / 3);
};

// CSS linear-gradient string. Uses pixel-accurate projection so handles match the painted gradient
// even when start/end don't span the full box (Figma-style behavior).
const gradientToCss = (g, width, height) => {
  if (!g || !Array.isArray(g.stops) || g.stops.length === 0) return null;
  if (g.stops.length === 1) return grayToRgbStr(g.stops[0].value);
  const sx = g.start.x * width, sy = g.start.y * height;
  const ex = g.end.x   * width, ey = g.end.y   * height;
  const dx = ex - sx, dy = ey - sy;
  const len = Math.hypot(dx, dy);
  if (len < 1e-6) return grayToRgbStr(g.stops[0].value);

  // CSS angle: measured from "up" (0deg = to-top) clockwise.
  const cssAngleRad = Math.atan2(dy, dx) + Math.PI / 2;
  const cssAngleDeg = ((cssAngleRad * 180 / Math.PI) % 360 + 360) % 360;

  // CSS spans the gradient line through the box center, length L:
  const sinA = Math.sin(cssAngleRad), cosA = Math.cos(cssAngleRad);
  const L = Math.abs(width * sinA) + Math.abs(height * cosA);
  if (L < 1e-6) return grayToRgbStr(g.stops[0].value);

  // Project user start/end onto the gradient direction relative to center.
  const cx = width / 2, cy = height / 2;
  const ux = dx / len, uy = dy / len;
  const tStart = (sx - cx) * ux + (sy - cy) * uy;
  const tEnd   = (ex - cx) * ux + (ey - cy) * uy;
  const toPct = (t) => ((t + L / 2) / L) * 100;

  const sorted = [...g.stops].sort((a, b) => a.offset - b.offset);
  const stopStrs = sorted.map(s => {
    const t = tStart + clamp01(s.offset) * (tEnd - tStart);
    const pct = toPct(t);
    return `${grayToRgbStr(s.value)} ${pct.toFixed(3)}%`;
  });
  return `linear-gradient(${cssAngleDeg.toFixed(3)}deg, ${stopStrs.join(', ')})`;
};

// Paint a gradient onto a 2D canvas context (used for PSD export).
const paintGradientToCtx = (ctx, g, x, y, width, height) => {
  if (!g || !Array.isArray(g.stops) || g.stops.length === 0) return;
  if (g.stops.length === 1) {
    ctx.fillStyle = grayToRgbStr(g.stops[0].value);
    ctx.fillRect(x, y, width, height);
    return;
  }
  const sx = x + g.start.x * width, sy = y + g.start.y * height;
  const ex = x + g.end.x   * width, ey = y + g.end.y   * height;
  const dx = ex - sx, dy = ey - sy;
  if (Math.hypot(dx, dy) < 1e-6) {
    ctx.fillStyle = grayToRgbStr(g.stops[0].value);
    ctx.fillRect(x, y, width, height);
    return;
  }
  const lg = ctx.createLinearGradient(sx, sy, ex, ey);
  const sorted = [...g.stops].sort((a, b) => a.offset - b.offset);
  for (const s of sorted) lg.addColorStop(clamp01(s.offset), grayToRgbStr(s.value));
  ctx.fillStyle = lg;
  ctx.fillRect(x, y, width, height);
};

const SCHEMA_VERSION = 1;
const APP_VERSION = 'conti.v28';
const DB_NAME = 'conti_program_db';
const DB_STORE = 'projects';
const AUTOSAVE_ID = '__autosave__';
const LS_FALLBACK_PREFIX = 'conti_program_proj_';
const LS_AUTOSAVE_KEY = 'conti_program_autosave';

// IndexedDB 사용 가능 여부 (Safari Private 모드 등에서는 막혀있을 수 있음)
let _idbSupported = null;
const idbSupported = () => {
  if (_idbSupported !== null) return _idbSupported;
  try { _idbSupported = typeof indexedDB !== 'undefined' && indexedDB !== null; }
  catch (_) { _idbSupported = false; }
  return _idbSupported;
};

const openDB = () => new Promise((resolve, reject) => {
  if (!idbSupported()) { reject(new Error('IndexedDB unavailable')); return; }
  const req = indexedDB.open(DB_NAME, 1);
  req.onupgradeneeded = (e) => {
    const db = e.target.result;
    if (!db.objectStoreNames.contains(DB_STORE)) {
      const store = db.createObjectStore(DB_STORE, { keyPath: 'id' });
      store.createIndex('savedAt', 'savedAt', { unique: false });
    }
  };
  req.onsuccess = () => resolve(req.result);
  req.onerror = () => reject(req.error || new Error('IndexedDB open failed'));
  req.onblocked = () => reject(new Error('IndexedDB blocked'));
});

const idbTx = async (mode) => {
  const db = await openDB();
  const tx = db.transaction(DB_STORE, mode);
  return { db, tx, store: tx.objectStore(DB_STORE) };
};

const idbReq = (req) => new Promise((resolve, reject) => {
  req.onsuccess = () => resolve(req.result);
  req.onerror = () => reject(req.error || new Error('IDB request failed'));
});

// localStorage fallback helpers
const lsListKeys = () => {
  const out = [];
  try {
    for (let i = 0; i < localStorage.length; i++) {
      const k = localStorage.key(i);
      if (k && k.startsWith(LS_FALLBACK_PREFIX)) out.push(k);
    }
  } catch (_) {}
  return out;
};

const ProjectStorage = {
  // 모든 프로젝트 메타데이터 목록 (autosave 제외)
  async listProjects() {
    if (idbSupported()) {
      try {
        const { db, store } = await idbTx('readonly');
        const all = await idbReq(store.getAll());
        db.close();
        return all
          .filter(r => r.id !== AUTOSAVE_ID)
          .map(r => ({ id: r.id, name: r.name, savedAt: r.savedAt, meta: r.meta || {} }))
          .sort((a, b) => (b.savedAt || 0) - (a.savedAt || 0));
      } catch (e) {
        // fall through to localStorage
      }
    }
    const out = [];
    for (const k of lsListKeys()) {
      try {
        const raw = localStorage.getItem(k);
        if (!raw) continue;
        const r = JSON.parse(raw);
        out.push({ id: r.id, name: r.name, savedAt: r.savedAt, meta: r.meta || {} });
      } catch (_) {}
    }
    return out.sort((a, b) => (b.savedAt || 0) - (a.savedAt || 0));
  },

  async getProject(id) {
    if (idbSupported()) {
      try {
        const { db, store } = await idbTx('readonly');
        const rec = await idbReq(store.get(id));
        db.close();
        if (rec) return rec;
      } catch (e) {}
    }
    try {
      const raw = localStorage.getItem(LS_FALLBACK_PREFIX + id);
      if (raw) return JSON.parse(raw);
    } catch (_) {}
    return null;
  },

  async saveProject(record) {
    // record: { id, name, savedAt, meta, payload }
    if (idbSupported()) {
      try {
        const { db, tx, store } = await idbTx('readwrite');
        await idbReq(store.put(record));
        await new Promise((res, rej) => { tx.oncomplete = res; tx.onerror = () => rej(tx.error); });
        db.close();
        return { ok: true, backend: 'idb' };
      } catch (e) {
        // fall through
      }
    }
    try {
      localStorage.setItem(LS_FALLBACK_PREFIX + record.id, JSON.stringify(record));
      return { ok: true, backend: 'localStorage' };
    } catch (e) {
      return { ok: false, error: e?.message || 'storage failed' };
    }
  },

  async deleteProject(id) {
    if (idbSupported()) {
      try {
        const { db, tx, store } = await idbTx('readwrite');
        await idbReq(store.delete(id));
        await new Promise((res, rej) => { tx.oncomplete = res; tx.onerror = () => rej(tx.error); });
        db.close();
      } catch (_) {}
    }
    try { localStorage.removeItem(LS_FALLBACK_PREFIX + id); } catch (_) {}
    return { ok: true };
  },

  async getAutosave() {
    if (idbSupported()) {
      try {
        const { db, store } = await idbTx('readonly');
        const rec = await idbReq(store.get(AUTOSAVE_ID));
        db.close();
        if (rec) return rec;
      } catch (_) {}
    }
    try {
      const raw = localStorage.getItem(LS_AUTOSAVE_KEY);
      if (raw) return JSON.parse(raw);
    } catch (_) {}
    return null;
  },

  async setAutosave(record) {
    const rec = { ...record, id: AUTOSAVE_ID };
    if (idbSupported()) {
      try {
        const { db, tx, store } = await idbTx('readwrite');
        await idbReq(store.put(rec));
        await new Promise((res, rej) => { tx.oncomplete = res; tx.onerror = () => rej(tx.error); });
        db.close();
        return { ok: true, backend: 'idb' };
      } catch (_) {}
    }
    try {
      localStorage.setItem(LS_AUTOSAVE_KEY, JSON.stringify(rec));
      return { ok: true, backend: 'localStorage' };
    } catch (e) {
      return { ok: false, error: e?.message || 'storage failed' };
    }
  },

  async clearAutosave() {
    if (idbSupported()) {
      try {
        const { db, tx, store } = await idbTx('readwrite');
        await idbReq(store.delete(AUTOSAVE_ID));
        await new Promise((res, rej) => { tx.oncomplete = res; tx.onerror = () => rej(tx.error); });
        db.close();
      } catch (_) {}
    }
    try { localStorage.removeItem(LS_AUTOSAVE_KEY); } catch (_) {}
    return { ok: true };
  },

  // 대략적인 사용 용량 (KB)
  async approximateSize() {
    if (idbSupported() && navigator.storage?.estimate) {
      try {
        const est = await navigator.storage.estimate();
        return { used: est.usage ?? 0, quota: est.quota ?? 0 };
      } catch (_) {}
    }
    // localStorage fallback - rough estimate
    let used = 0;
    try {
      for (const k of lsListKeys()) used += (localStorage.getItem(k) || '').length;
      const auto = localStorage.getItem(LS_AUTOSAVE_KEY);
      if (auto) used += auto.length;
    } catch (_) {}
    return { used: used * 2, quota: 5 * 1024 * 1024 }; // UTF-16 approx
  },
};

// 페이로드 검증 — 잘못된 데이터로 앱이 깨지지 않게 한다
const validatePayload = (data) => {
  if (!data || typeof data !== 'object') return { ok: false, error: '데이터 형식이 잘못되었습니다' };
  if (!Array.isArray(data.frames) || data.frames.length === 0) return { ok: false, error: 'frames 데이터가 없습니다' };
  for (const f of data.frames) {
    if (typeof f.id !== 'number') return { ok: false, error: 'frame id 가 잘못되었습니다' };
    if (!Array.isArray(f.blocks) || !Array.isArray(f.layers)) return { ok: false, error: 'frame 구조가 잘못되었습니다' };
  }
  return { ok: true };
};

// 전체 데이터에서 가장 큰 numeric id 를 찾는다 (loaded 후 _id 카운터를 끌어올리기 위해)
const findMaxIdInPayload = (data) => {
  let max = 0;
  const seen = (n) => { if (typeof n === 'number' && Number.isFinite(n) && n > max) max = n; };
  if (data?.frames) {
    for (const f of data.frames) {
      seen(f.id);
      if (Array.isArray(f.blocks)) {
        for (const b of f.blocks) {
          seen(b.id);
          if (b?.gradient && Array.isArray(b.gradient.stops)) {
            for (const s of b.gradient.stops) seen(s?.id);
          }
        }
      }
      if (Array.isArray(f.layers)) for (const l of f.layers) seen(l.id);
    }
  }
  if (data?.bubblesByLayer) {
    for (const arr of Object.values(data.bubblesByLayer)) {
      if (Array.isArray(arr)) for (const b of arr) seen(b.id);
    }
  }
  if (data?.typoPresets) for (const p of data.typoPresets) seen(p.id);
  return max;
};

// 다운로드 / 업로드 헬퍼 (.conti.json 파일)
const triggerDownload = (filename, jsonString) => {
  try {
    const blob = new Blob([jsonString], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url; a.download = filename; a.style.display = 'none';
    document.body.appendChild(a); a.click();
    setTimeout(() => { document.body.removeChild(a); URL.revokeObjectURL(url); }, 100);
    return true;
  } catch (_) { return false; }
};

const readFileAsText = (file) => new Promise((resolve, reject) => {
  const r = new FileReader();
  r.onload = () => resolve(r.result);
  r.onerror = () => reject(r.error || new Error('파일 읽기 실패'));
  r.readAsText(file);
});

const formatRelativeTime = (ts) => {
  if (!ts) return '';
  const diff = Date.now() - ts;
  if (diff < 5_000) return '방금 전';
  if (diff < 60_000) return `${Math.floor(diff / 1000)}초 전`;
  if (diff < 3_600_000) return `${Math.floor(diff / 60_000)}분 전`;
  if (diff < 86_400_000) return `${Math.floor(diff / 3_600_000)}시간 전`;
  const d = new Date(ts);
  return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')} ${String(d.getHours()).padStart(2, '0')}:${String(d.getMinutes()).padStart(2, '0')}`;
};

const formatBytes = (n) => {
  if (n < 1024) return `${n} B`;
  if (n < 1024 * 1024) return `${(n / 1024).toFixed(1)} KB`;
  return `${(n / 1024 / 1024).toFixed(2)} MB`;
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

// ===================================================================
//  PSD EXPORT (.clip 대신 클립스튜디오 호환 PSD/PSB로 내보내기)
//
//  왜 .clip 이 아니라 PSD 인가:
//   .clip 는 Celsys 의 비공개 컨테이너로, 내부적으로
//     CSFCHUNK → CHNKHead → CHNKExta… → CHNKSQLi (SQLite) → CHNKFoot
//   구조이며, 실제 픽셀 데이터는 SQLite 안의 Offscreen.BlockData 컬럼에
//   Celsys 자체 블록 압축 포맷으로 들어간다. 공개 스펙이 없어
//   브라우저(JS)에서 쓸 수 있는 .clip writer 라이브러리가 존재하지 않는다.
//
//   PSD 는 CSP 가 공식적으로 지원하는 1급 교환 포맷이고
//   File → Open → .psd 하면 레이어/이름/투명도/가시성이 그대로 보존된다.
//   (CSP 가 PSD 를 export 할 때도 말풍선/텍스트는 어차피 래스터화되므로
//    이번 워크플로우(콘티 러프 → CSP 본작업)에서 손실은 사실상 없다.)
//
//  높이가 30,000px 를 넘으면 자동으로 PSB(Large Document) 로 저장한다.
// ===================================================================

// 라이브러리(ag-psd, fflate) 를 동적 import 로 가져온다.
// 번들러 환경이라면 `import { writePsd } from 'ag-psd'` 으로 바꿔도 된다.
let __agPsdPromise = null;
const loadAgPsd = () => {
  if (!__agPsdPromise) {
    __agPsdPromise = import(/* @vite-ignore */ 'https://esm.sh/ag-psd@25.0.0?bundle')
      .catch(() => import(/* @vite-ignore */ 'https://cdn.jsdelivr.net/npm/ag-psd@25.0.0/+esm'));
  }
  return __agPsdPromise;
};
let __fflatePromise = null;
const loadFflate = () => {
  if (!__fflatePromise) {
    __fflatePromise = import(/* @vite-ignore */ 'https://esm.sh/fflate@0.8.2')
      .catch(() => import(/* @vite-ignore */ 'https://cdn.jsdelivr.net/npm/fflate@0.8.2/+esm'));
  }
  return __fflatePromise;
};

// 안전한 파일명 만들기
const sanitizeFilename = (s, fallback = 'frame') => {
  const t = String(s || '').replace(/[^\w가-힣\-_. ]+/g, '_').trim().slice(0, 60);
  return t || fallback;
};

// 깨끗한 흰색 캔버스 만들기 (배경 레이어용)
const makeWhiteCanvas = (w, h) => {
  const c = document.createElement('canvas');
  c.width = Math.max(1, w | 0); c.height = Math.max(1, h | 0);
  const ctx = c.getContext('2d');
  ctx.fillStyle = '#ffffff';
  ctx.fillRect(0, 0, c.width, c.height);
  return c;
};

// 빈 (투명) 캔버스
const makeBlankCanvas = (w, h) => {
  const c = document.createElement('canvas');
  c.width = Math.max(1, w | 0); c.height = Math.max(1, h | 0);
  return c;
};

// strokesByFrameRef 의 한 레이어를 캔버스에 합성
// (FrameView.redraw 와 동일한 로직, 단 BITMAP_Y_PADDING 보정 포함)
const composeRasterLayerCanvas = (frame, layerStore, canvasW, canvasH) => {
  const c = makeBlankCanvas(canvasW, canvasH);
  const ctx = c.getContext('2d');
  ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  let y = 0;
  for (const b of frame.blocks) {
    const arr = (layerStore?.byBlock?.[b.id]) || [];
    // cut 인 경우만 그림, gap 영역은 비워둔다 (콘티는 cut 안에만 그림)
    if (b.type === 'cut' && arr.length > 0) {
      // block-local 좌표계는 (0..bw, -BITMAP_Y_PADDING..h+padding) 였으므로
      // 캔버스 좌표(0..canvasW, y..y+h) 로 옮기려면 y 만큼 평행이동
      ctx.save();
      ctx.translate(0, y);
      for (const s of arr) {
        if (s.hidden) continue;
        renderStrokeToCtx(ctx, s, 0); // yShift=0 (이미 translate 했으니까)
      }
      ctx.restore();
    }
    y += b.height;
  }
  return c;
};

// 한 벡터(말풍선) 레이어를 SVG 로 직렬화한 뒤 캔버스로 래스터화한다.
// BubbleSVG 와 동일한 path 헬퍼(getRoundedRectPath / getThoughtBubblePath /
// getShoutBubblePath / getBubbleEdgePoint) 를 그대로 사용한다.
const composeBubbleLayerCanvas = async (bubbles, typoPresets, canvasW, canvasH) => {
  const c = makeBlankCanvas(canvasW, canvasH);
  if (!Array.isArray(bubbles) || bubbles.length === 0) return c;
  const ctx = c.getContext('2d');

  // SVG 한 덩어리로 빌드
  const svgParts = [];
  svgParts.push(`<svg xmlns="http://www.w3.org/2000/svg" width="${canvasW}" height="${canvasH}" viewBox="0 0 ${canvasW} ${canvasH}">`);
  // 폰트 fallback: Pretendard 가 CSP 에 없을 수 있으니 sans-serif 까지 명시
  svgParts.push(`<style>text,div{font-family:Pretendard,'Apple SD Gothic Neo','Noto Sans KR',sans-serif;}</style>`);

  for (const b of bubbles) {
    const { type, x, y, w, h, tailTip, text, typoPresetId } = b;
    const cx = x + w / 2, cy = y + h / 2, rx = w / 2, ry = h / 2;
    const preset = typoPresets?.find(p => p.id === typoPresetId);
    const fontSize = preset ? preset.size : (type === 'shout' ? 18 : 14);
    const fontWeight = preset ? preset.weight : (type === 'shout' ? 700 : 500);

    // tail
    if (tailTip) {
      if (type === 'thought') {
        const dots = 3;
        for (let i = 0; i < dots; i++) {
          const t = (i + 1) / (dots + 1);
          const ex = cx + (tailTip.x - cx) * t;
          const ey = (y + h) + (tailTip.y - (y + h)) * t;
          const r = Math.max(1.5, 5 - i * 1.2);
          svgParts.push(`<circle cx="${ex}" cy="${ey}" r="${r}" fill="#fff" stroke="#1a1a1a" stroke-width="2"/>`);
        }
      } else {
        const ep = getBubbleEdgePoint(b, tailTip.x, tailTip.y);
        const tdx = ep.x - tailTip.x, tdy = ep.y - tailTip.y;
        const tlen = Math.sqrt(tdx * tdx + tdy * tdy) || 1;
        const hw = type === 'shout' ? 14 : 11;
        const perp = { x: -tdy / tlen, y: tdx / tlen };
        const pts = `${ep.x + perp.x * hw},${ep.y + perp.y * hw} ${ep.x - perp.x * hw},${ep.y - perp.y * hw} ${tailTip.x},${tailTip.y}`;
        const dash = type === 'whisper' ? ` stroke-dasharray="5,3"` : '';
        svgParts.push(`<polygon points="${pts}" fill="#fff" stroke="#1a1a1a" stroke-width="2.5"${dash}/>`);
      }
    }

    // shape
    if (type === 'normal' || type === 'whisper') {
      const d = getRoundedRectPath(x, y, w, h, 108);
      const dash = type === 'whisper' ? ` stroke-dasharray="7,4"` : '';
      svgParts.push(`<path d="${d}" fill="#fff" stroke="#1a1a1a" stroke-width="2.5"${dash}/>`);
    } else if (type === 'thought') {
      const d = getThoughtBubblePath(cx, cy, rx, ry);
      svgParts.push(`<path d="${d}" fill="#fff" stroke="#1a1a1a" stroke-width="2.5"/>`);
    } else if (type === 'shout') {
      const d = getShoutBubblePath(cx, cy, rx, ry);
      svgParts.push(`<path d="${d}" fill="#fff" stroke="#1a1a1a" stroke-width="3.5" stroke-linejoin="miter"/>`);
    }

    // text (foreignObject 로 BubbleSVG 의 flex 중앙정렬 그대로 재현)
    const tpx = type === 'shout' ? w * 0.22 : type === 'thought' ? w * 0.1 : 12;
    const tpy = type === 'shout' ? h * 0.22 : type === 'thought' ? h * 0.1 : 8;
    const safeText = String(text || '')
      .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
      .replace(/\n/g, '<br/>');
    svgParts.push(
      `<foreignObject x="${x}" y="${y}" width="${Math.max(1, w)}" height="${Math.max(1, h)}">` +
      `<div xmlns="http://www.w3.org/1999/xhtml" style="width:100%;height:100%;display:flex;align-items:center;justify-content:center;padding:${tpy}px ${tpx}px;box-sizing:border-box;">` +
      `<div style="font-size:${fontSize}px;font-weight:${fontWeight};color:#1a1a1a;word-break:break-word;text-align:center;line-height:1.4;white-space:pre-wrap;width:100%;">${safeText}</div>` +
      `</div></foreignObject>`
    );
  }
  svgParts.push('</svg>');

  const svgBlob = new Blob([svgParts.join('')], { type: 'image/svg+xml;charset=utf-8' });
  const url = URL.createObjectURL(svgBlob);
  try {
    await new Promise((resolve, reject) => {
      const img = new Image();
      img.onload = () => { ctx.drawImage(img, 0, 0); resolve(); };
      img.onerror = (e) => reject(e || new Error('SVG 래스터화 실패'));
      img.src = url;
    });
  } finally {
    URL.revokeObjectURL(url);
  }
  return c;
};

// 컷 경계 + 양옆 마진을 표시하는 가이드 캔버스 (CSP 에서 본작업할 때 위치 잡기용)
const composeGuidesCanvas = (frame, canvasW, canvasH) => {
  const c = makeBlankCanvas(canvasW, canvasH);
  const ctx = c.getContext('2d');
  ctx.lineWidth = 1;
  // 컷 경계 (빨간 실선) / 갭 경계 (옅은 파선)
  let y = 0;
  for (const b of frame.blocks) {
    if (b.type === 'cut') {
      const ml = b.marginLeft ?? frame.sideMargin;
      const mr = b.marginRight ?? frame.sideMargin;
      // 컷 박스 외곽 (#d63a2e 옅은 빨강)
      ctx.strokeStyle = 'rgba(214, 58, 46, 0.55)';
      ctx.setLineDash([]);
      ctx.strokeRect(ml + 0.5, y + 0.5, Math.max(0, canvasW - ml - mr) - 1, b.height - 1);
    } else {
      // gap 영역은 가운데를 가로지르는 점선
      ctx.strokeStyle = 'rgba(214, 58, 46, 0.35)';
      ctx.setLineDash([6, 4]);
      ctx.beginPath();
      ctx.moveTo(0, y + b.height / 2 + 0.5);
      ctx.lineTo(canvasW, y + b.height / 2 + 0.5);
      ctx.stroke();
      ctx.setLineDash([]);
    }
    y += b.height;
  }
  // 양옆 sideMargin 보조선 (옅은 회색 파선)
  ctx.strokeStyle = 'rgba(80, 80, 80, 0.4)';
  ctx.setLineDash([4, 4]);
  ctx.beginPath();
  ctx.moveTo(frame.sideMargin + 0.5, 0);
  ctx.lineTo(frame.sideMargin + 0.5, canvasH);
  ctx.moveTo(canvasW - frame.sideMargin + 0.5, 0);
  ctx.lineTo(canvasW - frame.sideMargin + 0.5, canvasH);
  ctx.stroke();
  return c;
};

// 한 프레임을 PSD/PSB 바이트 Uint8Array 로 만든다.
// frame: project frame 객체
// strokesRef: strokesByFrameRef.current  (전체)
// bubblesByLayer / typoPresets: 컴포넌트 state
// 반환: { bytes: Uint8Array, ext: 'psd' | 'psb' }
const buildFramePsd = async (frame, strokesRef, bubblesByLayer, typoPresets) => {
  const { writePsd, writePsdBuffer } = await loadAgPsd();
  const canvasW = Math.max(1, frame.canvasWidth | 0);
  const canvasH = Math.max(1, frame.blocks.reduce((s, b) => s + b.height, 0) | 0);
  const usePsb = canvasH > 30000 || canvasW > 30000;

  // 레이어 빌드 (PSD 는 위쪽이 children[0])
  const conteChildren = [];

  // frame.layers 는 콘티 UI 상의 순서대로다.
  // PSD layer 순서를 콘티 순서와 맞추기 위해 그대로 push 한다.
  for (const L of frame.layers) {
    const opacity = Math.max(0, Math.min(1, (L.opacity ?? 100) / 100));
    const hidden = !L.visible;
    if (L.type === 'raster') {
      const ls = strokesRef?.[frame.id]?.[L.id];
      const canvas = composeRasterLayerCanvas(frame, ls || { byBlock: {} }, canvasW, canvasH);
      conteChildren.push({
        name: L.name || 'Layer',
        canvas, opacity, hidden,
        blendMode: 'normal',
      });
    } else if (L.type === 'vector') {
      const bubbles = bubblesByLayer?.[L.id] || [];
      const canvas = await composeBubbleLayerCanvas(bubbles, typoPresets, canvasW, canvasH);
      conteChildren.push({
        name: L.name || 'Bubble',
        canvas, opacity, hidden,
        blendMode: 'normal',
      });
    }
  }

  // 가이드 그룹 (CSP 에서 안 보이게 기본 hidden)
  const guideCanvas = composeGuidesCanvas(frame, canvasW, canvasH);
  const guideGroup = {
    name: '[가이드] 컷·마진',
    opened: false,
    hidden: true,
    children: [
      { name: '컷 경계 + 양옆 마진', canvas: guideCanvas, opacity: 1, hidden: false },
    ],
  };

  // 콘티 그룹
  // 레이어 순서 매핑:
  //   콘티 UI 는 frame.layers[length-1] 이 가장 위(최상단), layers[0] 이 가장 아래.
  //   redraw() 는 layers[0] → layers[length-1] 순으로 그리므로 뒤쪽이 위에 덮어씌워진다.
  //   PSD/ag-psd 의 children 은 children[0] 이 최상단.
  //   따라서 frame.layers 를 그대로 순회해 push 한 뒤 reverse() 하면
  //   conteChildren[0] = layers[length-1] (콘티 UI 맨 위) = PSD 최상단. 매핑 OK.
  const conteGroup = {
    name: '콘티',
    opened: true,
    hidden: false,
    children: conteChildren.reverse(),
  };

  // 배경(흰색)
  const bgCanvas = makeWhiteCanvas(canvasW, canvasH);
  const bgLayer = {
    name: 'Background',
    canvas: bgCanvas, opacity: 1, hidden: false, blendMode: 'normal',
  };

  // per-block gradient 배경(있을 때만 layer 로 추가)
  const hasAnyGradient = frame.blocks.some(b => !!b.gradient);
  let gradientLayer = null;
  if (hasAnyGradient) {
    const gc = makeBlankCanvas(canvasW, canvasH);
    const gctx = gc.getContext('2d');
    let y = 0;
    for (const b of frame.blocks) {
      if (b.gradient) {
        const ml = b.type === 'cut' ? (b.marginLeft ?? frame.sideMargin) : 0;
        const mr = b.type === 'cut' ? (b.marginRight ?? frame.sideMargin) : 0;
        const bw = b.type === 'cut' ? Math.max(10, canvasW - ml - mr) : canvasW;
        paintGradientToCtx(gctx, b.gradient, ml, y, bw, b.height);
      }
      y += b.height;
    }
    gradientLayer = {
      name: '배경 그라데이션',
      canvas: gc, opacity: 1, hidden: false, blendMode: 'normal',
    };
  }

  const psd = {
    width: canvasW,
    height: canvasH,
    // 합성용 캔버스(섬네일/플랫 미리보기). CSP 는 레이어를 읽으므로 우선순위 낮음.
    canvas: bgCanvas,
    // children 순서: 위(top)에서 아래(bottom) 로.
    //   guideGroup (최상단 가이드)
    //   conteGroup (콘티 레이어들)
    //   gradientLayer (있으면 콘티 아래)
    //   bgLayer (최하단 흰 배경)
    children: [guideGroup, conteGroup, ...(gradientLayer ? [gradientLayer] : []), bgLayer],
  };

  const writer = writePsdBuffer || writePsd;
  const bytes = writer(psd, { psb: usePsb });
  return { bytes: bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes), ext: usePsb ? 'psb' : 'psd' };
};

// 단일 프레임 다운로드
const triggerBytesDownload = (filename, bytes, mime = 'application/octet-stream') => {
  const blob = new Blob([bytes], { type: mime });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url; a.download = filename; a.style.display = 'none';
  document.body.appendChild(a); a.click();
  setTimeout(() => { document.body.removeChild(a); URL.revokeObjectURL(url); }, 100);
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
        <span className="layer-opacity-label" onClick={onActivate}>op</span>
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

// ===================================================================
//  SAVE / LOAD DIALOG
// ===================================================================
const SaveLoadDialog = ({
  open, onClose,
  currentProjectId, currentProjectName,
  onSaveCurrent, onSaveAsNew, onLoad, onDelete, onRename, onNewProject,
  onExport, onImportFile,
  onExportPSD,
  hasFrames, frameCount,
  storageBackend,
}) => {
  const [projects, setProjects] = useState([]);
  const [busy, setBusy] = useState(false);
  const [newName, setNewName] = useState('');
  const [errorMsg, setErrorMsg] = useState('');
  const [usage, setUsage] = useState({ used: 0, quota: 0 });
  const fileInputRef = useRef(null);

  const refresh = useCallback(async () => {
    setBusy(true);
    try {
      const list = await ProjectStorage.listProjects();
      setProjects(list);
      const u = await ProjectStorage.approximateSize();
      setUsage(u);
    } catch (e) {
      setErrorMsg(e?.message || '목록을 불러오지 못했습니다');
    } finally {
      setBusy(false);
    }
  }, []);

  useEffect(() => { if (open) { refresh(); setErrorMsg(''); setNewName(''); } }, [open, refresh]);

  if (!open) return null;

  const handleSaveCurrent = async () => {
    setBusy(true); setErrorMsg('');
    try {
      const r = await onSaveCurrent();
      if (!r?.ok) setErrorMsg(r?.error || '저장 실패');
      await refresh();
    } catch (e) { setErrorMsg(e?.message || '저장 실패'); }
    finally { setBusy(false); }
  };

  const handleSaveAsNew = async () => {
    const name = newName.trim();
    if (!name) { setErrorMsg('프로젝트 이름을 입력해주세요'); return; }
    setBusy(true); setErrorMsg('');
    try {
      const r = await onSaveAsNew(name);
      if (!r?.ok) setErrorMsg(r?.error || '저장 실패');
      else { setNewName(''); }
      await refresh();
    } catch (e) { setErrorMsg(e?.message || '저장 실패'); }
    finally { setBusy(false); }
  };

  const handleLoad = async (id, name) => {
    if (!window.confirm(`"${name}"을(를) 불러옵니다.\n현재 작업중인 내용은 자동 저장된 상태로 남고, 이 프로젝트로 전환됩니다.`)) return;
    setBusy(true); setErrorMsg('');
    try {
      const r = await onLoad(id);
      if (!r?.ok) setErrorMsg(r?.error || '불러오기 실패');
      else onClose();
    } catch (e) { setErrorMsg(e?.message || '불러오기 실패'); }
    finally { setBusy(false); }
  };

  const handleDelete = async (id, name) => {
    if (!window.confirm(`"${name}"을(를) 삭제합니다. 이 동작은 되돌릴 수 없습니다.`)) return;
    setBusy(true); setErrorMsg('');
    try { await onDelete(id); await refresh(); }
    catch (e) { setErrorMsg(e?.message || '삭제 실패'); }
    finally { setBusy(false); }
  };

  const handleRename = async (id, oldName) => {
    const next = window.prompt('새 이름을 입력해주세요', oldName);
    if (next === null) return;
    const trimmed = next.trim();
    if (!trimmed || trimmed === oldName) return;
    setBusy(true); setErrorMsg('');
    try { await onRename(id, trimmed); await refresh(); }
    catch (e) { setErrorMsg(e?.message || '이름 변경 실패'); }
    finally { setBusy(false); }
  };

  const handleNew = async () => {
    if (!window.confirm('새 프로젝트를 시작합니다.\n저장하지 않은 변경사항은 자동 저장본에 남지만, 새 프로젝트가 새로 자동 저장을 덮어쓰게 됩니다. 계속할까요?')) return;
    setBusy(true);
    try { await onNewProject(); onClose(); }
    catch (e) { setErrorMsg(e?.message || '새 프로젝트 실패'); }
    finally { setBusy(false); }
  };

  const handleExport = () => {
    setErrorMsg('');
    const r = onExport();
    if (!r?.ok) setErrorMsg(r?.error || '내보내기 실패');
  };

  const handleExportPSDCurrent = async () => {
    if (!onExportPSD) return;
    setBusy(true); setErrorMsg('');
    try {
      const r = await onExportPSD('current');
      if (!r?.ok) setErrorMsg(r?.error || 'PSD 내보내기 실패');
    } catch (e) { setErrorMsg(e?.message || 'PSD 내보내기 실패'); }
    finally { setBusy(false); }
  };

  const handleExportPSDAll = async () => {
    if (!onExportPSD) return;
    if (frameCount > 1 && !window.confirm(`${frameCount}개 프레임을 각각 PSD 로 변환해 zip 으로 받습니다.\n프레임 수에 따라 수십 초 걸릴 수 있어요. 계속할까요?`)) return;
    setBusy(true); setErrorMsg('');
    try {
      const r = await onExportPSD('all');
      if (!r?.ok) setErrorMsg(r?.error || 'PSD 내보내기 실패');
    } catch (e) { setErrorMsg(e?.message || 'PSD 내보내기 실패'); }
    finally { setBusy(false); }
  };

  const handleImportClick = () => fileInputRef.current?.click();

  const handleFileChange = async (e) => {
    const file = e.target.files?.[0];
    e.target.value = ''; // reset so same file can be picked again
    if (!file) return;
    if (!window.confirm(`"${file.name}"을(를) 불러옵니다.\n현재 작업중인 내용은 자동 저장된 상태로 남습니다.`)) return;
    setBusy(true); setErrorMsg('');
    try {
      const r = await onImportFile(file);
      if (!r?.ok) setErrorMsg(r?.error || '가져오기 실패');
      else onClose();
    } catch (err) { setErrorMsg(err?.message || '가져오기 실패'); }
    finally { setBusy(false); }
  };

  return (
    <div className="conti-modal-backdrop" onPointerDown={(e) => { if (e.target === e.currentTarget) onClose(); }}>
      <div className="conti-modal" role="dialog" aria-modal="true">
        <div className="conti-modal-header">
          <div>
            <div className="conti-modal-title">프로젝트 관리</div>
            <div className="conti-modal-subtitle">
              현재: <strong>{currentProjectName || '제목 없음'}</strong>
              {storageBackend && <span className="conti-modal-tag mono">{storageBackend === 'idb' ? 'IndexedDB' : 'localStorage'}</span>}
            </div>
          </div>
          <button className="conti-modal-close" onClick={onClose} aria-label="닫기">×</button>
        </div>

        {errorMsg && <div className="conti-modal-error">{errorMsg}</div>}

        <div className="conti-modal-body">
          {/* SAVE 영역 */}
          <section className="conti-modal-section">
            <h4>저장</h4>
            <div className="conti-modal-save-row">
              <button
                className="conti-modal-btn primary"
                disabled={busy || !currentProjectId}
                onClick={handleSaveCurrent}
                title={!currentProjectId ? '먼저 새 이름으로 저장해주세요' : '현재 프로젝트에 덮어쓰기'}
              >
                💾 현재 프로젝트에 저장
              </button>
            </div>
            <div className="conti-modal-save-row">
              <input
                className="conti-modal-input"
                placeholder="새 이름으로 저장 (예: 1화 콘티 v1)"
                value={newName}
                onChange={(e) => setNewName(e.target.value)}
                onKeyDown={(e) => { if (e.key === 'Enter') handleSaveAsNew(); }}
                disabled={busy}
              />
              <button className="conti-modal-btn" disabled={busy || !newName.trim()} onClick={handleSaveAsNew}>
                + 새로 저장
              </button>
            </div>
          </section>

          {/* PROJECT 목록 */}
          <section className="conti-modal-section">
            <h4>저장된 프로젝트 <span className="conti-modal-count mono">{projects.length}</span></h4>
            {projects.length === 0 ? (
              <div className="conti-modal-empty">
                {busy ? '불러오는 중...' : '저장된 프로젝트가 없습니다'}
              </div>
            ) : (
              <div className="conti-modal-list">
                {projects.map((p) => {
                  const isCurrent = p.id === currentProjectId;
                  const meta = p.meta || {};
                  return (
                    <div key={p.id} className={`conti-modal-item${isCurrent ? ' current' : ''}`}>
                      <div className="conti-modal-item-main">
                        <div className="conti-modal-item-name">
                          {p.name}
                          {isCurrent && <span className="conti-modal-current-badge">현재</span>}
                        </div>
                        <div className="conti-modal-item-meta mono">
                          {formatRelativeTime(p.savedAt)}
                          {meta.frames != null && ` · frames ${meta.frames}`}
                          {meta.cuts != null && ` · cuts ${meta.cuts}`}
                          {meta.strokes != null && ` · strokes ${meta.strokes}`}
                          {meta.bubbles != null && ` · bubbles ${meta.bubbles}`}
                        </div>
                      </div>
                      <div className="conti-modal-item-actions">
                        <button className="conti-modal-btn small" disabled={busy} onClick={() => handleLoad(p.id, p.name)}>열기</button>
                        <button className="conti-modal-btn small" disabled={busy} onClick={() => handleRename(p.id, p.name)}>이름</button>
                        <button className="conti-modal-btn small danger" disabled={busy} onClick={() => handleDelete(p.id, p.name)}>삭제</button>
                      </div>
                    </div>
                  );
                })}
              </div>
            )}
          </section>

          {/* EXPORT / IMPORT */}
          <section className="conti-modal-section">
            <h4>파일로 내보내기 · 가져오기</h4>
            <div className="conti-modal-hint">
              아이패드 ↔ 컴퓨터 사이를 옮기거나 백업하려면 파일로 내보내세요. .conti.json 파일이 다운로드됩니다.
            </div>
            <div className="conti-modal-save-row">
              <button className="conti-modal-btn" disabled={busy} onClick={handleExport}>
                ⬇ 현재 프로젝트 파일로 내보내기
              </button>
              <button className="conti-modal-btn" disabled={busy} onClick={handleImportClick}>
                ⬆ 파일에서 가져오기
              </button>
              <input ref={fileInputRef} type="file" accept=".json,.conti,.conti.json,application/json"
                style={{ display: 'none' }} onChange={handleFileChange} />
            </div>
          </section>

          {/* CLIP STUDIO 연동 — PSD 내보내기 */}
          <section className="conti-modal-section">
            <h4>클립스튜디오로 보내기 <span className="conti-modal-tag">PSD/PSB</span></h4>
            <div className="conti-modal-hint">
              .clip 포맷은 Celsys 비공개 포맷이라 직접 만들 수 없어, CSP 가 공식 지원하는 PSD 로 내보냅니다.
              CSP 에서 <strong>파일 → 열기</strong> 로 그대로 열면 레이어가 보존됩니다.
              {' '}높이가 30,000px 를 넘는 프레임은 자동으로 PSB(Large Document) 로 저장돼요.
              {' '}말풍선/텍스트는 래스터화됩니다 (CSP 자체 PSD export 도 동일).
            </div>
            <div className="conti-modal-save-row">
              <button
                className="conti-modal-btn primary"
                disabled={busy || !hasFrames}
                onClick={handleExportPSDCurrent}
                title="현재 선택된 프레임만 PSD 로 내보냅니다"
              >
                🎨 현재 프레임만 PSD 로
              </button>
              <button
                className="conti-modal-btn"
                disabled={busy || !hasFrames}
                onClick={handleExportPSDAll}
                title="모든 프레임을 각각 PSD 로 만들어 zip 으로 다운로드"
              >
                📦 모든 프레임 → zip{frameCount > 0 ? ` (${frameCount}개)` : ''}
              </button>
            </div>
          </section>

          {/* NEW PROJECT */}
          <section className="conti-modal-section">
            <h4>새 프로젝트</h4>
            <div className="conti-modal-hint">
              모든 frames / strokes / 말풍선을 비우고 새로 시작합니다. 자동 저장본은 덮어써집니다.
            </div>
            <button className="conti-modal-btn danger" disabled={busy} onClick={handleNew}>
              ⊕ 새 프로젝트 시작
            </button>
          </section>

          {/* USAGE INFO */}
          {usage.used > 0 && (
            <section className="conti-modal-section">
              <h4>저장 공간</h4>
              <div className="conti-modal-usage mono">
                사용량: {formatBytes(usage.used)}
                {usage.quota > 0 && ` / ${formatBytes(usage.quota)}`}
              </div>
            </section>
          )}
        </div>
      </div>
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
  color: var(--ink); background: var(--bg); user-select: none; -webkit-user-select: none; -webkit-touch-callout: none; overflow: hidden;
}
.conti-root *, .conti-root *::before, .conti-root *::after { box-sizing: border-box; }
/* iPad pen-drawing 안정화: 모든 자식에 callout/drag/tap-highlight 차단 (특히 iOS Safari에서 -webkit-touch-callout 가 상속되지 않는 경우 대비) */
.conti-root, .conti-root * {
  -webkit-touch-callout: none !important;
  -webkit-user-drag: none;
  -webkit-tap-highlight-color: transparent;
}
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
  display: flex; align-items: center; gap: 4px; padding: 6px 8px 6px 16px; background: var(--paper);
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
  /* 펜 입력시 iOS Scribble/선택 차단 */
  touch-action: none;
  -webkit-user-select: none; user-select: none;
  -webkit-touch-callout: none;
}
.conti-frame.selected .conti-frame-stage { outline: 2px solid var(--accent); outline-offset: 4px; }
.conti-block { position: absolute; pointer-events: none; }
.conti-block.cut { background: var(--cut); }
.conti-block.gap { background: var(--gap); }
.conti-frame-canvas {
  position: absolute; top: 0; left: 0; display: block; pointer-events: none;
  touch-action: none;
  -webkit-user-select: none; user-select: none;
  -webkit-touch-callout: none;
}
.conti-frame-overlay {
  position: absolute; top: 0; left: 0; display: block; z-index: 5;
  touch-action: none;
  -webkit-user-select: none; user-select: none;
  -webkit-touch-callout: none;
  -webkit-tap-highlight-color: transparent;
  -webkit-user-drag: none;
}
.conti-frame-overlay.tool-pen { cursor: crosshair; }
.conti-frame-overlay.tool-lasso { cursor: cell; }
.conti-frame-overlay.tool-lasso-selected { cursor: move; }
.conti-frame-overlay.tool-vector { cursor: default; }
.conti-frame-overlay.tool-eraser { cursor: none; }
.conti-eraser-cursor {
  position: absolute; pointer-events: none; border-radius: 50%;
  border: 2px solid rgba(0,0,0,0.55); background: rgba(255,255,255,0.25);
  box-shadow: 0 0 0 1px rgba(255,255,255,0.6);
  transform: translate(-50%, -50%); z-index: 10; transition: none;
}
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
.conti-block-row input[type="number"]::-webkit-inner-spin-button,
.conti-block-row input[type="number"]::-webkit-outer-spin-button { -webkit-appearance: none; margin: 0; }
.conti-block-row input[type="number"] { -moz-appearance: textfield; }
.conti-block-row .del {
  width: 22px; height: 22px; display: flex; align-items: center; justify-content: center;
  font-size: 14px; color: var(--muted); border-radius: 3px; flex-shrink: 0; transition: all 0.12s ease;
}
.conti-block-row .del:hover { background: var(--accent-soft); color: var(--accent); }
.block-height-stepper {
  display: flex; flex-direction: column; flex-shrink: 0; gap: 0;
  border: 1px solid var(--line); border-radius: 3px; overflow: hidden;
}
.block-height-btn {
  width: 16px; height: 11px; display: flex; align-items: center; justify-content: center;
  font-size: 8px; line-height: 1; flex-shrink: 0;
  color: var(--muted); background: var(--bg-panel);
  transition: color 0.1s ease, background 0.1s ease;
  user-select: none;
}
.block-height-btn + .block-height-btn { border-top: 1px solid var(--line); }
.block-height-btn:hover { color: var(--ink); background: var(--paper); }
.block-height-btn:active { background: var(--line); }
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
.conti-block-margin-row.attach-bottom { border-radius: 0; border-bottom: none; margin-bottom: 0; }

/* gradient button in block row */
.block-grad-btn {
  width: 22px; height: 22px; display: flex; align-items: center; justify-content: center;
  font-family: 'JetBrains Mono', monospace; font-size: 9px; font-weight: 700; letter-spacing: 0;
  flex-shrink: 0; border-radius: 4px;
  color: var(--muted); background: transparent; border: 1px solid var(--line);
  transition: all 0.12s ease; padding: 0;
}
.block-grad-btn:hover { color: var(--ink); border-color: var(--ink-2); }
.block-grad-btn.has {
  color: transparent; border-color: var(--ink-2);
  box-shadow: inset 0 0 0 1px rgba(255,255,255,0.5);
}
.block-grad-btn.editing {
  border-color: #3b8efe; box-shadow: 0 0 0 1px #3b8efe, inset 0 0 0 1px rgba(255,255,255,0.5);
}

/* gradient editor sub-row (sits below margin row / block row) */
.conti-block-gradient-row {
  display: flex; flex-direction: column; gap: 5px;
  padding: 8px 8px 8px 8px; margin-top: -1px; margin-bottom: 4px;
  background: var(--bg-panel); border: 1px solid var(--line); border-top: none;
  border-radius: 0 0 5px 5px;
}
.conti-block-gradient-row.viewport-active {
  border-color: var(--accent); background: color-mix(in srgb, var(--accent-soft) 60%, var(--bg-panel));
  box-shadow: inset 3px 0 0 var(--accent);
}
.grad-header {
  display: flex; align-items: center; gap: 5px;
}
.grad-label {
  font-family: 'JetBrains Mono', monospace; font-size: 9px; letter-spacing: 0.1em;
  color: var(--muted); text-transform: uppercase; flex-shrink: 0;
}
.grad-bar {
  flex: 1; height: 12px; border-radius: 2px; border: 1px solid var(--line); min-width: 0;
}
.grad-mini-btn {
  width: 20px; height: 20px; display: flex; align-items: center; justify-content: center;
  font-size: 11px; line-height: 1; color: var(--muted);
  background: var(--paper); border: 1px solid var(--line); border-radius: 3px;
  flex-shrink: 0; transition: all 0.12s ease;
}
.grad-mini-btn:hover { color: var(--ink); border-color: var(--ink-2); }
.grad-mini-btn.danger:hover { color: var(--accent); border-color: var(--accent); background: var(--accent-soft); }
.grad-stop-row {
  display: flex; align-items: center; gap: 5px; min-width: 0;
}
.grad-swatch {
  width: 16px; height: 16px; flex-shrink: 0; border-radius: 3px;
  border: 1px solid var(--line);
  box-shadow: inset 0 0 0 1px rgba(255,255,255,0.4);
}
.grad-gray-slider {
  flex: 1; min-width: 0; height: 6px; -webkit-appearance: none; appearance: none;
  background: linear-gradient(90deg, #ffffff, #000000);
  border: 1px solid var(--line); border-radius: 999px; outline: none; margin: 0;
}
.grad-gray-slider::-webkit-slider-thumb {
  -webkit-appearance: none; appearance: none; width: 12px; height: 12px;
  background: var(--paper); border: 2px solid var(--ink); border-radius: 50%; cursor: pointer;
}
.grad-gray-slider::-moz-range-thumb {
  width: 12px; height: 12px; background: var(--paper);
  border: 2px solid var(--ink); border-radius: 50%; cursor: pointer;
}
.grad-hex {
  font-size: 9px; color: var(--ink-2); letter-spacing: 0.04em;
  flex-shrink: 0; width: 50px; text-align: center;
}
.grad-offset {
  width: 36px; padding: 2px 3px; font-family: 'JetBrains Mono', monospace; font-size: 10px;
  background: var(--paper); border: 1px solid var(--line); border-radius: 3px;
  text-align: right; color: var(--ink); flex-shrink: 0;
  -moz-appearance: textfield;
}
.grad-offset::-webkit-inner-spin-button, .grad-offset::-webkit-outer-spin-button { -webkit-appearance: none; margin: 0; }
.grad-offset:focus { outline: none; border-color: var(--ink); }
.grad-offset-unit { font-size: 9px; color: var(--muted); margin-left: -3px; flex-shrink: 0; }
.grad-stop-del {
  width: 18px; height: 18px; display: flex; align-items: center; justify-content: center;
  font-size: 12px; color: var(--muted); border-radius: 3px; flex-shrink: 0;
  transition: all 0.12s ease;
}
.grad-stop-del:hover:not(:disabled) { color: var(--accent); background: var(--accent-soft); }
.grad-stop-del:disabled { opacity: 0.25; cursor: not-allowed; }

/* gradient editor SVG */
.conti-gradient-editor { user-select: none; -webkit-user-select: none; -webkit-touch-callout: none; }

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

/* ====== save status indicator (next to brand) ====== */
.conti-save-status {
  display: inline-flex; align-items: center; gap: 5px;
  font-family: 'JetBrains Mono', monospace; font-size: 9px;
  color: var(--muted); letter-spacing: 0.04em;
}
.conti-save-status .save-dot {
  width: 5px; height: 5px; border-radius: 50%; background: var(--muted);
  transition: background 0.2s ease;
}
.conti-save-status.saving .save-dot { background: #e0a82a; animation: contiSavePulse 1s ease-in-out infinite; }
.conti-save-status.saved .save-dot { background: #6fc275; }
.conti-save-status.error .save-dot { background: var(--accent); }
@keyframes contiSavePulse { 0%, 100% { opacity: 0.4; } 50% { opacity: 1; } }

/* ====== save/load modal ====== */
.conti-modal-backdrop {
  position: fixed; inset: 0; z-index: 1000;
  background: rgba(22, 20, 15, 0.55);
  display: flex; align-items: center; justify-content: center;
  padding: 24px; backdrop-filter: blur(2px); -webkit-backdrop-filter: blur(2px);
  animation: contiModalFade 0.18s ease-out;
}
@keyframes contiModalFade { from { opacity: 0; } to { opacity: 1; } }
.conti-modal {
  width: 100%; max-width: 640px; max-height: calc(100vh - 48px);
  background: var(--bg); border: 1px solid var(--line);
  border-radius: 10px; box-shadow: 0 20px 60px rgba(0,0,0,0.35);
  display: flex; flex-direction: column; overflow: hidden;
  animation: contiModalUp 0.22s cubic-bezier(0.2, 0.8, 0.2, 1);
}
@keyframes contiModalUp { from { transform: translateY(8px) scale(0.98); opacity: 0; } to { transform: none; opacity: 1; } }
.conti-modal-header {
  display: flex; align-items: flex-start; justify-content: space-between;
  padding: 18px 20px 14px; border-bottom: 1px solid var(--line); flex-shrink: 0;
  gap: 12px;
}
.conti-modal-title { font-size: 15px; font-weight: 700; color: var(--ink); letter-spacing: -0.01em; }
.conti-modal-subtitle {
  margin-top: 4px; font-size: 11px; color: var(--muted);
  display: flex; align-items: center; gap: 8px; flex-wrap: wrap;
}
.conti-modal-subtitle strong { color: var(--ink-2); font-weight: 600; }
.conti-modal-tag {
  display: inline-block; padding: 1px 6px; font-size: 9px;
  background: var(--bg-panel); border: 1px solid var(--line); border-radius: 3px;
  color: var(--muted); letter-spacing: 0.06em;
}
.conti-modal-close {
  width: 32px; height: 32px; flex-shrink: 0;
  font-size: 22px; line-height: 1; color: var(--muted);
  border-radius: 6px; transition: all 0.12s ease;
}
.conti-modal-close:hover { background: var(--bg-panel); color: var(--ink); }
.conti-modal-error {
  margin: 12px 20px 0; padding: 8px 12px;
  background: var(--accent-soft); border: 1px solid rgba(196, 58, 44, 0.3);
  border-radius: 5px; color: var(--accent); font-size: 12px;
}
.conti-modal-body {
  padding: 16px 20px 20px; overflow-y: auto; flex: 1; min-height: 0;
  display: flex; flex-direction: column; gap: 18px;
}
.conti-modal-section h4 {
  margin: 0 0 8px 0;
  font-family: 'JetBrains Mono', monospace; font-size: 10px; letter-spacing: 0.14em;
  color: var(--muted); text-transform: uppercase; font-weight: 600;
  display: flex; align-items: center; gap: 8px;
}
.conti-modal-count { color: var(--ink); font-size: 10px; }
.conti-modal-hint { font-size: 11px; color: var(--muted); margin-bottom: 8px; line-height: 1.5; }
.conti-modal-save-row {
  display: flex; gap: 6px; margin-bottom: 6px; flex-wrap: wrap;
}
.conti-modal-input {
  flex: 1; min-width: 180px; padding: 8px 10px; font-family: 'Pretendard', sans-serif; font-size: 13px;
  background: var(--paper); border: 1px solid var(--line); border-radius: 5px; color: var(--ink);
}
.conti-modal-input:focus { outline: none; border-color: var(--ink); }
.conti-modal-btn {
  padding: 8px 14px; font-family: 'Pretendard', sans-serif; font-size: 12px; font-weight: 500;
  color: var(--ink); background: var(--paper); border: 1px solid var(--line); border-radius: 5px;
  transition: all 0.12s ease; white-space: nowrap;
}
.conti-modal-btn:hover:not(:disabled) { background: var(--bg-panel); border-color: var(--ink-2); }
.conti-modal-btn:disabled { opacity: 0.4; cursor: not-allowed; }
.conti-modal-btn.primary { background: var(--ink); color: var(--paper); border-color: var(--ink); }
.conti-modal-btn.primary:hover:not(:disabled) { background: var(--ink-2); border-color: var(--ink-2); }
.conti-modal-btn.danger { color: var(--accent); border-color: rgba(196,58,44,0.4); }
.conti-modal-btn.danger:hover:not(:disabled) { background: var(--accent-soft); border-color: var(--accent); }
.conti-modal-btn.small { padding: 4px 9px; font-size: 11px; }
.conti-modal-empty {
  padding: 18px 12px; text-align: center; font-size: 12px; color: var(--muted);
  border: 1px dashed var(--line); border-radius: 5px;
}
.conti-modal-list {
  display: flex; flex-direction: column; gap: 5px;
  max-height: 280px; overflow-y: auto;
  padding-right: 2px;
}
.conti-modal-item {
  display: flex; align-items: center; gap: 10px;
  padding: 9px 12px; background: var(--paper);
  border: 1px solid var(--line); border-radius: 6px; transition: border-color 0.12s ease;
}
.conti-modal-item:hover { border-color: var(--ink-2); }
.conti-modal-item.current { border-color: var(--accent); background: var(--accent-soft); }
.conti-modal-item-main { flex: 1; min-width: 0; }
.conti-modal-item-name {
  font-size: 13px; color: var(--ink); font-weight: 600;
  display: flex; align-items: center; gap: 6px;
  white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
}
.conti-modal-current-badge {
  font-family: 'JetBrains Mono', monospace; font-size: 8px; letter-spacing: 0.08em;
  padding: 1px 5px; background: var(--accent); color: var(--paper);
  border-radius: 3px; text-transform: uppercase; font-weight: 600; flex-shrink: 0;
}
.conti-modal-item-meta { font-size: 10px; color: var(--muted); margin-top: 2px; }
.conti-modal-item-actions { display: flex; gap: 4px; flex-shrink: 0; }
.conti-modal-usage { font-size: 11px; color: var(--muted); }

/* mobile/tablet */
@media (max-width: 600px) {
  .conti-modal-backdrop { padding: 10px; }
  .conti-modal { max-height: calc(100vh - 20px); }
  .conti-modal-body { padding: 12px 14px 16px; gap: 14px; }
  .conti-modal-header { padding: 14px 16px 10px; }
  .conti-modal-item { flex-wrap: wrap; }
  .conti-modal-item-actions { width: 100%; justify-content: flex-end; }
}

@media (max-width: 900px) { .conti-sidebar.right { display: none; } }
@media (max-width: 700px) { .conti-sidebar { width: 200px; flex: 0 0 200px; } .conti-tool input[type="range"] { width: 70px; } }
`;

// ---------- FrameView ----------
const FrameView = forwardRef(function FrameView({
  frame, isSelected, showDimensions, activeTool, selectionPhase,
  getLayerBitmap, bubblesByLayer, selectedBubble, activeLayerType,
  typoPresets, eraserSize, eraserCursor,
  editingGradientBlockId,
  onSelect, onPointerDown, onPointerMove, onPointerUp,
  onBubbleOverlayPointerDown, onBubbleOverlayPointerMove, onBubbleOverlayPointerUp,
  onGradientHandlePointerDown, onGradientHandlePointerMove, onGradientHandlePointerUp,
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

  // ===================================================================
  // iPad / Apple Pencil 안정화:
  // React의 합성 touch 이벤트는 iOS Safari에서 passive listener로 등록되어
  // onPointerDown 안의 e.preventDefault() 가 OS의 기본동작(Scribble, 텍스트선택
  // 콜아웃 = "공유..." 팝업, long-press 등)을 막지 못함.
  // → overlay/stage 요소에 직접 native 리스너를 passive:false 로 등록해서
  //   터치/제스처 단계에서 즉시 preventDefault 한다.
  // ===================================================================
  useEffect(() => {
    const oc = overlayRef.current;
    const stage = oc?.parentElement; // .conti-frame-stage
    if (!oc) return;

    const block = (e) => { if (e.cancelable) e.preventDefault(); };

    // touch* : Scribble / 텍스트선택 콜아웃 / long-press 차단
    oc.addEventListener('touchstart', block, { passive: false });
    oc.addEventListener('touchmove', block, { passive: false });
    oc.addEventListener('touchend', block, { passive: false });
    oc.addEventListener('touchcancel', block, { passive: false });

    // gesture* : iOS pinch-zoom / rotate 차단 (Safari 전용)
    oc.addEventListener('gesturestart', block, { passive: false });
    oc.addEventListener('gesturechange', block, { passive: false });
    oc.addEventListener('gestureend', block, { passive: false });

    // selectstart : 빠른 stroke 시작 시 텍스트 선택이 트리거되는 것 차단
    const blockSelect = (e) => e.preventDefault();
    oc.addEventListener('selectstart', blockSelect);
    if (stage) stage.addEventListener('selectstart', blockSelect);

    return () => {
      oc.removeEventListener('touchstart', block);
      oc.removeEventListener('touchmove', block);
      oc.removeEventListener('touchend', block);
      oc.removeEventListener('touchcancel', block);
      oc.removeEventListener('gesturestart', block);
      oc.removeEventListener('gesturechange', block);
      oc.removeEventListener('gestureend', block);
      oc.removeEventListener('selectstart', blockSelect);
      if (stage) stage.removeEventListener('selectstart', blockSelect);
    };
  }, []);

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
  } else if (activeTool === 'eraser') {
    overlayCursorClass = 'tool-eraser';
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
          const bg = b.gradient ? gradientToCss(b.gradient, bw, b.height) : null;
          return (
            <div key={b.id} className={`conti-block ${b.type}${b.gradient ? ' has-gradient' : ''}`}
              style={{
                top: `${b.top}px`, left: `${ml}px`, width: `${bw}px`, height: `${b.height}px`,
                ...(bg ? { background: bg } : null),
              }} />
          );
        })}
        <canvas ref={canvasRef} className="conti-frame-canvas" style={{ touchAction: 'none' }} onContextMenu={e => e.preventDefault()} />

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
          onContextMenu={e => e.preventDefault()}
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

        {/* Gradient handle SVG (Figma-style) — only when editing a block's gradient in this frame */}
        {isSelected && editingGradientBlockId != null && (() => {
          const b = blockLayout.find(x => x.id === editingGradientBlockId);
          if (!b || !b.gradient) return null;
          const ml = b.type === 'cut' ? (b.marginLeft ?? frame.sideMargin) : 0;
          const mr = b.type === 'cut' ? (b.marginRight ?? frame.sideMargin) : 0;
          const bw = b.type === 'cut' ? Math.max(10, frame.canvasWidth - ml - mr) : frame.canvasWidth;
          const g = b.gradient;
          const sx = ml + g.start.x * bw, sy = b.top + g.start.y * b.height;
          const ex = ml + g.end.x   * bw, ey = b.top + g.end.y   * b.height;
          const HS = GRADIENT_HANDLE_SIZE;
          const handleStart = (ev, which) => {
            ev.stopPropagation();
            onGradientHandlePointerDown?.(ev, frame.id, b.id, which);
          };
          return (
            <svg className="conti-gradient-editor"
              width={frame.canvasWidth} height={totalHeight}
              style={{ position: 'absolute', top: 0, left: 0, overflow: 'visible', zIndex: 9, pointerEvents: 'none' }}>
              {/* outer outline (white for visibility on dark gradients) */}
              <line x1={sx} y1={sy} x2={ex} y2={ey} stroke="#ffffff" strokeWidth="3" strokeOpacity="0.85" />
              <line x1={sx} y1={sy} x2={ex} y2={ey} stroke={GRADIENT_LINE_COLOR} strokeWidth="1.5" />
              {/* start handle (white-filled square) */}
              <rect
                x={sx - HS / 2} y={sy - HS / 2} width={HS} height={HS}
                fill="#ffffff" stroke={GRADIENT_LINE_COLOR} strokeWidth="2"
                style={{ pointerEvents: 'all', cursor: 'move', touchAction: 'none' }}
                onPointerDown={ev => handleStart(ev, 'start')}
                onPointerMove={ev => onGradientHandlePointerMove?.(ev)}
                onPointerUp={ev => onGradientHandlePointerUp?.(ev)}
                onPointerCancel={ev => onGradientHandlePointerUp?.(ev)}
              />
              {/* end handle (blue-filled square) */}
              <rect
                x={ex - HS / 2} y={ey - HS / 2} width={HS} height={HS}
                fill={GRADIENT_LINE_COLOR} stroke="#ffffff" strokeWidth="2"
                style={{ pointerEvents: 'all', cursor: 'move', touchAction: 'none' }}
                onPointerDown={ev => handleStart(ev, 'end')}
                onPointerMove={ev => onGradientHandlePointerMove?.(ev)}
                onPointerUp={ev => onGradientHandlePointerUp?.(ev)}
                onPointerCancel={ev => onGradientHandlePointerUp?.(ev)}
              />
            </svg>
          );
        })()}

        {/* Eraser cursor visual */}
        {activeTool === 'eraser' && isSelected && eraserCursor && (
          <div className="conti-eraser-cursor" style={{
            left: eraserCursor.x, top: eraserCursor.y,
            width: eraserSize, height: eraserSize,
          }} />
        )}

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

  // Eraser
  const [eraserSize, setEraserSize] = useState(20);
  const [eraserCursor, setEraserCursor] = useState(null); // {x, y} in viewport coords

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

  // ===================================================================
  //  PROJECT (save/load) state
  // ===================================================================
  const [saveDialogOpen, setSaveDialogOpen] = useState(false);
  const [currentProjectId, setCurrentProjectId] = useState(null); // 저장된 프로젝트 id 또는 null
  const [currentProjectName, setCurrentProjectName] = useState('');
  // saveStatus: 'idle' | 'saving' | 'saved' | 'error' | 'dirty'
  const [saveStatus, setSaveStatus] = useState('idle');
  const [lastSaveAt, setLastSaveAt] = useState(0);
  const [storageBackend, setStorageBackend] = useState(null); // 'idb' | 'localStorage' | null
  // bumpRef를 늘리면 useEffect에서 (load 후) 모든 bitmap을 다시 그린다
  const [loadGen, setLoadGen] = useState(0);
  // 마운트 시 자동저장 복원을 한 번만 시도
  const autosaveCheckedRef = useRef(false);
  const autosaveTimerRef = useRef(null);
  // 저장된 상태 표시 표지를 일정 시간 후 'idle' 로 되돌리기 위한 타이머
  const savedFlashTimerRef = useRef(null);
  // load 직후 자동저장이 다시 트리거되지 않도록 잠시 잠금
  // 초기값 true: mount 시 자동저장본 복원 프롬프트가 끝날 때까지 자동저장 금지
  // (사용자가 "복원하지 않음"을 선택하면 그 사이에 빈 frame 이 자동저장을 덮어쓰는 걸 방지)
  const autosaveLockRef = useRef(true);
  // setLastSaveAt 의 최신값을 effect 안에서 안전하게 접근하기 위한 ref
  const lastSaveAtRef = useRef(0);
  useEffect(() => { lastSaveAtRef.current = lastSaveAt; }, [lastSaveAt]);
  // useCallback hooks 안에서 (의존성 추가 없이) 최신 requestAutosave 를 호출하기 위한 ref
  const requestAutosaveRef = useRef(null);


  const bubbleInterRef = useRef({ mode: null, frameId: null, layerId: null, bubbleId: null, startX: 0, startY: 0, origBubble: null });

  const drawingRef = useRef(null);
  const currentStrokeRef = useRef(null);
  const eraserRef = useRef({ active: false, frameId: null, layerId: null, erasedSet: new Set() });

  const lassoRef = useRef({
    phase: 'idle', frameId: null, layerId: null,
    lassoPoints: [], selectedItems: [], bbox: null,
    transform: { tx: 0, ty: 0, scaleX: 1, scaleY: 1, angle: 0, flipH: false, flipV: false },
    dragStart: null, origTransform: null, dragHandle: null, origHandleDist: null,
    transformHistory: [], // 올가미 툴 내부 undo 스택 (rotate/flip/drag/resize)
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
    const last = store.history[store.history.length - 1];
    if (last.type === 'erase') {
      store.history.pop();
      const dirtyBlocks = new Set();
      for (const stroke of last.strokes) {
        stroke.hidden = false;
        for (const [blockId, arr] of Object.entries(store.byBlock)) {
          if (arr.includes(stroke)) { dirtyBlocks.add(Number(blockId)); break; }
        }
      }
      for (const blockId of dirtyBlocks) {
        const block = selectedFrame.blocks.find(b => b.id === blockId);
        if (block) rebuildBlockBitmap(selectedFrameId, activeLayerId, block, selectedFrame.canvasWidth);
      }
    } else if (last.type === 'lasso-apply') {
      // 올가미 이동/변형 undo: 새로 배치된 stroke 제거 + 원본 stroke 복원
      store.history.pop();
      const dirtyBlocks = new Set();
      for (const { blockId, stroke } of last.added) {
        const arr = store.byBlock[blockId];
        if (arr) { const idx = arr.indexOf(stroke); if (idx >= 0) arr.splice(idx, 1); }
        dirtyBlocks.add(blockId);
      }
      for (const { blockId, stroke } of last.restored) {
        if (!store.byBlock[blockId]) store.byBlock[blockId] = [];
        stroke.hidden = false;
        store.byBlock[blockId].push(stroke);
        dirtyBlocks.add(blockId);
      }
      for (const blockId of dirtyBlocks) {
        const block = selectedFrame.blocks.find(b => b.id === blockId);
        if (block) rebuildBlockBitmap(selectedFrameId, activeLayerId, block, selectedFrame.canvasWidth);
      }
    } else if (last.type === 'lasso-delete') {
      // 올가미 삭제 undo: 삭제된 stroke 복원
      store.history.pop();
      const dirtyBlocks = new Set();
      for (const { blockId, stroke } of last.restored) {
        if (!store.byBlock[blockId]) store.byBlock[blockId] = [];
        stroke.hidden = false;
        store.byBlock[blockId].push(stroke);
        dirtyBlocks.add(blockId);
      }
      for (const blockId of dirtyBlocks) {
        const block = selectedFrame.blocks.find(b => b.id === blockId);
        if (block) rebuildBlockBitmap(selectedFrameId, activeLayerId, block, selectedFrame.canvasWidth);
      }
    } else {
      store.history.pop();
      const { blockId } = last;
      const arr = store.byBlock[blockId];
      if (arr && arr.length > 0) arr.pop();
      const block = selectedFrame.blocks.find(b => b.id === blockId);
      if (block) rebuildBlockBitmap(selectedFrameId, activeLayerId, block, selectedFrame.canvasWidth);
    }
    frameRefs.current[selectedFrameId]?.redraw();
    requestAutosaveRef.current?.();
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

  // ---------- gradient editing ----------
  // editingGradientBlockId: id of the block currently in "edit gradient" mode (handles visible + stops panel open). null = none.
  const [editingGradientBlockId, setEditingGradientBlockId] = useState(null);
  const gradientDragRef = useRef(null);
  // refs needed by gradient handle move (avoid stale closures)
  const framesRef = useRef(frames);
  useEffect(() => { framesRef.current = frames; }, [frames]);

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
    lasso.transformHistory = []; // 새 선택 시 transform 히스토리 초기화
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
    // 올가미 apply 전체를 하나의 배치 히스토리 엔트리로 기록 (undo 대응)
    const lassoHistoryAdded = [];   // 새로 배치된 stroke들
    const lassoHistoryRestored = []; // 원본 위치 stroke들 (undo 시 복원)
    let lassoHistoryLayerId = null;
    let lassoHistoryStore = null;

    for (const item of selectedItems) {
      const store = ensureLayerStore(frameId, item.layerId);
      if (!lassoHistoryStore) { lassoHistoryStore = store; lassoHistoryLayerId = item.layerId; }
      const origArr = store.byBlock[item.blockId];
      if (origArr) { const idx = origArr.indexOf(item.stroke); if (idx >= 0) origArr.splice(idx, 1); }
      if (!dirtyByLayer[item.layerId]) dirtyByLayer[item.layerId] = new Set();
      dirtyByLayer[item.layerId].add(item.blockId);
      // 원본 stroke 복원 정보 수집
      lassoHistoryRestored.push({ blockId: item.blockId, stroke: item.stroke });

      const newFramePts = item.framePoints.map(p => applySelectionTransform(p.x, p.y, cx, cy, transform));
      const centX = newFramePts.reduce((s,p)=>s+p.x,0)/newFramePts.length;
      const centY = newFramePts.reduce((s,p)=>s+p.y,0)/newFramePts.length;
      const newBlockId = findStrokeBlockId({ points: [{x:centX,y:centY}] }, frame.blocks, tops);
      if (newBlockId == null) continue;
      const newBlockTop = tops[newBlockId];
      const newLocalPts = newFramePts.map(p => ({ x: p.x, y: p.y - newBlockTop }));
      const newStroke = { points: newLocalPts, size: item.stroke.size, opacity: item.stroke.opacity, color: item.stroke.color, bbox: computeBbox(newLocalPts), hidden: false };
      if (!store.byBlock[newBlockId]) store.byBlock[newBlockId] = [];
      store.byBlock[newBlockId].push(newStroke);
      // 새 stroke 정보 수집 (undo 시 제거 대상)
      lassoHistoryAdded.push({ blockId: newBlockId, stroke: newStroke });
      dirtyByLayer[item.layerId].add(newBlockId);
    }
    // 배치 히스토리 엔트리 1개로 push (개별 push 대신)
    if (lassoHistoryStore && (lassoHistoryAdded.length > 0 || lassoHistoryRestored.length > 0)) {
      lassoHistoryStore.history.push({ type: 'lasso-apply', added: lassoHistoryAdded, restored: lassoHistoryRestored });
    }

    for (const [layerId, blockIds] of Object.entries(dirtyByLayer))
      for (const blockId of blockIds) {
        const block = frame.blocks.find(b => b.id === blockId);
        if (block) rebuildBlockBitmap(frameId, layerId, block, frame.canvasWidth);
      }
    frameRefs.current[frameId]?.redraw();
    lasso.phase = 'idle'; lasso.selectedItems = []; lasso.bbox = null; lasso.frameId = null;
    lasso.transformHistory = []; // apply 시 transform 히스토리 초기화
    frameRefs.current[frameId]?.clearOverlay();
    setHasSelection(false); setSelectionPhase('idle');
    requestAutosave();
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
    lasso.transformHistory = []; // cancel 시 transform 히스토리 초기화
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
    requestAutosave();
  };

  const flipSelection = (axis) => {
    const lasso = lassoRef.current;
    if (!['selected','dragging','resizing','rotating'].includes(lasso.phase)) return;
    lasso.transformHistory.push({ ...lasso.transform }); // flip 전 snapshot 저장
    lasso.transform = axis === 'h' ? { ...lasso.transform, flipH: !lasso.transform.flipH } : { ...lasso.transform, flipV: !lasso.transform.flipV };
    renderSelectionOverlay(lasso.frameId);
  };

  const rotateSelectionDeg = (deg) => {
    const lasso = lassoRef.current;
    if (!['selected','dragging','resizing','rotating'].includes(lasso.phase)) return;
    lasso.transformHistory.push({ ...lasso.transform }); // 회전 전 snapshot 저장
    lasso.transform = { ...lasso.transform, angle: lasso.transform.angle + deg * Math.PI / 180 };
    renderSelectionOverlay(lasso.frameId);
  };

  const deleteSelection = () => {
    const lasso = lassoRef.current;
    if (!lasso.selectedItems?.length) return;
    const frameId = lasso.frameId;
    const frame = frames.find(f => f.id === frameId);
    const dirtyByLayer = {};
    // 삭제된 stroke들의 복원 정보 수집 (undo 대응)
    const lassoDeleteRestored = [];
    let lassoDeleteStore = null;
    for (const item of lasso.selectedItems) {
      const store = ensureLayerStore(frameId, item.layerId);
      if (!lassoDeleteStore) lassoDeleteStore = store;
      const arr = store.byBlock[item.blockId];
      if (arr) { const idx = arr.indexOf(item.stroke); if (idx >= 0) arr.splice(idx, 1); }
      lassoDeleteRestored.push({ blockId: item.blockId, stroke: item.stroke });
      if (!dirtyByLayer[item.layerId]) dirtyByLayer[item.layerId] = new Set();
      dirtyByLayer[item.layerId].add(item.blockId);
    }
    // 배치 히스토리 엔트리 push
    if (lassoDeleteStore && lassoDeleteRestored.length > 0) {
      lassoDeleteStore.history.push({ type: 'lasso-delete', restored: lassoDeleteRestored });
    }
    for (const [layerId, blockIds] of Object.entries(dirtyByLayer))
      for (const blockId of blockIds) {
        const block = frame?.blocks.find(b => b.id === blockId);
        if (block) rebuildBlockBitmap(frameId, layerId, block, frame.canvasWidth);
      }
    frameRefs.current[frameId]?.redraw();
    lasso.phase = 'idle'; lasso.selectedItems = []; lasso.bbox = null; lasso.frameId = null;
    lasso.transformHistory = []; // delete 시 transform 히스토리 초기화
    frameRefs.current[frameId]?.clearOverlay();
    setHasSelection(false); setSelectionPhase('idle');
    requestAutosave();
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

    if (lasso.phase === 'drawing') {
      // 라쏘도 빠른 펜 이동에서 점 누락 방지를 위해 coalesced events 활용
      const native = e.nativeEvent || e;
      const coalesced = (typeof native.getCoalescedEvents === 'function')
        ? native.getCoalescedEvents()
        : null;
      if (coalesced && coalesced.length > 0) {
        for (const ev of coalesced) lasso.lassoPoints.push(getCanvasPoint(ev, overlayEl, frame));
      } else {
        lasso.lassoPoints.push(p);
      }
      renderSelectionOverlay(lasso.frameId); return;
    }
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
        // 올가미 내부 transform 히스토리가 있으면 먼저 undo, 없으면 일반 undo
        const lasso2 = lassoRef.current;
        if (lasso2.transformHistory && lasso2.transformHistory.length > 0) {
          const prevTransform = lasso2.transformHistory.pop();
          lasso2.transform = prevTransform;
          renderSelectionOverlay(lasso2.frameId);
        } else {
          undoLastStroke();
        }
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
      // 드래그/리사이즈/회전 시작 시 저장해둔 origTransform을 히스토리에 기록 (undo 대응)
      if (lasso.origTransform) lasso.transformHistory.push({ ...lasso.origTransform });
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
          // 올가미 툴 내부에서 transform 히스토리가 있으면 lasso undo 우선
          const lassoNow = lassoRef.current;
          if (['selected','dragging','resizing','rotating'].includes(lassoNow.phase) &&
              lassoNow.transformHistory && lassoNow.transformHistory.length > 0) {
            const prevTransform = lassoNow.transformHistory.pop();
            lassoNow.transform = prevTransform;
            renderSelectionOverlay(lassoNow.frameId);
          } else {
            undoLastStroke();
          }
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
      // Shortcut keys: P = pen, L = lasso, E = eraser
      if (!['INPUT','TEXTAREA'].includes(tag)) {
        if (e.key === 'p' || e.key === 'P') switchTool('pen');
        if (e.key === 'l' || e.key === 'L') switchTool('lasso');
        if (e.key === 'e' || e.key === 'E') switchTool('eraser');
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
  //  iPad / Apple Pencil 전역 안정화
  //  - viewport meta 로 pinch-zoom 차단 (펜 좌표 어긋남 + 제스처 충돌 방지)
  //  - document 레벨 gesturestart 차단
  //  - 캔버스 영역 안에서 발생하는 selectstart 차단 (텍스트 선택 콜아웃="공유..." 방지)
  // ===================================================================
  useEffect(() => {
    // viewport meta 동적 주입 (claude.ai/모바일 환경 대응)
    let metaInjected = false;
    let meta = document.querySelector('meta[name="viewport"]');
    if (!meta) {
      meta = document.createElement('meta');
      meta.name = 'viewport';
      document.head.appendChild(meta);
      metaInjected = true;
    }
    const prevContent = meta.getAttribute('content');
    meta.setAttribute(
      'content',
      'width=device-width, initial-scale=1.0, maximum-scale=1.0, minimum-scale=1.0, user-scalable=no, viewport-fit=cover'
    );

    // document 전역에서 iOS pinch/double-tap 제스처 차단
    const blockGesture = (e) => { if (e.cancelable) e.preventDefault(); };
    document.addEventListener('gesturestart', blockGesture, { passive: false });
    document.addEventListener('gesturechange', blockGesture, { passive: false });
    document.addEventListener('gestureend', blockGesture, { passive: false });

    // 캔버스 영역 안에서 발생하는 selectstart 만 차단 (sidebar input 입력은 그대로)
    const blockSelectInCanvas = (e) => {
      const area = canvasAreaRef.current;
      if (area && e.target && area.contains(e.target)) e.preventDefault();
    };
    document.addEventListener('selectstart', blockSelectInCanvas);

    return () => {
      document.removeEventListener('gesturestart', blockGesture);
      document.removeEventListener('gesturechange', blockGesture);
      document.removeEventListener('gestureend', blockGesture);
      document.removeEventListener('selectstart', blockSelectInCanvas);
      if (metaInjected && meta.parentNode) meta.parentNode.removeChild(meta);
      else if (meta && prevContent != null) meta.setAttribute('content', prevContent);
    };
  }, []);

  // ===================================================================
  //  ERASER helper — hide strokes whose points fall within eraserRadius
  // ===================================================================
  const eraseAtPoint = useCallback((frameId, frame, layerId, eraserX, eraserY, eraserRadius) => {
    const tops = computeBlockTops(frame.blocks);
    const store = strokesByFrameRef.current[frameId]?.[layerId];
    if (!store) return;
    const r2 = eraserRadius * eraserRadius;
    const dirtyBlocks = new Set();
    for (const block of frame.blocks) {
      const blockTop = tops[block.id];
      const localY = eraserY - blockTop;
      const arr = store.byBlock[block.id];
      if (!arr) continue;
      for (const stroke of arr) {
        if (stroke.hidden) continue;
        // Quick bbox reject
        if (stroke.bbox.maxX < eraserX - eraserRadius || stroke.bbox.minX > eraserX + eraserRadius) continue;
        if (stroke.bbox.maxY < localY - eraserRadius || stroke.bbox.minY > localY + eraserRadius) continue;
        // Point-level check
        let hit = false;
        for (const p of stroke.points) {
          const dx = p.x - eraserX, dy = p.y - localY;
          if (dx * dx + dy * dy <= r2) { hit = true; break; }
        }
        if (hit) {
          stroke.hidden = true;
          dirtyBlocks.add(block.id);
          eraserRef.current.erasedSet.add(stroke);
        }
      }
    }
    for (const blockId of dirtyBlocks) {
      const block = frame.blocks.find(b => b.id === blockId);
      if (block) rebuildBlockBitmap(frameId, layerId, block, frame.canvasWidth);
    }
    if (dirtyBlocks.size > 0) frameRefs.current[frameId]?.redraw();
  }, [rebuildBlockBitmap]);

  // ===================================================================
  //  Pen pointer handlers
  // ===================================================================
  const handlePointerDown = (e, frameId, overlayEl) => {
    if (activeTool === 'lasso') { handleLassoPointerDown(e, frameId, overlayEl); return; }
    if (activeTool === 'eraser') {
      if (e.pointerType === 'touch') {
        activeTouchPointersRef.current.set(e.pointerId, { x: e.clientX, y: e.clientY });
        if (activeTouchPointersRef.current.size >= 2) {
          if (!panStateRef.current) {
            const pts = [...activeTouchPointersRef.current.values()];
            panStateRef.current = { lastX: pts.reduce((s,p)=>s+p.x,0)/pts.length, lastY: pts.reduce((s,p)=>s+p.y,0)/pts.length };
          }
          // 지우개 툴에서도 two-finger tap undo 감지를 위해 twoFingerTapRef 설정
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
      eraserRef.current = { active: true, frameId, layerId: activeLayerId, erasedSet: new Set() };
      eraseAtPoint(frameId, frame, activeLayerId, p.x, p.y, eraserSize / 2);
      return;
    }
    if (e.pointerType === 'pen') {
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
      return;
    }
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
    if (activeTool === 'eraser') {
      // Update eraser cursor position
      if (overlayEl) {
        const rect = overlayEl.getBoundingClientRect();
        setEraserCursor({ x: e.clientX - rect.left, y: e.clientY - rect.top, frameEl: overlayEl });
      }
      if (e.pointerType === 'touch') {
        if (activeTouchPointersRef.current.has(e.pointerId))
          activeTouchPointersRef.current.set(e.pointerId, { x: e.clientX, y: e.clientY });
        if (activeTouchPointersRef.current.size >= 2) {
          // 지우개 툴에서도 two-finger tap vs pan 구분
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
      if (!eraserRef.current.active) return;
      e.preventDefault();
      const frame = frames.find(f => f.id === eraserRef.current.frameId);
      if (!frame || !overlayEl) return;
      const p = getCanvasPoint(e, overlayEl, frame);
      eraseAtPoint(eraserRef.current.frameId, frame, eraserRef.current.layerId, p.x, p.y, eraserSize / 2);
      return;
    }
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

    // ─── Apple Pencil 고해상도 입력 보정 ─────────────────────────────
    // 브라우저는 240Hz 펜 좌표를 60Hz로 합쳐서 pointermove 한 번으로 전달.
    // getCoalescedEvents() 로 원본 좌표를 다 꺼내서 그려야 빠른 stroke 가
    // 끊김 없이 잡힌다. (Native event 가 있을 때만 — React 합성 이벤트는
    // nativeEvent 안에서 꺼내야 함)
    const native = e.nativeEvent || e;
    const coalesced = (typeof native.getCoalescedEvents === 'function')
      ? native.getCoalescedEvents()
      : null;
    const events = (coalesced && coalesced.length > 0) ? coalesced : [native];

    const s = currentStrokeRef.current;

    // 먼저 이번 프레임의 모든 포인트를 수집한다
    for (const ev of events) {
      const p = getCanvasPoint(ev, overlayEl, frame);
      s.points.push(p);
    }

    // 커밋된 비트맵을 다시 그린 뒤, 현재 stroke 전체를 하나의 path로 그린다.
    // (세그먼트별 개별 stroke() 방식은 round cap 겹침으로 불투명도가 중첩돼
    //  원들이 보이는 문제가 생기므로, 전체 경로를 단일 stroke()로 처리한다.)
    const fref = frameRefs.current[drawingRef.current.frameId];
    if (fref) {
      fref.redraw();
      const mc = fref.getMainCanvas();
      if (mc) renderStrokeToCtx(mc.getContext('2d'), s, 0);
    }
  };

  const handlePointerUp = (e, overlayEl) => {
    if (activeTool === 'lasso') { handleLassoPointerUp(e, overlayEl); return; }
    if (activeTool === 'eraser') {
      if (e.pointerType === 'touch') {
        activeTouchPointersRef.current.delete(e.pointerId);
        // 지우개 툴에서도 two-finger tap → undo 트리거
        if (activeTouchPointersRef.current.size === 1 && twoFingerTapRef.current.active && !twoFingerTapRef.current.moved) {
          twoFingerTapRef.current = { active: false, startMap: null, moved: false };
          undoLastStroke();
          panStateRef.current = null;
          return;
        }
        if (activeTouchPointersRef.current.size === 0) twoFingerTapRef.current = { active: false, startMap: null, moved: false };
        if (activeTouchPointersRef.current.size < 2) panStateRef.current = null;
      }
      setEraserCursor(null);
      if (!eraserRef.current.active) return;
      const { frameId, layerId, erasedSet } = eraserRef.current;
      eraserRef.current = { active: false, frameId: null, layerId: null, erasedSet: new Set() };
      if (erasedSet.size > 0) {
        const store = ensureLayerStore(frameId, layerId);
        store.history.push({ type: 'erase', layerId, strokes: [...erasedSet] });
        requestAutosave();
      }
      return;
    }
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
    const stored = { points: simplified, size: liveStroke.size, opacity: liveStroke.opacity, color: liveStroke.color, bbox: computeBbox(simplified), hidden: false };
    const store = ensureLayerStore(drawState.frameId, drawState.layerId);
    if (!store.byBlock[ownerId]) store.byBlock[ownerId] = [];
    store.byBlock[ownerId].push(stored);
    store.history.push({ layerId: drawState.layerId, blockId: ownerId });
    const entry = ensureBlockBitmap(drawState.frameId, drawState.layerId, ownerBlock, frame.canvasWidth, stored.bbox.maxY);
    renderStrokeToCtx(entry.ctx, stored, BITMAP_Y_PADDING);
    requestAutosave();
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
  //  GRADIENT — per-block grayscale gradient (#FFFFFF ↔ #000000)
  //  Figma-style: two endpoints in normalized (0..1) coords + sorted stops.
  // ===================================================================
  const mutateBlockGradient = useCallback((blockId, mutator) => {
    setFrames(arr => arr.map(f => f.id !== selectedFrameId ? f : ({
      ...f, blocks: f.blocks.map(b => {
        if (b.id !== blockId) return b;
        const next = mutator(b.gradient);
        if (next === undefined) return b;          // no change
        if (next === null) {
          const { gradient, ...rest } = b;          // remove gradient
          return rest;
        }
        return { ...b, gradient: next };
      }),
    })));
  }, [selectedFrameId]);

  const addGradient = useCallback((blockId) => {
    mutateBlockGradient(blockId, g => g || makeDefaultGradient());
    setEditingGradientBlockId(blockId);
  }, [mutateBlockGradient]);

  const removeGradient = useCallback((blockId) => {
    mutateBlockGradient(blockId, () => null);
    setEditingGradientBlockId(curr => curr === blockId ? null : curr);
  }, [mutateBlockGradient]);

  const toggleEditGradient = useCallback((blockId) => {
    setEditingGradientBlockId(curr => curr === blockId ? null : blockId);
  }, []);

  const addGradientStop = useCallback((blockId) => {
    mutateBlockGradient(blockId, g => {
      if (!g) return g;
      const sorted = [...g.stops].sort((a, b) => a.offset - b.offset);
      // find the biggest gap between existing stops to place the new one
      let bestGap = -1, bestPos = 0.5, bestLeft = sorted[0]?.value ?? 128, bestRight = sorted[0]?.value ?? 128;
      for (let i = 0; i < sorted.length - 1; i++) {
        const gap = sorted[i + 1].offset - sorted[i].offset;
        if (gap > bestGap) { bestGap = gap; bestPos = (sorted[i].offset + sorted[i + 1].offset) / 2; bestLeft = sorted[i].value; bestRight = sorted[i + 1].value; }
      }
      const newStop = { id: newId(), offset: clamp01(bestPos), value: clampGray((bestLeft + bestRight) / 2) };
      return { ...g, stops: [...sorted, newStop].sort((a, b) => a.offset - b.offset) };
    });
  }, [mutateBlockGradient]);

  const removeGradientStop = useCallback((blockId, stopIndex) => {
    mutateBlockGradient(blockId, g => {
      if (!g) return g;
      if (g.stops.length <= 2) return g;            // keep at least 2 stops
      const sorted = [...g.stops].sort((a, b) => a.offset - b.offset);
      sorted.splice(stopIndex, 1);
      return { ...g, stops: sorted };
    });
  }, [mutateBlockGradient]);

  const updateGradientStop = useCallback((blockId, stopIndex, patch) => {
    mutateBlockGradient(blockId, g => {
      if (!g) return g;
      const sorted = [...g.stops].sort((a, b) => a.offset - b.offset);
      const cur = sorted[stopIndex];
      if (!cur) return g;
      const next = { ...cur };
      if (patch.offset != null) next.offset = clamp01(patch.offset);
      if (patch.value  != null) next.value  = clampGray(patch.value);
      sorted[stopIndex] = next;
      return { ...g, stops: sorted };
    });
  }, [mutateBlockGradient]);

  const swapGradientEnds = useCallback((blockId) => {
    mutateBlockGradient(blockId, g => {
      if (!g) return g;
      return {
        ...g,
        start: g.end,
        end: g.start,
        // also mirror stops so the visual gradient stays the same direction
        stops: g.stops.map(s => ({ ...s, offset: 1 - s.offset })).sort((a, b) => a.offset - b.offset),
      };
    });
  }, [mutateBlockGradient]);

  // ---------- gradient handle pointer handling (Figma-style canvas drag) ----------
  const handleGradientHandlePointerDown = useCallback((e, frameId, blockId, which) => {
    e.preventDefault();
    e.stopPropagation();
    const target = e.currentTarget;
    try { target.setPointerCapture(e.pointerId); } catch (_) {}
    gradientDragRef.current = { frameId, blockId, which, pointerId: e.pointerId, target };
  }, []);

  const handleGradientHandlePointerMove = useCallback((e) => {
    const drag = gradientDragRef.current;
    if (!drag || drag.pointerId !== e.pointerId) return;
    e.preventDefault();
    e.stopPropagation();
    const frame = framesRef.current.find(f => f.id === drag.frameId);
    if (!frame) return;
    const block = frame.blocks.find(b => b.id === drag.blockId);
    if (!block) return;

    const frameEl = canvasAreaRef.current?.querySelector(`[data-frame-id="${drag.frameId}"]`);
    const stageEl = frameEl?.querySelector('.conti-frame-stage');
    if (!stageEl) return;
    const rect = stageEl.getBoundingClientRect();
    if (rect.width === 0 || rect.height === 0) return;

    const totalH = frame.blocks.reduce((s, x) => s + x.height, 0);
    const scaleX = frame.canvasWidth / rect.width;
    const scaleY = totalH / rect.height;
    const xInStage = (e.clientX - rect.left) * scaleX;
    const yInStage = (e.clientY - rect.top)  * scaleY;

    let top = 0;
    for (const x of frame.blocks) { if (x.id === block.id) break; top += x.height; }

    const ml = block.type === 'cut' ? (block.marginLeft ?? frame.sideMargin) : 0;
    const mr = block.type === 'cut' ? (block.marginRight ?? frame.sideMargin) : 0;
    const bw = block.type === 'cut' ? Math.max(10, frame.canvasWidth - ml - mr) : frame.canvasWidth;

    const nx = clamp01((xInStage - ml) / bw);
    const ny = clamp01((yInStage - top) / Math.max(1, block.height));

    setFrames(arr => arr.map(f => f.id !== drag.frameId ? f : ({
      ...f, blocks: f.blocks.map(b => {
        if (b.id !== drag.blockId || !b.gradient) return b;
        return { ...b, gradient: { ...b.gradient, [drag.which]: { x: nx, y: ny } } };
      }),
    })));
  }, []);

  const handleGradientHandlePointerUp = useCallback((e) => {
    const drag = gradientDragRef.current;
    if (!drag || drag.pointerId !== e.pointerId) return;
    try { drag.target?.releasePointerCapture?.(drag.pointerId); } catch (_) {}
    gradientDragRef.current = null;
  }, []);

  // ESC closes gradient edit mode
  useEffect(() => {
    if (editingGradientBlockId == null) return;
    const onKey = (e) => { if (e.key === 'Escape') setEditingGradientBlockId(null); };
    window.addEventListener('keydown', onKey);
    return () => window.removeEventListener('keydown', onKey);
  }, [editingGradientBlockId]);

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
    const lasso = lassoRef.current;
    // 올가미 내부에서 transform 히스토리가 있으면 lasso undo 우선
    if (['selected','dragging','resizing','rotating'].includes(lasso.phase) &&
        lasso.transformHistory && lasso.transformHistory.length > 0) {
      const prevTransform = lasso.transformHistory.pop();
      lasso.transform = prevTransform;
      renderSelectionOverlay(lasso.frameId);
      return;
    }
    if (!selectedFrame || lasso.phase !== 'idle') return;
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
    requestAutosave();
  };

  const clearAll = () => {
    if (!selectedFrame) return;
    if (lassoRef.current.phase !== 'idle' && lassoRef.current.frameId === selectedFrameId)
      cancelLassoSelection(selectedFrameId, selectedFrame);
    if (!window.confirm(`"${selectedFrame.name}"의 모든 드로잉을 지웁니다. 계속하시겠습니까?`)) return;
    const fStore = strokesByFrameRef.current[selectedFrameId] || {};
    for (const ls of Object.values(fStore)) { ls.byBlock = {}; ls.bitmaps = {}; ls.history = []; }
    frameRefs.current[selectedFrameId]?.redraw();
    requestAutosave();
  };

  // ===================================================================
  //  PROJECT SAVE / LOAD logic
  // ===================================================================

  // 현재 작업 상태를 통째로 직렬화 가능한 객체로 변환한다.
  // bitmap (canvas) 과 history (undo stack) 는 저장하지 않고, 불러올 때 strokes 로부터 다시 만든다.
  const serializeProject = useCallback(() => {
    const strokes = {};
    const ref = strokesByFrameRef.current || {};
    for (const fid of Object.keys(ref)) {
      const layerMap = ref[fid] || {};
      const layerOut = {};
      let hasAny = false;
      for (const lid of Object.keys(layerMap)) {
        const ls = layerMap[lid];
        if (!ls?.byBlock) continue;
        const blocksOut = {};
        let layerHasAny = false;
        for (const bid of Object.keys(ls.byBlock)) {
          const arr = ls.byBlock[bid] || [];
          if (arr.length === 0) continue;
          // hidden / bbox 는 저장하지 않는다 — bbox 는 load 시 computeBbox 로 재생성, hidden 은 false 가 디폴트
          // hidden 스트로크는 지워진 것으로 간주하여 저장에서 제외
          const visibleStrokes = arr.filter(s => !s.hidden);
          if (visibleStrokes.length === 0) continue;
          blocksOut[bid] = visibleStrokes.map(s => ({
            points: s.points.map(p => ({ x: p.x, y: p.y })),
            size: s.size,
            opacity: s.opacity,
            color: s.color || '#0F0F0F',
          }));
          layerHasAny = true;
        }
        if (layerHasAny) { layerOut[lid] = blocksOut; hasAny = true; }
      }
      if (hasAny) strokes[fid] = layerOut;
    }
    return {
      frames: frames.map(f => ({
        id: f.id,
        name: f.name,
        canvasWidth: f.canvasWidth,
        sideMargin: f.sideMargin,
        activeLayerId: f.activeLayerId,
        blocks: f.blocks.map(b => ({ ...b })),
        layers: f.layers.map(l => ({ ...l })),
      })),
      selectedFrameId,
      bubblesByLayer: JSON.parse(JSON.stringify(bubblesByLayer)),
      typoPresets: typoPresets.map(p => ({ ...p })),
      strokes,
    };
  }, [frames, selectedFrameId, bubblesByLayer, typoPresets]);

  // 메타데이터 (목록에 보여지는 통계)
  const computeProjectMeta = useCallback((data) => {
    let cuts = 0, strokes = 0, bubbles = 0;
    for (const f of data.frames || []) {
      for (const b of (f.blocks || [])) if (b.type === 'cut') cuts++;
    }
    for (const fStrokes of Object.values(data.strokes || {})) {
      for (const layerStrokes of Object.values(fStrokes || {})) {
        for (const arr of Object.values(layerStrokes || {})) strokes += (arr?.length || 0);
      }
    }
    for (const arr of Object.values(data.bubblesByLayer || {})) bubbles += (arr?.length || 0);
    return { frames: (data.frames || []).length, cuts, strokes, bubbles };
  }, []);

  // 페이로드를 받아서 모든 state / ref 를 갈아끼운다. bitmap 재생성은 useEffect 에서 처리한다.
  const deserializeProject = useCallback((data) => {
    const v = validatePayload(data);
    if (!v.ok) return v;

    // 1) ID 카운터를 끌어올려서 신규 ID 가 기존과 충돌하지 않게 한다
    bumpIdTo(findMaxIdInPayload(data));

    // 2) strokes ref 를 새 데이터로 교체 (기존 bitmaps / history 는 버린다)
    const newStore = {};
    for (const fid of Object.keys(data.strokes || {})) {
      const layerMap = data.strokes[fid] || {};
      const numericFid = Number(fid);
      newStore[numericFid] = {};
      for (const lid of Object.keys(layerMap)) {
        const blocksOut = {};
        for (const bid of Object.keys(layerMap[lid] || {})) {
          const arr = layerMap[lid][bid] || [];
          blocksOut[bid] = arr.map(s => {
            const pts = (s.points || []).map(p => ({ x: p.x, y: p.y }));
            return {
              points: pts,
              size: s.size,
              opacity: s.opacity,
              color: s.color || '#0F0F0F',
              bbox: computeBbox(pts.length ? pts : [{ x: 0, y: 0 }]),
              hidden: false,
            };
          });
        }
        const numericLid = Number(lid);
        newStore[numericFid][numericLid] = { byBlock: blocksOut, bitmaps: {}, history: [] };
      }
    }
    strokesByFrameRef.current = newStore;

    // 3) bubble layer key 를 numeric 으로 정규화
    const newBubbles = {};
    for (const lid of Object.keys(data.bubblesByLayer || {})) {
      newBubbles[Number(lid)] = (data.bubblesByLayer[lid] || []).map(b => ({ ...b }));
    }

    // 4) lasso / drawing 상태 초기화
    lassoRef.current = {
      phase: 'idle', frameId: null, layerId: null,
      lassoPoints: [], selectedItems: [], bbox: null,
      transform: { tx: 0, ty: 0, scaleX: 1, scaleY: 1, angle: 0, flipH: false, flipV: false },
      dragStart: null, origTransform: null, dragHandle: null, origHandleDist: null,
      transformHistory: [],
    };
    drawingRef.current = null;
    currentStrokeRef.current = null;
    setHasSelection(false);
    setSelectionPhase('idle');
    setSelectedBubble(null);

    // 5) 새 frame 의 getLayerBitmap 클로저를 미리 등록
    getLayerBitmapRef.current = {};
    for (const f of (data.frames || [])) {
      const fid = f.id;
      getLayerBitmapRef.current[fid] = (layerId, blockId) => {
        const fStore = strokesByFrameRef.current[fid];
        return fStore?.[layerId]?.bitmaps[blockId] || null;
      };
    }

    // 6) state 갈아끼우기
    const newFrames = data.frames.map(f => ({
      ...f,
      blocks: (f.blocks || []).map(b => ({ ...b })),
      layers: (f.layers || []).map(l => ({ ...l })),
    }));
    const targetFrameId = (newFrames.find(f => f.id === data.selectedFrameId) ? data.selectedFrameId : newFrames[0].id);
    setFrames(newFrames);
    setSelectedFrameId(targetFrameId);
    setBubblesByLayer(newBubbles);
    if (Array.isArray(data.typoPresets) && data.typoPresets.length > 0) {
      setTypoPresets(data.typoPresets.map(p => ({ ...p })));
    }

    // 7) bitmap rebuild 트리거 — useEffect 가 새 frames 와 함께 처리한다
    autosaveLockRef.current = true; // load 직후 autosave 가 다시 실행되지 않게 잠금 (잠깐)
    setLoadGen(g => g + 1);

    return { ok: true };
  }, []);

  // load 직후 모든 frame / layer / block 의 bitmap 을 다시 만든다.
  useEffect(() => {
    if (loadGen === 0) return;
    // setFrames 가 반영된 시점이라 frames 가 새 데이터 — 그걸 기준으로 rebuild
    for (const f of frames) {
      for (const layer of f.layers) {
        if (layer.type !== 'raster') continue;
        ensureLayerStore(f.id, layer.id);
        for (const block of f.blocks) rebuildBlockBitmap(f.id, layer.id, block, f.canvasWidth);
      }
    }
    // 다음 tick 에 redraw — canvas useLayoutEffect 가 먼저 사이즈 잡고 실행되도록
    const t = setTimeout(() => {
      for (const f of frames) frameRefs.current[f.id]?.redraw();
      // load 잠금 해제
      autosaveLockRef.current = false;
    }, 30);
    return () => clearTimeout(t);
  }, [loadGen, frames, ensureLayerStore, rebuildBlockBitmap]);

  // 자동 저장 트리거 (디바운스)
  const requestAutosave = useCallback(() => {
    if (autosaveLockRef.current) return;
    setSaveStatus('dirty');
    if (autosaveTimerRef.current) clearTimeout(autosaveTimerRef.current);
    autosaveTimerRef.current = setTimeout(async () => {
      if (autosaveLockRef.current) return;
      setSaveStatus('saving');
      try {
        const data = serializeProject();
        const meta = computeProjectMeta(data);
        const r = await ProjectStorage.setAutosave({
          name: currentProjectName || '자동 저장본',
          savedAt: Date.now(),
          appVersion: APP_VERSION,
          schemaVersion: SCHEMA_VERSION,
          meta,
          payload: data,
          // 현재 명시적으로 저장된 프로젝트와 연결되어 있으면 같이 기록 (load 시 컨텍스트 유지)
          linkedProjectId: currentProjectId || null,
        });
        if (r?.ok) {
          if (r.backend) setStorageBackend(r.backend);
          setSaveStatus('saved');
          setLastSaveAt(Date.now());
          if (savedFlashTimerRef.current) clearTimeout(savedFlashTimerRef.current);
          savedFlashTimerRef.current = setTimeout(() => setSaveStatus('idle'), 2500);
        } else {
          setSaveStatus('error');
        }
      } catch (_) { setSaveStatus('error'); }
    }, 1500);
  }, [serializeProject, computeProjectMeta, currentProjectName, currentProjectId]);

  // useCallback hooks 등에서 stale closure 없이 호출할 수 있게 ref 동기화
  useEffect(() => { requestAutosaveRef.current = requestAutosave; }, [requestAutosave]);

  // React state 가 바뀌면 자동 저장 요청 (frames / bubbles / typo)
  useEffect(() => {
    if (autosaveLockRef.current) return;
    requestAutosave();
  }, [frames, bubblesByLayer, typoPresets, requestAutosave]);

  // 마운트 시 자동 저장본을 1회 검사해서 복원 여부를 묻는다
  useEffect(() => {
    if (autosaveCheckedRef.current) return;
    autosaveCheckedRef.current = true;
    let cancelled = false;
    let restoredViaDeserialize = false;
    (async () => {
      try {
        const auto = await ProjectStorage.getAutosave();
        if (cancelled || !auto?.payload) return;
        // 비어있는 (frame 1개, stroke 0, bubble 0) 자동저장은 무시
        const meta = auto.meta || {};
        const isEmpty = (meta.frames ?? 0) <= 1 && (meta.strokes ?? 0) === 0 && (meta.bubbles ?? 0) === 0;
        if (isEmpty) return;
        const when = formatRelativeTime(auto.savedAt);
        const summary = `자동 저장된 작업이 있습니다.\n\n` +
          `${auto.name || '자동 저장본'}\n저장: ${when}\n` +
          `frames ${meta.frames ?? '?'} · cuts ${meta.cuts ?? '?'} · ` +
          `strokes ${meta.strokes ?? '?'} · bubbles ${meta.bubbles ?? '?'}\n\n` +
          `이전 작업으로 복원하시겠습니까?`;
        if (window.confirm(summary)) {
          const r = deserializeProject(auto.payload);
          if (r.ok) {
            restoredViaDeserialize = true; // deserializeProject 가 자체적으로 lock 을 관리함
            // 자동저장이 저장된 프로젝트와 연결되어 있으면 컨텍스트 복원
            if (auto.linkedProjectId) {
              const linked = await ProjectStorage.getProject(auto.linkedProjectId);
              if (linked) {
                setCurrentProjectId(auto.linkedProjectId);
                setCurrentProjectName(linked.name || auto.name || '');
              } else {
                setCurrentProjectName(auto.name || '');
              }
            } else {
              setCurrentProjectName(auto.name || '');
            }
            setLastSaveAt(auto.savedAt || 0);
          }
        }
      } catch (_) {}
      finally {
        // deserializeProject 가 lock 을 관리하지 않은 경우 여기서 풀어준다
        if (!cancelled && !restoredViaDeserialize) {
          autosaveLockRef.current = false;
        }
      }
    })();
    return () => { cancelled = true; };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  // ===== 명시적 저장 / 불러오기 =====

  const handleSaveAsNewProject = useCallback(async (name) => {
    setSaveStatus('saving');
    const data = serializeProject();
    const meta = computeProjectMeta(data);
    const id = `proj_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`;
    const record = {
      id,
      name,
      savedAt: Date.now(),
      appVersion: APP_VERSION,
      schemaVersion: SCHEMA_VERSION,
      meta,
      payload: data,
    };
    const r = await ProjectStorage.saveProject(record);
    if (r.ok) {
      if (r.backend) setStorageBackend(r.backend);
      setCurrentProjectId(id);
      setCurrentProjectName(name);
      setSaveStatus('saved');
      setLastSaveAt(Date.now());
      if (savedFlashTimerRef.current) clearTimeout(savedFlashTimerRef.current);
      savedFlashTimerRef.current = setTimeout(() => setSaveStatus('idle'), 2500);
    } else {
      setSaveStatus('error');
    }
    return r;
  }, [serializeProject, computeProjectMeta]);

  const handleSaveCurrentProject = useCallback(async () => {
    if (!currentProjectId) {
      // 새 이름으로 저장
      const name = window.prompt('프로젝트 이름을 입력해주세요', currentProjectName || `프로젝트 ${new Date().toLocaleString('ko-KR')}`);
      if (!name?.trim()) return { ok: false, error: '이름이 비어있습니다' };
      return handleSaveAsNewProject(name.trim());
    }
    setSaveStatus('saving');
    const data = serializeProject();
    const meta = computeProjectMeta(data);
    const record = {
      id: currentProjectId,
      name: currentProjectName,
      savedAt: Date.now(),
      appVersion: APP_VERSION,
      schemaVersion: SCHEMA_VERSION,
      meta,
      payload: data,
    };
    const r = await ProjectStorage.saveProject(record);
    if (r.ok) {
      if (r.backend) setStorageBackend(r.backend);
      setSaveStatus('saved');
      setLastSaveAt(Date.now());
      if (savedFlashTimerRef.current) clearTimeout(savedFlashTimerRef.current);
      savedFlashTimerRef.current = setTimeout(() => setSaveStatus('idle'), 2500);
    } else {
      setSaveStatus('error');
    }
    return r;
  }, [currentProjectId, currentProjectName, serializeProject, computeProjectMeta, handleSaveAsNewProject]);

  const handleLoadProject = useCallback(async (id) => {
    const rec = await ProjectStorage.getProject(id);
    if (!rec?.payload) return { ok: false, error: '프로젝트를 찾을 수 없습니다' };
    const r = deserializeProject(rec.payload);
    if (r.ok) {
      setCurrentProjectId(id);
      setCurrentProjectName(rec.name || '');
      setLastSaveAt(rec.savedAt || 0);
      setSaveStatus('idle');
    }
    return r;
  }, [deserializeProject]);

  const handleDeleteProject = useCallback(async (id) => {
    await ProjectStorage.deleteProject(id);
    if (currentProjectId === id) { setCurrentProjectId(null); /* 이름은 유지 */ }
  }, [currentProjectId]);

  const handleRenameProject = useCallback(async (id, newName) => {
    const rec = await ProjectStorage.getProject(id);
    if (!rec) return;
    rec.name = newName;
    await ProjectStorage.saveProject(rec);
    if (currentProjectId === id) setCurrentProjectName(newName);
  }, [currentProjectId]);

  // 모든 강제 상태를 새것으로 리셋
  const handleNewProject = useCallback(async () => {
    autosaveLockRef.current = true;
    // strokes, lasso, drawing 정리
    strokesByFrameRef.current = {};
    getLayerBitmapRef.current = {};
    lassoRef.current = {
      phase: 'idle', frameId: null, layerId: null,
      lassoPoints: [], selectedItems: [], bbox: null,
      transform: { tx: 0, ty: 0, scaleX: 1, scaleY: 1, angle: 0, flipH: false, flipV: false },
      dragStart: null, origTransform: null, dragHandle: null, origHandleDist: null,
      transformHistory: [],
    };
    drawingRef.current = null;
    currentStrokeRef.current = null;
    clipboardRef.current = null;
    setHasSelection(false); setHasClipboard(false); setSelectionPhase('idle'); setSelectedBubble(null);

    const fresh = makeStarterFrame('Frame 1');
    setFrames([fresh]);
    setSelectedFrameId(fresh.id);
    setBubblesByLayer({});
    setTypoPresets(DEFAULT_TYPO_PRESETS);
    setCurrentProjectId(null);
    setCurrentProjectName('');
    setLastSaveAt(0);
    setSaveStatus('idle');

    // 자동 저장본도 리셋
    await ProjectStorage.clearAutosave();

    // 새 frame 의 bitmap 셋업을 위해 loadGen 트리거
    setLoadGen(g => g + 1);
    return { ok: true };
  }, []);

  // JSON 파일로 내보내기
  const handleExport = useCallback(() => {
    try {
      const data = serializeProject();
      const meta = computeProjectMeta(data);
      const record = {
        id: currentProjectId || `export_${Date.now()}`,
        name: currentProjectName || '제목 없음',
        savedAt: Date.now(),
        appVersion: APP_VERSION,
        schemaVersion: SCHEMA_VERSION,
        meta,
        payload: data,
      };
      const safeName = (record.name || 'project').replace(/[^\w가-힣\-_. ]+/g, '_').slice(0, 60);
      const ts = new Date().toISOString().slice(0, 19).replace(/[:T]/g, '-');
      const filename = `${safeName}_${ts}.conti.json`;
      const ok = triggerDownload(filename, JSON.stringify(record));
      return ok ? { ok: true } : { ok: false, error: '다운로드 실패' };
    } catch (e) { return { ok: false, error: e?.message || '내보내기 실패' }; }
  }, [serializeProject, computeProjectMeta, currentProjectId, currentProjectName]);

  // JSON 파일에서 불러오기
  const handleImportFile = useCallback(async (file) => {
    try {
      const text = await readFileAsText(file);
      let parsed;
      try { parsed = JSON.parse(text); }
      catch (_) { return { ok: false, error: 'JSON 파싱 실패 — 올바른 .conti.json 파일이 맞는지 확인해주세요' }; }
      const data = parsed?.payload || parsed?.data || parsed;
      const r = deserializeProject(data);
      if (r.ok) {
        setCurrentProjectId(null); // 가져온 파일은 아직 IDB 에 저장되지 않은 상태로 본다
        setCurrentProjectName(parsed.name || file.name.replace(/\.(conti\.)?json$/i, ''));
        setLastSaveAt(0);
        setSaveStatus('idle');
      }
      return r;
    } catch (e) { return { ok: false, error: e?.message || '가져오기 실패' }; }
  }, [deserializeProject]);

  // ---- PSD 내보내기 (클립스튜디오 호환) ----
  // 클립스튜디오의 .clip 컨테이너는 비공개 포맷(Celsys 자체 BlockData 픽셀 압축)이라
  // 브라우저에서 직접 만들 수 없다. 대신 CSP 가 1급으로 지원하는 PSD/PSB 로 내보낸다.
  // - target: 'current' = 현재 선택된 프레임만 / 'all' = 모든 프레임을 zip 으로
  const handleExportPSD = useCallback(async (target = 'current') => {
    try {
      const baseName = sanitizeFilename(currentProjectName || '제목 없음', 'conti');

      if (target === 'current') {
        if (!selectedFrame) return { ok: false, error: '선택된 프레임이 없습니다' };
        const { bytes, ext } = await buildFramePsd(
          selectedFrame, strokesByFrameRef.current, bubblesByLayer, typoPresets
        );
        const fname = `${baseName}_${sanitizeFilename(selectedFrame.name, 'frame')}.${ext}`;
        triggerBytesDownload(fname, bytes);
        return { ok: true, filename: fname };
      }

      // all → zip
      if (!Array.isArray(frames) || frames.length === 0) {
        return { ok: false, error: '내보낼 프레임이 없습니다' };
      }
      const { zipSync, strToU8 } = await loadFflate();
      const entries = {};
      // 동시에 빌드하면 메모리/CPU 부담 — 직렬로 처리
      for (let i = 0; i < frames.length; i++) {
        const f = frames[i];
        const { bytes, ext } = await buildFramePsd(
          f, strokesByFrameRef.current, bubblesByLayer, typoPresets
        );
        const idx = String(i + 1).padStart(2, '0');
        const name = `${idx}_${sanitizeFilename(f.name, `frame_${i + 1}`)}.${ext}`;
        entries[name] = bytes;
      }
      // README 도 같이 넣어준다 — CSP 사용자가 처음 받으면 헷갈릴 수 있어서
      const readme =
        `이 zip 은 콘티 프로그램에서 내보낸 PSD 파일 모음입니다.\n\n` +
        `사용법:\n` +
        `  1. 각 .psd / .psb 파일을 클립스튜디오에서 [파일 > 열기] 로 엽니다.\n` +
        `  2. 레이어 / 레이어 이름 / 가시성 / 투명도가 그대로 유지됩니다.\n` +
        `  3. [가이드] 그룹에는 컷 경계와 양옆 마진이 들어 있습니다 (기본 숨김).\n` +
        `  4. 말풍선/텍스트는 래스터화되어 있습니다 (CSP 도 PSD export 시 동일 동작).\n\n` +
        `참고: .clip 포맷은 비공개 포맷이라 직접 만들 수 없어 PSD/PSB 로 내보냅니다.\n` +
        `CSP 가 공식 권장하는 교환 포맷입니다.\n`;
      entries['README.txt'] = strToU8(readme);

      const zipped = zipSync(entries, { level: 6 });
      const fname = `${baseName}_psd.zip`;
      triggerBytesDownload(fname, zipped, 'application/zip');
      return { ok: true, filename: fname, count: frames.length };
    } catch (e) {
      console.error('[PSD export]', e);
      return { ok: false, error: e?.message || 'PSD 내보내기 실패' };
    }
  }, [selectedFrame, frames, bubblesByLayer, typoPresets, currentProjectName]);


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
            <div className="conti-brand-name">{currentProjectName || '콘티 프로그램'}</div>
            <div className="conti-brand-version">
              {APP_VERSION}
              {saveStatus !== 'idle' && (
                <>
                  {' · '}
                  <span className={`conti-save-status ${saveStatus}`}>
                    <span className="save-dot" />
                    {saveStatus === 'saving' && '저장중'}
                    {saveStatus === 'saved' && '저장됨'}
                    {saveStatus === 'error' && '저장 실패'}
                    {saveStatus === 'dirty' && '미저장'}
                  </span>
                </>
              )}
              {saveStatus === 'idle' && lastSaveAt > 0 && (
                <>{' · '}<span style={{ color: 'var(--muted)' }}>{formatRelativeTime(lastSaveAt)} 저장</span></>
              )}
            </div>
          </div>
        </div>

        {/* Tool selector (raster only) */}
        {activeLayerType === 'raster' && (
          <div className="conti-tool">
            <button className={`conti-icon-btn ${activeTool === 'pen' ? 'active' : ''}`} onClick={() => switchTool('pen')}>✏ pen</button>
            <button className={`conti-icon-btn ${activeTool === 'lasso' ? 'active' : ''}`} onClick={() => switchTool('lasso')}>⬡ lasso</button>
            <button className={`conti-icon-btn ${activeTool === 'eraser' ? 'active' : ''}`} onClick={() => switchTool('eraser')}>◻ eraser</button>
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

        {/* Eraser options */}
        {activeLayerType === 'raster' && activeTool === 'eraser' && (
          <div className="conti-tool">
            <span className="conti-tool-label">size</span>
            <input type="range" min="4" max="200" step="1" value={eraserSize}
              onChange={e => setEraserSize(parseInt(e.target.value, 10))} />
            <input className="conti-num" type="number" min="4" max="200" step="1" value={eraserSize}
              onChange={e => { const v = parseInt(e.target.value, 10); if (Number.isFinite(v)) setEraserSize(Math.max(4, Math.min(200, v))); }} />
            <span className="conti-tool-unit">px</span>
          </div>
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
              disabled={!selectedFrame || (lassoRef.current.phase !== 'idle' && !(lassoRef.current.transformHistory?.length > 0))}>↶ undo</button>
          )}
          <button className="conti-icon-btn" onClick={() => setSaveDialogOpen(true)}
            title="프로젝트 저장 / 불러오기">📁 project</button>
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
                <NumberInputWithDraft
                  min={200} max={2000} step={2}
                  value={selectedFrame.canvasWidth}
                  onCommit={raw => { const v = parseInt(raw, 10); if (Number.isFinite(v)) updateFrameDim(selectedFrameId, 'canvasWidth', Math.max(200, Math.min(2000, v))); }}
                />
              </div>
              <div className="conti-config-row">
                <label>side margin</label>
                <NumberInputWithDraft
                  min={0} max={500} step={2}
                  value={selectedFrame.sideMargin}
                  onCommit={raw => { const v = parseInt(raw, 10); if (Number.isFinite(v)) updateFrameDim(selectedFrameId, 'sideMargin', Math.max(0, Math.min(500, v))); }}
                />
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
                    <NumberInputWithDraft
                      className="typo-system-size"
                      min={6} max={200} step={1}
                      value={p.size}
                      onCommit={raw => {
                        const v = Math.max(6, Math.min(200, parseInt(raw, 10) || p.size));
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
                  <button
                    className="del"
                    title="삭제"
                    disabled={typoPresets.length <= 1}
                    onClick={() => setTypoPresets(prev => prev.filter(x => x.id !== p.id))}
                  >×</button>
                </div>
              ))}
            </div>
            <button
              className="conti-add-btn"
              onClick={() => {
                const last = typoPresets[typoPresets.length - 1];
                setTypoPresets(prev => [
                  ...prev,
                  { id: newId(), name: 'New', size: last ? Math.max(6, last.size - 8) : 20, weight: 400 },
                ]);
              }}
            >+ add typo</button>
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
                eraserSize={eraserSize}
                eraserCursor={f.id === selectedFrameId ? eraserCursor : null}
                editingGradientBlockId={f.id === selectedFrameId ? editingGradientBlockId : null}
                onSelect={setSelectedFrameId}
                onPointerDown={handlePointerDown}
                onPointerMove={handlePointerMove}
                onPointerUp={handlePointerUp}
                onBubbleOverlayPointerDown={handleBubbleOverlayPointerDown}
                onBubbleOverlayPointerMove={handleBubbleOverlayPointerMove}
                onBubbleOverlayPointerUp={handleBubbleOverlayPointerUp}
                onGradientHandlePointerDown={handleGradientHandlePointerDown}
                onGradientHandlePointerMove={handleGradientHandlePointerMove}
                onGradientHandlePointerUp={handleGradientHandlePointerUp}
              />
            ))}
          </div>

          {selectedFrame && (
            <div className="conti-status">
              <span className={`dot ${activeLayerType === 'vector' ? 'vector' : activeTool === 'lasso' ? 'lasso' : activeTool === 'eraser' ? 'lasso' : ''}`} />
              <span>{selectedFrame.name}</span>
              <span>·</span>
              <span>{activeLayerType === 'vector' ? `🗨 ${activeLayer?.name}` : activeTool === 'lasso' ? (hasSelection ? '🟥 selected' : 'lasso') : activeTool === 'eraser' ? 'eraser' : 'pen'}</span>
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
                  const isEditingGrad = editingGradientBlockId === b.id;
                  const hasGrad = !!b.gradient;
                  // attach-bottom: row should have flat bottom because another row sits directly under it
                  const mainAttachBottom = isCut || isEditingGrad;
                  const marginAttachBottom = isCut && isEditingGrad;
                  return (
                    <div key={b.id} data-block-id={b.id}>
                      {showAbove && <div style={{ position:'relative',height:3,background:'var(--accent)',borderRadius:2,margin:'0 0 2px 0' }} />}
                      <div className={`conti-block-row${mainAttachBottom ? ' has-margin' : ''} ${dragId === b.id ? 'dragging' : ''} ${b.id === activeBlockId ? 'viewport-active' : ''}`}>
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
                        <NumberInputWithDraft
                          min={50} max={5000} step={50}
                          value={b.height}
                          onCommit={raw => updateBlockHeight(b.id, raw)}
                        />
                        <div className="block-height-stepper">
                          <button className="block-height-btn" title="+50px"
                            onClick={() => updateBlockHeight(b.id, String(b.height + 50))}>▲</button>
                          <button className="block-height-btn" title="-50px"
                            onClick={() => updateBlockHeight(b.id, String(b.height - 50))}>▼</button>
                        </div>
                        <span className="conti-tool-unit mono">px</span>
                        <button
                          className={`block-grad-btn${hasGrad ? ' has' : ''}${isEditingGrad ? ' editing' : ''}`}
                          title={hasGrad ? (isEditingGrad ? '그라데이션 편집 닫기' : '그라데이션 편집') : '그라데이션 추가'}
                          onClick={() => { if (hasGrad) toggleEditGradient(b.id); else addGradient(b.id); }}
                          style={hasGrad ? { background: gradientToCss(b.gradient, 22, 22) || 'transparent' } : null}
                        >
                          {hasGrad ? '' : 'G'}
                        </button>
                        <button className="del" onClick={() => removeBlock(b.id)} title="삭제">×</button>
                      </div>
                      {isCut && (
                        <div className={`conti-block-margin-row${marginAttachBottom ? ' attach-bottom' : ''}${b.id === activeBlockId ? ' viewport-active' : ''}`}>
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
                      {isEditingGrad && b.gradient && (
                        <div className={`conti-block-gradient-row${b.id === activeBlockId ? ' viewport-active' : ''}`}>
                          <div className="grad-header">
                            <span className="grad-label">GRADIENT</span>
                            <div className="grad-bar"
                                 style={{ background: gradientToCss({ ...b.gradient, start: { x: 0, y: 0.5 }, end: { x: 1, y: 0.5 } }, 100, 1) || '#ccc' }} />
                            <button className="grad-mini-btn" title="시작/끝 뒤집기"
                              onClick={() => swapGradientEnds(b.id)}>⇄</button>
                            <button className="grad-mini-btn" title="stop 추가"
                              onClick={() => addGradientStop(b.id)}>+</button>
                            <button className="grad-mini-btn danger" title="그라데이션 제거"
                              onClick={() => removeGradient(b.id)}>✕</button>
                          </div>
                          {[...b.gradient.stops]
                            .map((s, originalIdx) => ({ s, originalIdx }))
                            .sort((a, c) => a.s.offset - c.s.offset)
                            .map(({ s: stop }, sortedIdx) => (
                              <div className="grad-stop-row" key={stop.id ?? sortedIdx}>
                                <span className="grad-swatch" style={{ background: grayToRgbStr(stop.value) }} />
                                <input className="grad-gray-slider" type="range" min="0" max="255" step="1"
                                  value={stop.value}
                                  onChange={e => updateGradientStop(b.id, sortedIdx, { value: Number(e.target.value) })} />
                                <span className="grad-hex mono">{grayToHex(stop.value)}</span>
                                <input className="grad-offset mono" type="number" min="0" max="100" step="1"
                                  value={Math.round(stop.offset * 100)}
                                  onChange={e => updateGradientStop(b.id, sortedIdx, { offset: Number(e.target.value) / 100 })} />
                                <span className="grad-offset-unit mono">%</span>
                                <button className="grad-stop-del"
                                  disabled={b.gradient.stops.length <= 2}
                                  onClick={() => removeGradientStop(b.id, sortedIdx)}
                                  title="stop 삭제">−</button>
                              </div>
                          ))}
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

      <SaveLoadDialog
        open={saveDialogOpen}
        onClose={() => setSaveDialogOpen(false)}
        currentProjectId={currentProjectId}
        currentProjectName={currentProjectName}
        onSaveCurrent={handleSaveCurrentProject}
        onSaveAsNew={handleSaveAsNewProject}
        onLoad={handleLoadProject}
        onDelete={handleDeleteProject}
        onRename={handleRenameProject}
        onNewProject={handleNewProject}
        onExport={handleExport}
        onImportFile={handleImportFile}
        onExportPSD={handleExportPSD}
        hasFrames={frames.length > 0}
        frameCount={frames.length}
        storageBackend={storageBackend}
      />
    </div>
  );
}
