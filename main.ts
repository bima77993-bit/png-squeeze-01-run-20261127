// png-squeeze-01-run-20261127 entry.
// Self-contained Node 22 program (built-in modules only). Reads /input/<id>/image.png
// (1280x720 RGBA stored PNG), writes /output/<id>/image.png losslessly, as small as
// possible. Pipeline: decode -> colour-type/palette screen -> per-row filter choice
// -> optimal-parse DEFLATE (hash-chain match finder + shortest-path DP + dynamic
// Huffman, fixed block splitting). Deterministic: no clock, no env, work-budgeted.
// PNG codec + screen adapted from the kit's program/generator/subject/{png,scale}.mjs
// (make.fun, MIT). The DEFLATE below is original work.
import { inflateSync, deflateSync, constants } from 'node:zlib';
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const W = 1280, H = 720;

// ---------- PNG codec ----------
const SIGNATURE = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
const CHANNELS = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };
const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; t[n] = c; }
  return t;
})();
function crc32(bytes, start = 0, end = bytes.length) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}
function adler32(bytes) {
  let a = 1, b = 0;
  for (let i = 0; i < bytes.length;) {
    const end = Math.min(bytes.length, i + 5552);
    for (; i < end; i++) { a += bytes[i]; b += a; }
    a %= 65521; b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}
const ascii = (s) => Uint8Array.from(s, (ch) => ch.charCodeAt(0));
function pngOf(chunks) {
  let size = SIGNATURE.length;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set(SIGNATURE, 0);
  let at = SIGNATURE.length;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    out.set(ascii(type), at + 4);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}
function ihdrOf(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width); v.setUint32(4, height);
  d[8] = 8; d[9] = colourType;
  return d;
}
function paeth(a, b, c) {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) { for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0); }
  else if (type === 2) { for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]); }
  else if (type === 3) { for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1); }
  else { for (let i = 0; i < n; i++) { const a = i >= bpp ? cur[i - bpp] : 0; const b = prev === null ? 0 : prev[i]; const c = prev !== null && i >= bpp ? prev[i - bpp] : 0; out[i] = cur[i] - paeth(a, b, c); } }
}
function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) { const v = row[i]; s += v < 128 ? v : 256 - v; }
  return s;
}
function decodePng(bytes) {
  if (bytes.length < 8 || SIGNATURE.some((b, i) => bytes[i] !== b)) throw new Error('bad signature');
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8, header = null, palette = null, trns = null;
  const idat = [];
  let ended = false;
  while (at < bytes.length) {
    if (ended) throw new Error('bytes after IEND');
    const len = view.getUint32(at);
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (type === 'IHDR') {
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), colourType: data[9] };
    } else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') ended = true;
  }
  const { width, height, colourType } = header;
  const bpp = CHANNELS[colourType];
  const stride = width * bpp;
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat));
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    const src = y * (stride + 1) + 1;
    const o = y * stride, p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) { for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0); }
    else if (ft === 2) { for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0); }
    else if (ft === 3) { for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1); }
    else { for (let i = 0; i < stride; i++) { const a = i >= bpp ? samples[o + i - bpp] : 0; const b = y > 0 ? samples[p + i] : 0; const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0; samples[o + i] = raw[src + i] + paeth(a, b, c); } }
  }
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) { const g = samples[i]; rgba[d] = rgba[d + 1] = rgba[d + 2] = g; rgba[d + 3] = g === key ? 0 : 255; }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) { rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s]; rgba[d + 3] = samples[s + 1]; }
  } else {
    const entries = palette.length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) { lut[e * 4] = palette[e * 3]; lut[e * 4 + 1] = palette[e * 3 + 1]; lut[e * 4 + 2] = palette[e * 3 + 2]; lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255; }
    for (let i = 0, d = 0; i < n; i++, d += 4) { const e = samples[i]; rgba[d] = lut[e * 4]; rgba[d + 1] = lut[e * 4 + 1]; rgba[d + 2] = lut[e * 4 + 2]; rgba[d + 3] = lut[e * 4 + 3]; }
  }
  return { width, height, rgba };
}

// ---------- Colour-type / palette screen (adapted from the kit scale.mjs) ----------
function wordsOf(rgba) {
  const at = rgba.byteOffset % 4 === 0 ? rgba : rgba.slice();
  return new Uint32Array(at.buffer, at.byteOffset, at.length >>> 2);
}
function analyse(rgba) {
  const n = rgba.length >>> 2;
  const u32 = wordsOf(rgba);
  let opaque = true, grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const c = u32[i];
      const k = counts.get(c);
      if (k === undefined) { if (counts.size === 256) many = true; else counts.set(c, 1); }
      else counts.set(c, k + 1);
    }
  }
  const colours = many ? null : [...counts.keys()].map((c) => {
    const b = new Uint8Array(Uint32Array.of(c).buffer);
    return { rgba: [b[0], b[1], b[2], b[3]], word: c, count: counts.get(c) };
  });
  return { opaque, grey, colours };
}
function transparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}
function samplesOf(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) { out[s] = rgba[d]; out[s + 1] = rgba[d + 3]; }
    else { out[s] = rgba[d]; out[s + 1] = rgba[d + 1]; out[s + 2] = rgba[d + 2]; }
  }
  return out;
}
function paletteOrder(colours, order) {
  const lum = (c) => 299 * c.rgba[0] + 587 * c.rgba[1] + 114 * c.rgba[2];
  return [...colours].sort((x, y) => {
    const ta = x.rgba[3] === 255 ? 1 : 0;
    const tb = y.rgba[3] === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.rgba[3] !== y.rgba[3]) return x.rgba[3] - y.rgba[3];
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
}
function paletteForm(rgba, colours, order) {
  const entries = paletteOrder(colours, order);
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.rgba[0]; plte[i * 3 + 1] = c.rgba[1]; plte[i * 3 + 2] = c.rgba[2];
    if (c.rgba[3] !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.rgba[3]);
  const n = rgba.length >>> 2;
  const u32 = wordsOf(rgba);
  const indices = new Uint8Array(n);
  for (let i = 0; i < n; i++) indices[i] = index.get(u32[i]);
  return { plte, trns, indices };
}
const SCREEN = { level: 6, memLevel: 8, strategy: constants.Z_DEFAULT_STRATEGY };
const BRUTE_CONTEXT = 32768;
const BRUTE_LEVEL = 4;
function pairsOf(row, seen, stamp) {
  let n = 0;
  for (let i = 1; i < row.length; i++) {
    const pair = (row[i - 1] << 8) | row[i];
    if (seen[pair] !== stamp) { seen[pair] = stamp; n++; }
  }
  return n;
}
function filtered(samples, width, height, bpp, choice, raw = new Uint8Array(height * (width * bpp + 1))) {
  const stride = width * bpp;
  const trial = Array.from({ length: 5 }, (_, t) => { const row = new Uint8Array(stride + 1); row[0] = t; return row; });
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - BRUTE_CONTEXT), at);
    let type = 0, best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t].subarray(1));
      let cost;
      if (choice === 'minsum') cost = signedSum(trial[t].subarray(1));
      else if (choice === 'pairs') cost = pairsOf(trial[t].subarray(1), seen, ++stamp);
      else cost = deflateSync(trial[t], before.length === 0 ? { level: BRUTE_LEVEL, memLevel: 9 } : { level: BRUTE_LEVEL, memLevel: 9, dictionary: before }).length;
      if (cost < best) { best = cost; type = t; }
    }
    raw.set(trial[type], at);
  }
  return raw;
}
const FILTERS = {
  palette: [0],
  paletteByLuminance: [0, 'minsum', 'brute'],
  channels: [0, 1, 2, 4, 'minsum', 'pairs', 'brute'],
};
function formsOf(rgba) {
  const { opaque, grey, colours } = analyse(rgba);
  const forms = [];
  if (colours !== null) {
    for (const [order, filters] of [['count', FILTERS.palette], ['luminance', FILTERS.paletteByLuminance]]) {
      const p = paletteForm(rgba, colours, order);
      forms.push({ colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns, filters });
    }
    if (!grey) return forms;
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct, trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct];
  forms.push({ colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns, filters: FILTERS.channels });
  return forms;
}
const chunkBytes = (form) => (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);
function pngOfForm(width, height, form, idat) {
  const chunks = [['IHDR', ihdrOf(width, height, form.colourType)]];
  if (form.plte !== null) chunks.push(['PLTE', form.plte]);
  if (form.trns !== null) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', idat]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngOf(chunks);
}
// Screen all forms x filter choices by zlib level 6; return the winner's form,
// filter choice and filtered data (smallest zlib-6 bytes incl. PLTE/tRNS).
function screen(rgba) {
  let best = null, spare = null;
  for (const form of formsOf(rgba)) {
    const size = H * (W * form.bpp + 1);
    const chunks = chunkBytes(form);
    for (const choice of form.filters) {
      const data = filtered(form.samples, W, H, form.bpp, choice, spare !== null && spare.length === size ? spare : new Uint8Array(size));
      spare = null;
      const bytes = deflateSync(data, SCREEN).length + chunks;
      if (best === null || bytes < best.bytes) {
        if (best !== null) spare = best.data;
        best = { form, choice, data, bytes };
      } else spare = data;
    }
  }
  return best;
}
// oz.mjs — a compact optimal-parse DEFLATE (zopfli-style) in pure JS.
// Hash-chain longest match (positions inserted strictly in order) + 1-match DP
// with Huffman costs + iterative Huffman refinement + fixed block splitting.
// Deterministic: no clock, no env. Pure functions of the input bytes.

const WSIZE = 32768;
const MIN_MATCH = 3;
const MAX_MATCH = 258;
const HASH_BITS = 15;
const HASH_SIZE = 1 << HASH_BITS;
const HASH_MASK = HASH_SIZE - 1;

const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];

function lenCode(len) {
  let lo = 0, hi = 28;
  while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (LEN_BASE[mid] <= len) lo = mid; else hi = mid - 1; }
  return lo;
}
function distCode(dist) {
  let lo = 0, hi = 29;
  while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (DIST_BASE[mid] <= dist) lo = mid; else hi = mid - 1; }
  return lo;
}
function reverseBits(code, len) {
  let r = 0;
  for (let i = 0; i < len; i++) r = (r << 1) | ((code >> i) & 1);
  return r;
}

// ---- Huffman: heap tree -> lengths. The tree is a full binary tree, so the code is
// complete (Kraft == 1) whenever there are >= 2 symbols. No capping here: the caller
// checks maxLen and falls back to a fixed-Huffman block when it exceeds maxBits. ----
function buildHuffman(freq, maxBits) {
  const n = freq.length;
  const lengths = new Uint8Array(n);
  let nn = 0;
  for (let i = 0; i < n; i++) if (freq[i] > 0) nn++;
  if (nn === 0) return { lengths, codes: new Uint32Array(n), maxLen: 0 };
  if (nn === 1) {
    for (let i = 0; i < n; i++) if (freq[i] > 0) { lengths[i] = 1; break; }
    return { lengths, codes: new Uint32Array(n), maxLen: 1 };
  }
  const heap = [];
  const left = new Int32Array(2 * n);
  const right = new Int32Array(2 * n);
  const f = new Float64Array(2 * n);
  for (let i = 0; i < n; i++) f[i] = freq[i];
  const push = (idx) => {
    heap.push(idx);
    let c = heap.length - 1;
    while (c > 0) { const p = (c - 1) >> 1; if (f[heap[p]] <= f[heap[c]]) break; const t = heap[p]; heap[p] = heap[c]; heap[c] = t; c = p; }
  };
  const pop = () => {
    const top = heap[0];
    const last = heap.pop();
    if (heap.length > 0) {
      heap[0] = last;
      let p = 0;
      for (;;) {
        const l = p * 2 + 1, r = l + 1;
        let s = p;
        if (l < heap.length && f[heap[l]] < f[heap[s]]) s = l;
        if (r < heap.length && f[heap[r]] < f[heap[s]]) s = r;
        if (s === p) break;
        const t = heap[p]; heap[p] = heap[s]; heap[s] = t; p = s;
      }
    }
    return top;
  };
  for (let i = 0; i < n; i++) if (freq[i] > 0) push(i);
  let nodes = n;
  while (heap.length > 1) {
    const a = pop(), b = pop();
    left[nodes] = a; right[nodes] = b;
    f[nodes] = f[a] + f[b];
    push(nodes);
    nodes++;
  }
  const root = heap[0];
  const depth = new Int32Array(nodes);
  const stack = [root];
  let maxLen = 0;
  while (stack.length) {
    const v = stack.pop();
    if (v < n) { lengths[v] = depth[v]; if (depth[v] > maxLen) maxLen = depth[v]; }
    else {
      depth[left[v]] = depth[v] + 1; depth[right[v]] = depth[v] + 1;
      stack.push(left[v]); stack.push(right[v]);
    }
  }
  const codes = new Uint32Array(n);
  const blCount = new Int32Array(maxBits + 1);
  for (let i = 0; i < n; i++) if (lengths[i] > 0 && lengths[i] <= maxBits) blCount[lengths[i]]++;
  const nextCode = new Uint32Array(maxBits + 1);
  let code = 0;
  for (let b = 1; b <= maxBits; b++) { code = (code + blCount[b - 1]) << 1; nextCode[b] = code; }
  for (let i = 0; i < n; i++) if (lengths[i] > 0 && lengths[i] <= maxBits) codes[i] = nextCode[lengths[i]]++;
  return { lengths, codes, maxLen };
}

// ---- Bit writer (LSB-first packing) ----
class BitWriter {
  constructor(cap) {
    this.buf = new Uint8Array(cap);
    this.pos = 0;
    this.bitbuf = 0;
    this.bitcnt = 0;
  }
  write(code, len) {
    this.bitbuf |= code << this.bitcnt;
    this.bitcnt += len;
    while (this.bitcnt >= 8) {
      this.buf[this.pos++] = this.bitbuf & 0xff;
      this.bitbuf >>>= 8;
      this.bitcnt -= 8;
    }
  }
  writeRev(code, len) {
    this.write(reverseBits(code, len), len);
  }
  align() {
    if (this.bitcnt > 0) { this.buf[this.pos++] = this.bitbuf & 0xff; this.bitbuf = 0; this.bitcnt = 0; }
  }
  get length() { return this.pos; }
}

// ---- Match finder: hash chains, positions inserted strictly in order ----
// Returns, per position, the longest match AND the closest match of length >= 8
// (a long far match is often worse than a shorter close one; the DP needs both).
function precomputeMatches(data, chainLimit, goodLen) {
  const n = data.length;
  const head = new Int32Array(HASH_SIZE).fill(-1);
  const prev = new Int32Array(n);
  const matchLen = new Uint16Array(n);
  const matchDist = new Int32Array(n);
  const matchLen2 = new Uint16Array(n);
  const matchDist2 = new Int32Array(n);
  let inserted = 0; // next position to insert; positions < inserted are in the table
  const hashAt = (i) => ((data[i] << 10) ^ (data[i + 1] << 5) ^ data[i + 2]) & HASH_MASK;
  for (let i = 0; i < n; i++) {
    // insert positions < i (all strictly before i)
    while (inserted < i) {
      if (inserted + 2 < n) {
        const h = hashAt(inserted);
        prev[inserted] = head[h];
        head[h] = inserted;
      }
      inserted++;
    }
    if (i + MIN_MATCH > n) continue;
    const h = hashAt(i);
    let cur = head[h];
    let bestLen = MIN_MATCH - 1, bestDist = 0;
    let closeLen = 0, closeDist = 0;
    let chain = 0;
    const limit = i > WSIZE ? i - WSIZE : 0;
    const maxLen = Math.min(MAX_MATCH, n - i);
    while (cur >= limit && chain < chainLimit) {
      chain++;
      if (bestLen >= MIN_MATCH && data[cur + bestLen] !== data[i + bestLen]) { cur = prev[cur]; continue; }
      let len = 0;
      const maxCmp = Math.min(maxLen, n - cur);
      while (len + 4 <= maxCmp &&
        data[cur + len] === data[i + len] && data[cur + len + 1] === data[i + len + 1] &&
        data[cur + len + 2] === data[i + len + 2] && data[cur + len + 3] === data[i + len + 3]) len += 4;
      while (len < maxCmp && data[cur + len] === data[i + len]) len++;
      if (len > bestLen) {
        bestLen = len; bestDist = i - cur;
        if (len >= maxLen) break;
        if (len >= goodLen) break;
      }
      // closest good match: smallest distance among matches of length >= 8
      if (len >= 8) {
        const d = i - cur;
        if (closeDist === 0 || d < closeDist) { closeLen = len; closeDist = d; }
      }
      cur = prev[cur];
    }
    if (bestLen >= MIN_MATCH) { matchLen[i] = bestLen; matchDist[i] = bestDist; }
    if (closeLen >= 8 && closeDist !== bestDist) { matchLen2[i] = closeLen; matchDist2[i] = closeDist; }
  }
  return { matchLen, matchDist, matchLen2, matchDist2 };
}

// Greedy parse using precomputed matches (for initial Huffman frequencies).
function greedyParse(data, matchLen, matchDist) {
  const n = data.length;
  const litFreq = new Float64Array(286);
  const distFreq = new Float64Array(30);
  const seq = [];
  let i = 0;
  while (i < n) {
    const L = matchLen[i];
    if (L >= MIN_MATCH) {
      const D = matchDist[i];
      seq.push({ len: L, dist: D });
      litFreq[257 + lenCode(L)]++;
      distFreq[distCode(D)]++;
      i += L;
    } else {
      seq.push({ lit: data[i] });
      litFreq[data[i]]++;
      i++;
    }
  }
  litFreq[256]++;
  return { seq, litFreq, distFreq };
}

// DP optimal parse over precomputed matches: at each position, literal or a match
// from either candidate (longest / closest-good), lengths L and L-1. Costs from
// Huffman lengths (or a flat model when litHuff/distHuff are null). Returns sequence + freqs.
function dpParse(data, m, litHuff, distHuff) {
  const { matchLen, matchDist, matchLen2, matchDist2 } = m;
  const n = data.length;
  const litCost = new Float64Array(286);
  const distCost = new Float64Array(30);
  if (litHuff === null) {
    // Flat cost model: literals 8 bits, length/dist symbols ~6 bits. Avoids the bias
    // of a greedy-parse Huffman that penalises symbols the greedy parse never used.
    for (let s = 0; s < 256; s++) litCost[s] = 8;
    litCost[256] = 5;
    for (let s = 257; s < 286; s++) litCost[s] = 6;
    for (let s = 0; s < 30; s++) distCost[s] = 6;
  } else {
    for (let s = 0; s < 286; s++) litCost[s] = litHuff.lengths[s] || 15;
    for (let s = 0; s < 30; s++) distCost[s] = distHuff.lengths[s] || 15;
  }
  const lenCost = new Float64Array(MAX_MATCH + 1);
  for (let L = MIN_MATCH; L <= MAX_MATCH; L++) {
    const lc = lenCode(L);
    lenCost[L] = litCost[257 + lc] + LEN_EXTRA[lc];
  }
  const cost = new Float64Array(n + 1).fill(Infinity);
  const choice = new Int16Array(n + 1);
  const choiceDist = new Int32Array(n + 1);
  cost[0] = 0;
  for (let p = 0; p < n; p++) {
    const c = cost[p];
    if (!Number.isFinite(c)) continue;
    const lc = c + litCost[data[p]];
    if (lc < cost[p + 1]) { cost[p + 1] = lc; choice[p + 1] = 0; }
    for (let k = 0; k < 2; k++) {
      const L = k === 0 ? matchLen[p] : matchLen2[p];
      if (L < MIN_MATCH) continue;
      const D = k === 0 ? matchDist[p] : matchDist2[p];
      const dc = distCost[distCode(D)] + DIST_EXTRA[distCode(D)];
      const cand = L >= 4 ? [L, L - 1] : [L];
      for (let j = 0; j < cand.length; j++) {
        const len = cand[j];
        if (len < MIN_MATCH) continue;
        const nc = c + lenCost[len] + dc;
        if (nc < cost[p + len]) { cost[p + len] = nc; choice[p + len] = len; choiceDist[p + len] = D; }
      }
    }
  }
  const seq = [];
  const litFreq = new Float64Array(286);
  const distFreq = new Float64Array(30);
  let p = n;
  while (p > 0) {
    const ch = choice[p];
    if (ch === 0) {
      seq.push({ lit: data[p - 1] });
      litFreq[data[p - 1]]++;
      p -= 1;
    } else {
      const D = choiceDist[p];
      seq.push({ len: ch, dist: D });
      litFreq[257 + lenCode(ch)]++;
      distFreq[distCode(D)]++;
      p -= ch;
    }
  }
  seq.reverse();
  litFreq[256]++;
  return { seq, litFreq, distFreq, bits: cost[n] };
}

// Deflate one block of `data` (a Uint8Array view). Returns {seq, litHuff, distHuff}.
function deflateBlock(data, opts) {
  const chainLimit = opts.chain ?? 128;
  const goodLen = opts.good ?? 258;
  const iters = opts.iters ?? 1;
  const flat = opts.flat ?? true;
  const m = precomputeMatches(data, chainLimit, goodLen);
  if (flat) {
    // Flat cost model for the DP (stable), then one Huffman build from the result.
    const r = dpParse(data, m, null, null);
    const litHuff = buildHuffman(r.litFreq, 15);
    let distFreq = r.distFreq;
    if (distFreq.every((v) => v === 0)) distFreq[0] = 1;
    const distHuff = buildHuffman(distFreq, 15);
    return { seq: r.seq, litHuff, distHuff };
  }
  let { litFreq, distFreq } = greedyParse(data, m.matchLen, m.matchDist);
  // ensure at least one distance code (needed even with no matches)
  if (distFreq.every((v) => v === 0)) distFreq[0] = 1;
  let litHuff = buildHuffman(litFreq, 15);
  let distHuff = buildHuffman(distFreq, 15);
  let best = null;
  for (let it = 0; it < iters; it++) {
    const r = dpParse(data, m, litHuff, distHuff);
    best = r;
    const lh = buildHuffman(r.litFreq, 15);
    const dh = buildHuffman(r.distFreq, 15);
    litHuff = lh; distHuff = dh;
  }
  if (best === null) {
    // iters=0: greedy parse only
    const g = greedyParse(data, m.matchLen, m.matchDist);
    return { seq: g.seq, litHuff, distHuff };
  }
  return { seq: best.seq, litHuff, distHuff };
}

// Plan a dynamic-Huffman block (no writing): tokens + code-length Huffman.
// Returns {valid, tokens, clHuff, clMax, litMax, distMax}; valid=false when the
// code-length Huffman would overflow 7 bits (caller then uses a fixed block).
function planDynamicBlock(seq, litHuff, distHuff) {
  const ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
  let litMax = 286, distMax = 30;
  while (litMax > 257 && litHuff.lengths[litMax - 1] === 0) litMax--;
  while (distMax > 1 && distHuff.lengths[distMax - 1] === 0) distMax--;
  const all = new Uint8Array(litMax + distMax);
  for (let i = 0; i < litMax; i++) all[i] = litHuff.lengths[i];
  for (let i = 0; i < distMax; i++) all[litMax + i] = distHuff.lengths[i];
  const tokens = [];
  let idx = 0;
  const N = all.length;
  while (idx < N) {
    const v = all[idx];
    if (v === 0) {
      let run = 0;
      while (idx + run < N && all[idx + run] === 0) run++;
      while (run >= 11) { const take = Math.min(run, 138); tokens.push({ sym: 18, extra: take - 11, bits: 7 }); run -= take; idx += take; }
      if (run >= 3) { tokens.push({ sym: 17, extra: run - 3, bits: 3 }); idx += run; run = 0; }
      while (run > 0) { tokens.push({ sym: 0, extra: 0, bits: 0 }); idx++; run--; }
    } else {
      tokens.push({ sym: v, extra: 0, bits: 0 });
      idx++;
      let run = 0;
      while (idx + run < N && all[idx + run] === v) run++;
      while (run >= 3) { const take = Math.min(run, 6); tokens.push({ sym: 16, extra: take - 3, bits: 2 }); run -= take; idx += take; }
      while (run > 0) { tokens.push({ sym: v, extra: 0, bits: 0 }); idx++; run--; }
    }
  }
  const clFreq = new Float64Array(19);
  for (const t of tokens) clFreq[t.sym]++;
  const clHuff = buildHuffman(clFreq, 7);
  if (clHuff.maxLen > 7) return { valid: false };
  let clMax = 19;
  while (clMax > 4 && clHuff.lengths[ORDER[clMax - 1]] === 0) clMax--;
  return { valid: true, tokens, clHuff, clMax, litMax, distMax };
}

function writeDynamicBlock(bw, plan, seq, litHuff, distHuff) {
  const ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
  const { tokens, clHuff, clMax, litMax, distMax } = plan;
  bw.write(litMax - 257, 5);
  bw.write(distMax - 1, 5);
  bw.write(clMax - 4, 4);
  for (let i = 0; i < clMax; i++) bw.write(clHuff.lengths[ORDER[i]], 3);
  for (const t of tokens) {
    bw.writeRev(clHuff.codes[t.sym], clHuff.lengths[t.sym]);
    if (t.bits) bw.write(t.extra, t.bits);
  }
  for (const s of seq) {
    if (s.lit !== undefined) {
      bw.writeRev(litHuff.codes[s.lit], litHuff.lengths[s.lit]);
    } else {
      const lc = lenCode(s.len);
      bw.writeRev(litHuff.codes[257 + lc], litHuff.lengths[257 + lc]);
      if (LEN_EXTRA[lc]) bw.write(s.len - LEN_BASE[lc], LEN_EXTRA[lc]);
      const dc = distCode(s.dist);
      bw.writeRev(distHuff.codes[dc], distHuff.lengths[dc]);
      if (DIST_EXTRA[dc]) bw.write(s.dist - DIST_BASE[dc], DIST_EXTRA[dc]);
    }
  }
  bw.writeRev(litHuff.codes[256], litHuff.lengths[256]);
}

// Fixed-Huffman block data (BTYPE=01): predefined lit/len + dist codes.
function fixedLit(sym) {
  if (sym < 144) return [0x30 + sym, 8];
  if (sym < 256) return [0x190 + (sym - 144), 9];
  if (sym < 280) return [sym - 256, 7];
  return [0xC0 + (sym - 280), 8];
}
function writeFixedBlock(bw, seq) {
  for (const s of seq) {
    if (s.lit !== undefined) {
      const [c, l] = fixedLit(s.lit);
      bw.writeRev(c, l);
    } else {
      const lc = lenCode(s.len);
      const [c, l] = fixedLit(257 + lc);
      bw.writeRev(c, l);
      if (LEN_EXTRA[lc]) bw.write(s.len - LEN_BASE[lc], LEN_EXTRA[lc]);
      const dc = distCode(s.dist);
      bw.writeRev(dc, 5);
      if (DIST_EXTRA[dc]) bw.write(s.dist - DIST_BASE[dc], DIST_EXTRA[dc]);
    }
  }
  bw.writeRev(0, 7); // end of block (256)
}

// Full optimal deflate of `data` into a zlib stream.
function deflateOptimal(data, opts = {}) {
  const blockSize = opts.blockSize ?? 262144;
  const bw = new BitWriter(data.length + 4096);
  bw.buf[bw.pos++] = 0x78;
  bw.buf[bw.pos++] = 0x9c;
  const nblocks = Math.max(1, Math.ceil(data.length / blockSize));
  for (let b = 0; b < nblocks; b++) {
    const start = b * blockSize;
    const end = Math.min(data.length, start + blockSize);
    const last = b === nblocks - 1;
    const { seq, litHuff, distHuff } = deflateBlock(data.subarray(start, end), opts);
    const plan = (litHuff.maxLen <= 15 && distHuff.maxLen <= 15) ? planDynamicBlock(seq, litHuff, distHuff) : { valid: false };
    if (plan.valid) {
      bw.write(last ? 1 : 0, 1);
      bw.write(0b10, 2);
      writeDynamicBlock(bw, plan, seq, litHuff, distHuff);
    } else {
      bw.write(last ? 1 : 0, 1);
      bw.write(0b01, 2);
      writeFixedBlock(bw, seq);
    }
  }
  bw.align();
  let a = 1, bb = 0;
  for (let i = 0; i < data.length;) {
    const end = Math.min(data.length, i + 5552);
    for (; i < end; i++) { a += data[i]; bb += a; }
    a %= 65521; bb %= 65521;
  }
  const ad = ((bb << 16) | a) >>> 0;
  bw.buf[bw.pos++] = (ad >>> 24) & 0xff;
  bw.buf[bw.pos++] = (ad >>> 16) & 0xff;
  bw.buf[bw.pos++] = (ad >>> 8) & 0xff;
  bw.buf[bw.pos++] = ad & 0xff;
  return bw.buf.subarray(0, bw.pos);
}

function verifyDeflate(data, stream) {
  const out = inflateSync(stream);
  if (out.length !== data.length) return false;
  for (let i = 0; i < data.length; i++) if (out[i] !== data[i]) return false;
  return true;
}

// ---------- Main ----------
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DEFLATE_OPTS = { chain: 256, iters: 2, good: 258, blockSize: 262144, flat: false };
const Z9 = { level: 9, memLevel: 9 };
for (const id of readdirSync(I).sort()) {
  const image = decodePng(new Uint8Array(readFileSync(join(I, id, 'image.png'))));
  const { form, data } = screen(image.rgba);
  // Best of: zlib level 9 vs our optimal-parse deflate (never worse than zlib 9).
  const z9 = deflateSync(data, Z9);
  const oz = deflateOptimal(data, DEFLATE_OPTS);
  const idat = z9.length <= oz.length ? z9 : oz;
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'image.png'), pngOfForm(image.width, image.height, form, idat));
}
