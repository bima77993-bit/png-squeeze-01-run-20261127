// png-squeeze-01-run-20261127 entry v2.
// Self-contained Node 22 program (built-in modules only). Reads /input/<id>/image.png
// (1280x720 RGBA stored PNG), writes /output/<id>/image.png losslessly, as small as
// possible. Pipeline: decode -> colour-type/palette screen -> per-row filter choice
// -> zopfli-faithful DEFLATE (hash-chain match finder + multi-candidate DP +
// length-limited Huffman, katajainen). Deterministic: no clock, no env, work-budgeted.
// PNG codec + screen adapted from the kit's program/generator/subject/{png,scale}.mjs
// (make.fun, MIT). The DEFLATE below is original work (faithful port of the zopfli
// algorithm's structure: lazy greedy + iterative DP + dynamic/fixed block choice).
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
// oz2.mjs — faithful zopfli-style optimal-parse DEFLATE in pure JS.
// Direct port of the algorithms in google/zopfli 1.0.3 (Apache 2.0):
//   - hash-chain longest match with the "same run" skip, recording the
//     sublen frontier (best/shortest distance for every length) per position
//   - forward shortest-path DP over ALL lengths (GetBestLengths), with the
//     min-cost pruning, literal + length transitions
//   - lazy-matching greedy parse for the initial symbol statistics
//   - iterative refinement: DP with entropy costs from the previous parse,
//     keeping the parse with the smallest ACTUAL dynamic block size
//   - length-limited Huffman via katajainen (boundary package-merge), RLE
//     optimisation of the code-length counts, best-of-8 tree encodings
//   - fixed/dynamic/uncompressed block-type choice per block (auto type),
//     with an optimal-fixed re-parse when fixed is competitive
// Deterministic: no clock, no env. Pure functions of the input bytes.
// Differences from C zopfli (all speed-only, no output effect intended):
//   - matches are precomputed once per stream (sublen steps) instead of
//     re-walking chains on every DP iteration (the LMC cache equivalent)
//   - the HASH_SAME_HASH second hash table is not used (chain limit + the
//     same-run skip keep flat images fast enough)
//   - no cost randomisation (only triggers after 5 unchanged iterations;
//     we run at most 5)

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
// Length symbol for every length 0..258 (ZopfliGetLengthSymbol table).
// NOTE: symbols reach 285, so this must NOT be a Uint8Array.
const LEN_SYM = (() => {
  const t = new Uint16Array(259);
  for (let l = 0; l < 259; l++) {
    let lo = 0, hi = 28;
    while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (LEN_BASE[mid] <= l) lo = mid; else hi = mid - 1; }
    t[l] = 257 + lo;
  }
  return t;
})();
// Distance symbol for every distance 0..32768 (ZopfliGetDistSymbol).
const DIST_SYM = (() => {
  const t = new Uint8Array(32769);
  for (let d = 0; d <= 32768; d++) {
    let lo = 0, hi = 29;
    while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (DIST_BASE[mid] <= d) lo = mid; else hi = mid - 1; }
    t[d] = lo;
  }
  return t;
})();
const LEN_EXTRA_OF_SYM = (s) => LEN_EXTRA[s - 257];
const DIST_EXTRA_OF_SYM = (s) => DIST_EXTRA[s];

function reverseBits(code, len) {
  let r = 0;
  for (let i = 0; i < len; i++) r = (r << 1) | ((code >> i) & 1);
  return r;
}

// ---- Length-limited Huffman code lengths (katajainen.c, boundary
// package-merge). Returns Uint8Array of lengths, or null if impossible. ----
function katajainen(freq, n, maxbits) {
  const lengths = new Uint8Array(n);
  const leaves = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) leaves.push({ weight: freq[i], count: i });
  const numsymbols = leaves.length;
  if (numsymbols === 0) return lengths;
  if (numsymbols === 1) { lengths[leaves[0].count] = 1; return lengths; }
  if (numsymbols === 2) { lengths[leaves[0].count] = 1; lengths[leaves[1].count] = 1; return lengths; }
  if ((1 << maxbits) < numsymbols) return null;
  leaves.sort((a, b) => (a.weight - b.weight) || (a.count - b.count));
  let mb = maxbits;
  if (numsymbols - 1 < mb) mb = numsymbols - 1;
  const node0 = { weight: leaves[0].weight, count: 1, tail: null };
  const node1 = { weight: leaves[1].weight, count: 2, tail: null };
  const lists = [];
  for (let i = 0; i < mb; i++) lists.push([node0, node1]);
  function boundaryPM(index) {
    const lastcount = lists[index][1].count;
    if (index === 0 && lastcount >= numsymbols) return;
    const oldchain = lists[index][1];
    const newchain = { weight: 0, count: 0, tail: null };
    lists[index][0] = oldchain;
    lists[index][1] = newchain;
    if (index === 0) {
      newchain.weight = leaves[lastcount].weight;
      newchain.count = lastcount + 1;
      newchain.tail = null;
    } else {
      const sum = lists[index - 1][0].weight + lists[index - 1][1].weight;
      if (lastcount < numsymbols && sum > leaves[lastcount].weight) {
        newchain.weight = leaves[lastcount].weight;
        newchain.count = lastcount + 1;
        newchain.tail = oldchain.tail;
      } else {
        newchain.weight = sum;
        newchain.count = lastcount;
        newchain.tail = lists[index - 1][1];
        boundaryPM(index - 1);
        boundaryPM(index - 1);
      }
    }
  }
  function boundaryPMFinal(index) {
    const lastcount = lists[index][1].count;
    const sum = lists[index - 1][0].weight + lists[index - 1][1].weight;
    if (lastcount < numsymbols && sum > leaves[lastcount].weight) {
      const newchain = { weight: 0, count: lastcount + 1, tail: lists[index][1].tail };
      lists[index][1] = newchain;
    } else {
      lists[index][1].tail = lists[index - 1][1];
    }
  }
  const numRuns = 2 * numsymbols - 4;
  for (let i = 0; i < numRuns - 1; i++) boundaryPM(mb - 1);
  boundaryPMFinal(mb - 1);
  const counts = new Array(16).fill(0);
  let end = 16;
  for (let node = lists[mb - 1][1]; node; node = node.tail) counts[--end] = node.count;
  let ptr = 15, value = 1, val = counts[15];
  while (ptr >= end) {
    for (; val > counts[ptr - 1]; val--) lengths[leaves[val - 1].count] = value;
    ptr--;
    value++;
  }
  return lengths;
}

// Canonical Huffman codes from lengths (ZopfliLengthsToSymbols).
function lengthsToSymbols(lengths, n, maxbits) {
  const symbols = new Uint32Array(n);
  const blCount = new Int32Array(maxbits + 1);
  for (let i = 0; i < n; i++) blCount[lengths[i]]++;
  const nextCode = new Int32Array(maxbits + 1);
  let code = 0;
  blCount[0] = 0;
  for (let b = 1; b <= maxbits; b++) { code = (code + blCount[b - 1]) << 1; nextCode[b] = code; }
  for (let i = 0; i < n; i++) { const len = lengths[i]; if (len !== 0) { symbols[i] = nextCode[len]; nextCode[len]++; } }
  return symbols;
}

// Ensure at least 2 distance codes (PatchDistanceCodesForBuggyDecoders).
function patchDistanceCodes(dLengths) {
  let num = 0;
  for (let i = 0; i < 30; i++) {
    if (dLengths[i]) num++;
    if (num >= 2) return;
  }
  if (num === 0) { dLengths[0] = 1; dLengths[1] = 1; }
  else if (num === 1) { dLengths[dLengths[0] ? 1 : 0] = 1; }
}

// Adjust counts so the Huffman tree RLE-compresses better (deflate.c).
function optimizeHuffmanForRle(length, counts) {
  let i, k, stride, symbol, sum, limit;
  for (; length >= 0; --length) {
    if (length === 0) return;
    if (counts[length - 1] !== 0) break;
  }
  const goodForRle = new Array(length).fill(0);
  symbol = counts[0];
  stride = 0;
  for (i = 0; i < length + 1; i++) {
    if (i === length || counts[i] !== symbol) {
      if ((symbol === 0 && stride >= 5) || (symbol !== 0 && stride >= 7)) {
        for (k = 0; k < stride; k++) goodForRle[i - k - 1] = 1;
      }
      stride = 1;
      if (i !== length) symbol = counts[i];
    } else stride++;
  }
  stride = 0;
  limit = counts[0];
  sum = 0;
  for (i = 0; i < length + 1; i++) {
    if (i === length || goodForRle[i] || Math.abs(counts[i] - limit) >= 4) {
      if (stride >= 4 || (stride >= 3 && sum === 0)) {
        let count = Math.floor((sum + Math.floor(stride / 2)) / stride);
        if (count < 1) count = 1;
        if (sum === 0) count = 0;
        for (k = 0; k < stride; k++) counts[i - k - 1] = count;
      }
      stride = 0;
      sum = 0;
      if (i < length - 3) limit = Math.floor((counts[i] + counts[i + 1] + counts[i + 2] + counts[i + 3] + 2) / 4);
      else if (i < length) limit = counts[i];
      else limit = 0;
    }
    stride++;
    if (i !== length) sum += counts[i];
  }
}

// RLE-encode the lit/len + dist code lengths (EncodeTree). Returns the size
// in bits plus the tokens and the code-length Huffman, for writing.
const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
function encodeTreeInfo(llLengths, dLengths, use16, use17, use18) {
  let hlit = 29, hdist = 29;
  while (hlit > 0 && llLengths[257 + hlit - 1] === 0) hlit--;
  while (hdist > 0 && dLengths[1 + hdist - 1] === 0) hdist--;
  const hlit2 = hlit + 257;
  const lldTotal = hlit2 + hdist + 1;
  const rle = [], rleBits = [];
  const clcounts = new Array(19).fill(0);
  for (let i = 0; i < lldTotal; i++) {
    const symbol = i < hlit2 ? llLengths[i] : dLengths[i - hlit2];
    let count = 1;
    if (use16 || (symbol === 0 && (use17 || use18))) {
      let j = i + 1;
      while (j < lldTotal && symbol === (j < hlit2 ? llLengths[j] : dLengths[j - hlit2])) j++;
      count = j - i;
    }
    i += count - 1;
    if (symbol === 0 && count >= 3) {
      if (use18) {
        while (count >= 11) { const c2 = Math.min(count, 138); rle.push(18); rleBits.push(c2 - 11); clcounts[18]++; count -= c2; }
      }
      if (use17) {
        while (count >= 3) { const c2 = Math.min(count, 10); rle.push(17); rleBits.push(c2 - 3); clcounts[17]++; count -= c2; }
      }
    }
    if (use16 && count >= 4) {
      count--;
      clcounts[symbol]++;
      rle.push(symbol); rleBits.push(0);
      while (count >= 3) { const c2 = Math.min(count, 6); rle.push(16); rleBits.push(c2 - 3); clcounts[16]++; count -= c2; }
    }
    clcounts[symbol] += count;
    while (count > 0) { rle.push(symbol); rleBits.push(0); count--; }
  }
  const clLengths = katajainen(clcounts, 19, 7);
  let hclen = 15;
  while (hclen > 0 && clcounts[CL_ORDER[hclen + 3]] === 0) hclen--;
  let size = 14 + (hclen + 4) * 3;
  for (let s = 0; s < 19; s++) size += clLengths[s] * clcounts[s];
  size += clcounts[16] * 2 + clcounts[17] * 3 + clcounts[18] * 7;
  return { size, rle, rleBits, clLengths, hlit, hdist, hclen };
}
function bestEncodeTree(llLengths, dLengths) {
  let best = null;
  for (let i = 0; i < 8; i++) {
    const info = encodeTreeInfo(llLengths, dLengths, i & 1, i & 2, i & 4);
    if (best === null || info.size < best.size) best = info;
  }
  return best;
}

// ---- Bit writer (LSB-first) ----
class BitWriter2 {
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
  writeRaw(bytes) {
    this.align();
    this.buf.set(bytes, this.pos);
    this.pos += bytes.length;
  }
  get length() { return this.pos; }
}

// ---- Match precompute: hash chains + sublen frontier (steps) ----
// Per position, steps are (endLen, dist) pairs; the interval (prevEnd, endLen]
// has sublen = dist (best/shortest distance for each length in it).
// This is ZopfliFindLongestMatch's sublen, recorded once per stream.
function precomputeSteps(data, chainLimit, goodLen, fruitlessLimit) {
  const n = data.length;
  const head = new Int32Array(HASH_SIZE).fill(-1);
  const prev = new Int32Array(n);
  const run = new Uint16Array(n);
  for (let i = n - 1; i >= 0; i--) {
    run[i] = (i + 1 < n && data[i] === data[i + 1]) ? Math.min(run[i + 1] + 1, 65535) : 1;
  }
  const hashAt = (i) => ((data[i] << 10) ^ (data[i + 1] << 5) ^ data[i + 2]) & HASH_MASK;
  let cap = 1 << 20;
  let stepLen = new Uint16Array(cap);
  let stepDist = new Int32Array(cap);
  let stepCount = 0;
  const off = new Int32Array(n + 1);
  const grow = () => {
    const nl = new Uint16Array(cap * 2), nd = new Int32Array(cap * 2);
    nl.set(stepLen); nd.set(stepDist);
    stepLen = nl; stepDist = nd; cap *= 2;
  };
  let inserted = 0;
  for (let i = 0; i < n; i++) {
    off[i] = stepCount;
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
    const limit = i > WSIZE ? i - WSIZE : 0;
    const maxLen = Math.min(MAX_MATCH, n - i);
    let bestLen = 2;
    let chain = 0;
    let sinceImprove = 0;
    const same0 = run[i] - 1;
    while (cur >= limit && chain < chainLimit) {
      chain++;
      // Quick check first: the byte at bestLen must match, else this
      // candidate cannot beat the current best (no maxCmp needed here).
      if (bestLen >= MIN_MATCH && data[cur + bestLen] !== data[i + bestLen]) {
        if (fruitlessLimit > 0) {
          if (++sinceImprove >= fruitlessLimit) break;
        }
        cur = prev[cur]; continue;
      }
      const maxCmp = maxLen < n - cur ? maxLen : n - cur;
      if (bestLen >= maxCmp) { cur = prev[cur]; continue; }
      let len = 0;
      if (same0 > 2 && data[cur] === data[i]) {
        let skip = same0;
        const s1 = run[cur] - 1;
        if (s1 < skip) skip = s1;
        if (skip > maxCmp) skip = maxCmp;
        len = skip;
      }
      while (len + 4 <= maxCmp &&
        data[cur + len] === data[i + len] && data[cur + len + 1] === data[i + len + 1] &&
        data[cur + len + 2] === data[i + len + 2] && data[cur + len + 3] === data[i + len + 3]) len += 4;
      while (len < maxCmp && data[cur + len] === data[i + len]) len++;
      if (len > bestLen) {
        if (stepCount === cap) grow();
        stepLen[stepCount] = len;
        stepDist[stepCount] = i - cur;
        stepCount++;
        bestLen = len;
        sinceImprove = 0;
        if (len >= maxLen) break;
        if (len >= goodLen) break;
      } else if (fruitlessLimit > 0 && bestLen >= MIN_MATCH) {
        if (++sinceImprove >= fruitlessLimit) break;
      }
      cur = prev[cur];
    }
  }
  off[n] = stepCount;
  return { off, len: stepLen.subarray(0, stepCount), dist: stepDist.subarray(0, stepCount), n };
}

// ---- Cost models ----
function calcEntropy(count, n, bitlengths) {
  let sum = 0;
  for (let i = 0; i < n; i++) sum += count[i];
  const log2sum = (sum === 0 ? Math.log(n) : Math.log(sum)) * 1.4426950408889;
  for (let i = 0; i < n; i++) {
    let b = count[i] === 0 ? log2sum : log2sum - Math.log(count[i]) * 1.4426950408889;
    if (b < 0 && b > -1e-5) b = 0;
    bitlengths[i] = b;
  }
}
function entropyCosts(litFreq, distFreq) {
  const llCost = new Float64Array(288);
  const dCost = new Float64Array(32);
  calcEntropy(litFreq, 288, llCost);
  calcEntropy(distFreq, 32, dCost);
  return { llCost, dCost };
}
function fixedCosts() {
  const llCost = new Float64Array(288);
  const dCost = new Float64Array(32);
  for (let s = 0; s < 144; s++) llCost[s] = 8;
  for (let s = 144; s < 256; s++) llCost[s] = 9;
  for (let s = 256; s < 280; s++) llCost[s] = 7;
  for (let s = 280; s < 288; s++) llCost[s] = 8;
  for (let s = 0; s < 32; s++) dCost[s] = 5;
  return { llCost, dCost };
}
const FIXED_LL = (() => {
  const a = new Uint8Array(288);
  for (let s = 0; s < 144; s++) a[s] = 8;
  for (let s = 144; s < 256; s++) a[s] = 9;
  for (let s = 256; s < 280; s++) a[s] = 7;
  for (let s = 280; s < 288; s++) a[s] = 8;
  return a;
})();
const FIXED_D = new Uint8Array(32).fill(5);

// ---- Lazy-matching greedy parse (ZopfliLZ77Greedy), for initial stats ----
function greedyParse(data, steps, start, end) {
  const litFreq = new Float64Array(288);
  const distFreq = new Float64Array(32);
  const score = (len, dist) => len - (dist > 1024 ? 1 : 0);
  const longest = (p) => {
    const s0 = steps.off[p], s1 = steps.off[p + 1];
    if (s0 === s1) return [0, 0];
    const s = s1 - 1;
    return [steps.len[s], steps.dist[s]];
  };
  let i = start;
  let prevLen = 0, prevDist = 0, avail = false;
  while (i < end) {
    let [leng, dist] = longest(i);
    if (leng > end - i) leng = end - i;
    const ls = score(leng, dist);
    if (avail) {
      avail = false;
      const ps = score(prevLen, prevDist);
      if (ls > ps + 1) {
        litFreq[data[i - 1]]++;
        if (ls >= MIN_MATCH && leng < MAX_MATCH) {
          avail = true; prevLen = leng; prevDist = dist;
          i++;
          continue;
        }
      } else {
        litFreq[LEN_SYM[prevLen]]++;
        distFreq[DIST_SYM[prevDist]]++;
        i = (i - 1) + prevLen;
        continue;
      }
    } else if (ls >= MIN_MATCH && leng < MAX_MATCH) {
      avail = true; prevLen = leng; prevDist = dist;
      i++;
      continue;
    }
    if (ls >= MIN_MATCH) {
      litFreq[LEN_SYM[leng]]++;
      distFreq[DIST_SYM[dist]]++;
      i += leng;
    } else {
      litFreq[data[i]]++;
      i++;
    }
  }
  if (avail) {
    // Unreachable in theory (a pending match is always resolved); emit it
    // clamped rather than dropping bytes.
    const p = i - 1;
    let L = prevLen;
    if (L > end - p) L = end - p;
    if (L >= MIN_MATCH) { litFreq[LEN_SYM[L]]++; distFreq[DIST_SYM[prevDist]]++; }
    else litFreq[data[p]]++;
  }
  litFreq[256]++;
  return { litFreq, distFreq };
}

// ---- Forward shortest-path DP (GetBestLengths) ----
// mode 'all': every length 3..kend (exact zopfli). mode 'sparse': step starts,
// length-symbol boundaries and step ends only.
// Returns {seq (flat [litlen, dist] pairs), litFreq, distFreq, bits}.
function dpParse(data, steps, start, end, llCost, dCost, mode) {
  const len = end - start;
  const lenCost = new Float64Array(MAX_MATCH + 1);
  for (let L = MIN_MATCH; L <= MAX_MATCH; L++) {
    const s = LEN_SYM[L];
    lenCost[L] = llCost[s] + LEN_EXTRA[s - 257];
  }
  const distCost = new Float64Array(WSIZE + 1);
  for (let d = 1; d <= WSIZE; d++) {
    const s = DIST_SYM[d];
    distCost[d] = dCost[s] + DIST_EXTRA[s];
  }
  let minLen = Infinity, minDist = Infinity;
  for (let L = MIN_MATCH; L <= MAX_MATCH; L++) if (lenCost[L] < minLen) minLen = lenCost[L];
  for (let d = 1; d <= WSIZE; d++) if (distCost[d] < minDist) minDist = distCost[d];
  const mincost = minLen + minDist;
  const costs = new Float64Array(len + 1).fill(Infinity);
  const lengthArr = new Uint16Array(len + 1);
  const choiceDist = new Int32Array(len + 1);
  costs[0] = 0;
  for (let j = 0; j < len; j++) {
    const c = costs[j];
    if (!Number.isFinite(c)) continue;
    const p = start + j;
    const nc = c + llCost[data[p]];
    if (nc < costs[j + 1]) { costs[j + 1] = nc; lengthArr[j + 1] = 1; choiceDist[j + 1] = 0; }
    const s0 = steps.off[p], s1 = steps.off[p + 1];
    if (s0 === s1) continue;
    const floor = mincost + c;
    let prevEnd = 2;
    for (let s = s0; s < s1; s++) {
      const hi = steps.len[s];
      const d = steps.dist[s];
      const lo = Math.max(MIN_MATCH, prevEnd + 1);
      const dc = distCost[d];
      const maxK = Math.min(hi, len - j);
      if (mode === 'all') {
        for (let k = lo; k <= maxK; k++) {
          if (costs[j + k] <= floor) continue;
          const ncost = c + lenCost[k] + dc;
          if (ncost < costs[j + k]) { costs[j + k] = ncost; lengthArr[j + k] = k; choiceDist[j + k] = d; }
        }
      } else {
        if (lo <= maxK && costs[j + lo] > floor) {
          const ncost = c + lenCost[lo] + dc;
          if (ncost < costs[j + lo]) { costs[j + lo] = ncost; lengthArr[j + lo] = lo; choiceDist[j + lo] = d; }
        }
        for (let b = 0; b < 29; b++) {
          const k = LEN_BASE[b];
          if (k <= lo) continue;
          if (k > maxK) break;
          if (costs[j + k] <= floor) continue;
          const ncost = c + lenCost[k] + dc;
          if (ncost < costs[j + k]) { costs[j + k] = ncost; lengthArr[j + k] = k; choiceDist[j + k] = d; }
        }
        if (hi > lo && hi <= maxK && costs[j + hi] > floor) {
          const ncost = c + lenCost[hi] + dc;
          if (ncost < costs[j + hi]) { costs[j + hi] = ncost; lengthArr[j + hi] = hi; choiceDist[j + hi] = d; }
        }
      }
      prevEnd = hi;
    }
  }
  const seq = [];
  const litFreq = new Float64Array(288);
  const distFreq = new Float64Array(32);
  let pos = len;
  while (pos > 0) {
    const L = lengthArr[pos];
    if (L === 1) {
      const b = data[start + pos - 1];
      seq.push(b, 0);
      litFreq[b]++;
      pos -= 1;
    } else {
      const d = choiceDist[pos];
      seq.push(L, d);
      litFreq[LEN_SYM[L]]++;
      distFreq[DIST_SYM[d]]++;
      pos -= L;
    }
  }
  for (let a = 0, b = seq.length - 2; a < b; a += 2, b -= 2) {
    const t0 = seq[a], t1 = seq[a + 1];
    seq[a] = seq[b]; seq[a + 1] = seq[b + 1];
    seq[b] = t0; seq[b + 1] = t1;
  }
  litFreq[256]++;
  return { seq, litFreq, distFreq, bits: costs[len] };
}

// ---- Block size (bits, incl. the 3-bit header) ----
function dataBits(litFreq, distFreq, llLengths, dLengths) {
  let bits = 0;
  for (let s = 0; s < 256; s++) bits += llLengths[s] * litFreq[s];
  for (let s = 257; s < 286; s++) { bits += llLengths[s] * litFreq[s]; bits += LEN_EXTRA[s - 257] * litFreq[s]; }
  for (let s = 0; s < 30; s++) { bits += dLengths[s] * distFreq[s]; bits += DIST_EXTRA[s] * distFreq[s]; }
  bits += llLengths[256];
  return bits;
}
function dynamicBlockInfo(litFreq, distFreq) {
  const llCounts = Array.from(litFreq);
  const dCounts = Array.from(distFreq);
  llCounts[256] = 1;
  let llLengths = katajainen(llCounts, 288, 15);
  let dLengths = katajainen(dCounts, 32, 15);
  if (llLengths === null || dLengths === null) return null;
  patchDistanceCodes(dLengths);
  let tree = bestEncodeTree(llLengths, dLengths);
  let bestBits = tree.size + dataBits(litFreq, distFreq, llLengths, dLengths);
  let bestLL = llLengths, bestD = dLengths, bestTree = tree;
  const llCounts2 = llCounts.slice();
  const dCounts2 = dCounts.slice();
  optimizeHuffmanForRle(288, llCounts2);
  optimizeHuffmanForRle(32, dCounts2);
  const llLengths2 = katajainen(llCounts2, 288, 15);
  const dLengths2 = katajainen(dCounts2, 32, 15);
  if (llLengths2 !== null && dLengths2 !== null) {
    patchDistanceCodes(dLengths2);
    const tree2 = bestEncodeTree(llLengths2, dLengths2);
    const bits2 = tree2.size + dataBits(litFreq, distFreq, llLengths2, dLengths2);
    if (bits2 < bestBits) { bestBits = bits2; bestLL = llLengths2; bestD = dLengths2; bestTree = tree2; }
  }
  return { bits: 3 + bestBits, llLengths: bestLL, dLengths: bestD, tree: bestTree };
}
function uncompressedBits(byteLen) {
  if (byteLen === 0) return 0;
  const blocks = Math.floor(byteLen / 65535) + (byteLen % 65535 ? 1 : 0);
  return blocks * 5 * 8 + byteLen * 8;
}

// ---- One deflate block: iterate DP, keep the best actual block size ----
function lz77OptimalBlock(data, steps, start, end, opts) {
  const byteLen = end - start;
  const iters = opts.iters ?? 2;
  const mode = opts.dpMode ?? 'all';
  let g = greedyParse(data, steps, start, end);
  let e = entropyCosts(g.litFreq, g.distFreq);
  let llCost = e.llCost, dCost = e.dCost;
  let best = null, bestBits = Infinity, bestFreqs = null;
  for (let it = 0; it < iters; it++) {
    const r = dpParse(data, steps, start, end, llCost, dCost, mode);
    const info = dynamicBlockInfo(r.litFreq, r.distFreq);
    if (info !== null && info.bits < bestBits) {
      bestBits = info.bits;
      best = { seq: r.seq, btype: 2, llLengths: info.llLengths, dLengths: info.dLengths, tree: info.tree, bits: info.bits };
      bestFreqs = { litFreq: r.litFreq, distFreq: r.distFreq };
    }
    const e2 = entropyCosts(r.litFreq, r.distFreq);
    llCost = e2.llCost; dCost = e2.dCost;
  }
  if (best === null) {
    // No dynamic info (should not happen): fall back to a fixed block from
    // the last parse.
    const fc = fixedCosts();
    const r = dpParse(data, steps, start, end, fc.llCost, fc.dCost, mode);
    return { seq: r.seq, btype: 1, bits: 3 + dataBits(r.litFreq, r.distFreq, FIXED_LL, FIXED_D) };
  }
  const fixedCostBest = 3 + dataBits(bestFreqs.litFreq, bestFreqs.distFreq, FIXED_LL, FIXED_D);
  const uncCost = uncompressedBits(byteLen);
  if (uncCost < bestBits && uncCost < fixedCostBest) {
    return { seq: null, btype: 0, bits: uncCost };
  }
  if (fixedCostBest < bestBits) {
    const expensive = (best.seq.length / 2 < 1000) || fixedCostBest <= bestBits * 1.1;
    let seq = best.seq, bits = fixedCostBest;
    if (expensive) {
      const fc = fixedCosts();
      const rf = dpParse(data, steps, start, end, fc.llCost, fc.dCost, mode);
      const rfBits = 3 + dataBits(rf.litFreq, rf.distFreq, FIXED_LL, FIXED_D);
      if (rfBits < bits) { seq = rf.seq; bits = rfBits; }
    }
    return { seq, btype: 1, bits };
  }
  return best;
}

// ---- Writers ----
function fixedLit(sym) {
  if (sym < 144) return [0x30 + sym, 8];
  if (sym < 256) return [0x190 + (sym - 144), 9];
  if (sym < 280) return [sym - 256, 7];
  return [0xC0 + (sym - 280), 8];
}
function writeSeq(bw, seq, llSymbols, llLengths, dSymbols, dLengths) {
  for (let t = 0; t < seq.length; t += 2) {
    const litlen = seq[t], dist = seq[t + 1];
    if (dist === 0) {
      bw.writeRev(llSymbols[litlen], llLengths[litlen]);
    } else {
      const ls = LEN_SYM[litlen];
      bw.writeRev(llSymbols[ls], llLengths[ls]);
      const le = LEN_EXTRA[ls - 257];
      if (le) bw.write(litlen - LEN_BASE[ls - 257], le);
      const ds = DIST_SYM[dist];
      bw.writeRev(dSymbols[ds], dLengths[ds]);
      const de = DIST_EXTRA[ds];
      if (de) bw.write(dist - DIST_BASE[ds], de);
    }
  }
}
function writeFixedBlock(bw, seq) {
  for (let t = 0; t < seq.length; t += 2) {
    const litlen = seq[t], dist = seq[t + 1];
    if (dist === 0) {
      const [c, l] = fixedLit(litlen);
      bw.writeRev(c, l);
    } else {
      const ls = LEN_SYM[litlen];
      const [c, l] = fixedLit(ls);
      bw.writeRev(c, l);
      const le = LEN_EXTRA[ls - 257];
      if (le) bw.write(litlen - LEN_BASE[ls - 257], le);
      const ds = DIST_SYM[dist];
      bw.writeRev(ds, 5);
      const de = DIST_EXTRA[ds];
      if (de) bw.write(dist - DIST_BASE[ds], de);
    }
  }
  bw.writeRev(0, 7);
}
function writeDynamicBlock(bw, tree, seq, llLengths, dLengths) {
  const llSymbols = lengthsToSymbols(llLengths, 288, 15);
  const dSymbols = lengthsToSymbols(dLengths, 32, 15);
  const clSymbols = lengthsToSymbols(tree.clLengths, 19, 7);
  bw.write(tree.hlit, 5);
  bw.write(tree.hdist, 5);
  bw.write(tree.hclen, 4);
  for (let i = 0; i < tree.hclen + 4; i++) bw.write(tree.clLengths[CL_ORDER[i]], 3);
  for (let i = 0; i < tree.rle.length; i++) {
    const sym = tree.rle[i];
    bw.writeRev(clSymbols[sym], tree.clLengths[sym]);
    if (sym === 16) bw.write(tree.rleBits[i], 2);
    else if (sym === 17) bw.write(tree.rleBits[i], 3);
    else if (sym === 18) bw.write(tree.rleBits[i], 7);
  }
  writeSeq(bw, seq, llSymbols, llLengths, dSymbols, dLengths);
  bw.writeRev(llSymbols[256], llLengths[256]);
}
function writeStoredBlock(bw, data, start, end, last) {
  let pos = start;
  for (;;) {
    const blocksize = Math.min(65535, end - pos);
    const currentFinal = pos + blocksize >= end;
    bw.write(last && currentFinal ? 1 : 0, 1);
    bw.write(0, 2);
    bw.align();
    bw.writeRaw(Uint8Array.of(blocksize & 0xff, (blocksize >> 8) & 0xff, (~blocksize) & 0xff, ((~blocksize) >> 8) & 0xff));
    bw.writeRaw(data.subarray(pos, pos + blocksize));
    if (currentFinal) break;
    pos += blocksize;
  }
}

// ---- Top level: deflate `data` into a zlib stream ----
function deflateZopfli(data, opts = {}) {
  if (data.length === 0) {
    // Smallest empty block: fixed block with just the end symbol.
    const bw = new BitWriter2(16);
    bw.buf[bw.pos++] = 0x78;
    bw.buf[bw.pos++] = 0x9c;
    bw.write(1, 1);
    bw.write(0b01, 2);
    bw.writeRev(0, 7);
    bw.align();
    bw.buf[bw.pos++] = 0; bw.buf[bw.pos++] = 0; bw.buf[bw.pos++] = 0; bw.buf[bw.pos++] = 1;
    return bw.buf.subarray(0, bw.pos);
  }
  const blockSize = opts.blockSize ?? 262144;
  const steps = precomputeSteps(data, opts.chain ?? 256, opts.good ?? 258, opts.fruitless ?? 0);
  const bw = new BitWriter2(data.length + 16384);
  bw.buf[bw.pos++] = 0x78;
  bw.buf[bw.pos++] = 0x9c;
  const nblocks = Math.max(1, Math.ceil(data.length / blockSize));
  for (let b = 0; b < nblocks; b++) {
    const start = b * blockSize;
    const end = Math.min(data.length, start + blockSize);
    const last = b === nblocks - 1;
    const res = lz77OptimalBlock(data, steps, start, end, opts);
    if (res.btype === 0) {
      writeStoredBlock(bw, data, start, end, last);
    } else if (res.btype === 1) {
      bw.write(last ? 1 : 0, 1);
      bw.write(0b01, 2);
      writeFixedBlock(bw, res.seq);
    } else {
      bw.write(last ? 1 : 0, 1);
      bw.write(0b10, 2);
      writeDynamicBlock(bw, res.tree, res.seq, res.llLengths, res.dLengths);
    }
  }
  bw.align();
  let a = 1, bb = 0;
  for (let i = 0; i < data.length;) {
    const e = Math.min(data.length, i + 5552);
    for (; i < e; i++) { a += data[i]; bb += a; }
    a %= 65521; bb %= 65521;
  }
  const ad = ((bb << 16) | a) >>> 0;
  bw.buf[bw.pos++] = (ad >>> 24) & 0xff;
  bw.buf[bw.pos++] = (ad >>> 16) & 0xff;
  bw.buf[bw.pos++] = (ad >>> 8) & 0xff;
  bw.buf[bw.pos++] = ad & 0xff;
  return bw.buf.subarray(0, bw.pos);
}

function verifyDeflate2(data, stream) {
  const out = inflateSync(stream);
  if (out.length !== data.length) return false;
  for (let i = 0; i < data.length; i++) if (out[i] !== data[i]) return false;
  return true;
}

// ---------- Main ----------
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
// oz2: faithful zopfli port. chain=192, iters=1, block 256KB, DP mode 'all'.
// Time-budgeted: chain=192 (vs 256) saves ~3 s across the set for ~1.6k points,
// keeping the worst held-out set (~40 s local) inside the 60 s server limit.
// iters=1 costs ~+270 B on i002 vs iters=2 but saves ~9 s. Best-of(zlib9, oz2).
const DEFLATE_OPTS = { chain: 192, iters: 1, good: 258, blockSize: 262144, mode: 'all' };
const Z9 = { level: 9, memLevel: 9 };
for (const id of readdirSync(I).sort()) {
  const image = decodePng(new Uint8Array(readFileSync(join(I, id, 'image.png'))));
  const { form, data } = screen(image.rgba);
  // Best of: zlib level 9 vs our zopfli-port deflate (never worse than zlib 9).
  const z9 = deflateSync(data, Z9);
  const oz = deflateZopfli(data, DEFLATE_OPTS);
  const idat = z9.length <= oz.length ? z9 : oz;
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'image.png'), pngOfForm(image.width, image.height, form, idat));
}
