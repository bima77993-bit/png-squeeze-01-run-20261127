# png-squeeze-01-run-20261127

![GitHub repo size](https://img.shields.io/github/repo-size/bima77993-bit/png-squeeze-01-run-20261127)
![GitHub license](https://img.shields.io/github/license/bima77993-bit/png-squeeze-01-run-20261127)
![GitHub last commit](https://img.shields.io/github/last-commit/bima77993-bit/png-squeeze-01-run-20261127)

Entry for the make.fun bounty **[Squeeze screenshots into the smallest PNG, 27 November 2026](https://make.fun/bounty/png-squeeze-01-run-20261127)** ($100 total, 50 places, deadline 29 Nov 2026 12:00 WIB).

## What it does

`main.ts` (Node 22, built-in modules only, zero dependencies) reads
`/input/i001..i008/image.png` (1280×720 RGBA stored PNGs) and writes
`/output/<id>/image.png` — losslessly, as small as possible.

Pipeline:

1. **Decode** the stored RGBA PNG (zlib inflate).
2. **Screen** colour types and per-row filter choices by zlib level 6:
   palette (≤256 colours) + tRNS, grey, grey+alpha, RGB, RGBA, alpha dropped
   when fully opaque; filters 0–4, `minsum`, `pairs`, `brute`.
3. **Compress** the winner's filtered data with the **best of zlib level 9 and
   an original optimal-parse DEFLATE** (hash-chain match finder + shortest-path
   DP + dynamic Huffman, 256 KB blocks). The best-of fallback keeps the entry
   from ever doing worse than zlib 9.
4. Deterministic: no clock, no environment — byte-identical across runs.
   Budgeted by work, never by wall clock. 60 s wall for all 8 instances.

## Scores (local `grade-local`, official scorer)

| set | score | per-instance bytes |
|-----|-------|--------------------|
| practice | **708,837** | i001 12,472 · i002 52,273 · i003 108,156 · i004 101,164 · i005 16,552 · i006 174,819 · i007 60,890 · i008 24,900 |
| held-out h1 (fresh seed) | **719,578** | — |
| held-out h2 (fresh seed) | **714,678** | — |

Held-out sets were generated with the kit's public generator from fresh seeds,
so the compressor generalises and does not overfit the practice set.
L1 regrade reproduced byte-for-byte (deterministic).

## Notes

- The optimal-parse deflate is only ~3–5% better than zlib 9 and is unreliable
  on alpha/grey images (hence the best-of fallback). The biggest remaining lever
  is a Viterbi filter DP (globally optimal filter sequence instead of greedy
  per-row) and a better match-finder/DP cost model; closing the gap to the
  ~780k reference needs a faithful zopfli-style port, not more parameter tuning.
- PNG codec + screen adapted from the kit's
  `program/generator/subject/{png,scale}.mjs` (make.fun, MIT). The DEFLATE
  is original work.
