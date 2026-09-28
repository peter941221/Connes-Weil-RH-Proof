# 2095 - Route A legal half-strip grid screen

Date: 2026-09-28.

Status: COVER-LEGAL-HALFSTRIP-GRID-CANDIDATE.

At fixed scale `0.86`, evaluator `m=6400`, finite window `|xi| <= 40`, and
step `0.02`, all 20 points in the registered gamma/delta grid are negative:

```text
gamma cells: 37.586178, 40.918719, 43.327073, 48.005151
delta cells: 0.10, 0.20, 0.30, 0.40, 0.49
support:     9.288
book:        1368
worst Q:     -5.1246019166052637e11
worst cell:  gamma=37.586178, delta=0.49
```

The sign survives the sampled legal half-strip grid and the weakest sampled
margin is still negative. This is stronger than the isolated 2093/2094
screens, but it remains a screening result: the m=6400 finite grid is not an
outward certificate, gamma/delta interpolation is not proved, and fixed scale
0.86 is not claimed optimal or uniformly valid.

Decision: `COVER-LEGAL-HALFSTRIP-GRID-CANDIDATE`.

The next proof object is a cellwise continuity/enclosure certificate. It must
bound Q and every transfer/error term over each gamma/delta cell, split cells
if the owner/book or selector changes, and retain the actual selected-owner
quantifier order.

Artifact: `results/2095_cover_legal_halfstrip_grid_m6400.json`.
Script: `scripts/routea_cover_legal_halfstrip_grid_2095.py`.

Scope correction (record 2104): `GAMMAS_EXT` under-approximates the actual
closed-ball zero owner. Record 2100 finds 11-20 omitted numerical known-zero
positions on representative rows. The 20/20 sign is valid only for the
truncated model and must not be promoted to a cellwise actual-owner COVER
premise; the proposed direct interpolation from these rows is withdrawn.
