# 1981 — Powered-seed same-index screen

Date: 2026-09-25.

Status: SIGN_ONLY_TAIL_FAIL. This is a reproducible under-approximation
screen, not a GO certificate, determinant theorem, or RH proof.

## Changed assumption

Replace the interpolation seed transform by the rescaled ten-fold convolution
transform

```text
L_powered(s) = L_smoothSeed(0.5 * s)^10.
```

This changes the actual CompactLog seed and therefore requires a new support,
seed-mass, correction C2, base C4, and visible-prime proof in Lean. It is not
a post-processing rescale of the old owner.

## Owner and constants

The probe fixes one `rho`, `N = 4`, one base, one correction, and uses the
formal owner under-approximated by known zeta zeros, the hypothetical orbit,
and all healthy targets:

```text
rho              = 0.55 + 14.134725141734693 i
closed-ball R    = 48.208904068660146
known zeros      = 19
owner cardinality= 27
minimum separation = 0.05
base C4          = 152.9640664309362
base C2          = 25.135397681669808
correction C2    = 683.8644420520491
```

The source-zero list is only a known-zero under-approximation, so these are
stress values rather than formal-owner bounds.

## Same-index results

Each row recomputes the gate and tail with the same `n` and
`lambda = b / C`:

```text
n  C             b             D             det             lambda   L_n/lambda^2
0  +2.372e3      +2.684e6      +2.927e9      -2.582e11       1.131e3   2.144e28
1  -5.174e3      -7.784e6      -1.018e10     -7.947e12       1.504e3   3.056e27
2  -2.129e4      -2.485e7      -2.702e10     -4.227e13       1.167e3   1.259e27
3  -7.410e3      -8.072e6      -4.051e9      -3.513e13       1.089e3   3.610e26
4  +3.000e6      +4.314e9      +6.199e12     -1.420e16       1.438e3   5.220e25
```

The gate signs are present at `n = 0` and `n = 4`, but the same-index tail
ratio is greater than one by 25--28 orders of magnitude in every tested row.
The two sign rows therefore remain `SIGN_ONLY`; neither is GO.

Reproduction:

```text
python scripts/fourpoint_powered_seed_1981.py
```

The output is `results/1981_powered_seed_underapprox.json`.

## Decision

The powered seed is a legitimate conditioning improvement over the committed
smoothSeed selector, but it does not close the four-point span route. Before
any determinant Lean work, the next candidate must supply a proved powered-seed
CompactLog construction and a complete-owner tail ratio below one for one
common `n` and vertex `lambda`.
