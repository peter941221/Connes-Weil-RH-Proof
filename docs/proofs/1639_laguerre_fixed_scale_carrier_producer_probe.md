# 1639 — Laguerre fixed-scale carrier producer probe

Date: 2026-09-18

Status: strong numerical producer candidate, not a theorem. This record serves
the formal compact-observable interface of 1636 and the healthy-CompactLog B5
carrier consumer. The carrier base remains formally open; RH is not claimed.

## 1. Trial space

The previous bump-width family became Gram-ill-conditioned. The new probe uses
the half-line Laguerre functions

```text
h_n(x) = exp(x/2) L_n(-x) 1_{x<0}.
```

These are orthonormal in `L2((-infinity,0])`, so their Fourier transforms are
natural Hardy-side inputs and the finite-section Gram matrix is close to the
identity. The actual multiplier is tested at fixed `lambda`; the section
dimension is then increased.

The compact observable is fixed throughout the run: the rank-two projection
onto the rational Hardy vectors with spatial profiles `h_3` and `h_4`.

## 2. Controls

The degenerate model passes its two essential controls:

```text
model m=1, lambda=1, dim=14: sigma_min = 9.999e-1 (N=32768)
model m=1, lambda=1, dim=14: sigma_min = 9.999e-1 (N=16384)
```

Thus the observed collapse is not caused by the Hardy projection pipeline
alone. At model `m=1, lambda=0.2`, the same Laguerre family reaches
`sigma_min = 7.73e-4` at dimension 14, matching the known nonempty finite-window
model behavior.

## 3. Actual-symbol readback

At resolution `N=32768`, the fixed-scale results are:

```text
lambda   dim=1       dim=8       dim=12      dim=14       observable mass at dim=14
0.2      6.37e-1     3.15e-1     4.83e-3     2.11e-4       0.9467
0.1      6.17e-1     1.64e-1     3.50e-4     1.82e-5       0.9524
0.05     6.15e-1     9.71e-2     8.05e-5     3.10e-6       0.9558
0.02     6.13e-1     7.76e-2     7.40e-5     3.63e-7       0.9587
```

The lower-resolution cross-check gives:

```text
lambda   sigma(dim=14), N=16384   observable mass
0.2      2.1027e-4                 0.9467
0.1      1.7874e-5                 0.9525
0.05     3.0240e-6                 0.9557
0.02     3.4741e-7                 0.9587
```

The end values are stable at the displayed scale. Unlike the 1637 bump
translate section, the fixed-scale Laguerre section keeps decreasing as the
input dimension grows, while the fixed compact observable retains roughly
95 percent of the minimizing vector's mass.

## 4. Mathematical meaning and boundary

This is the exact numerical shape required by 1636:

```text
fixed D_lambda x_n -> 0,
bounded normalized x_n,
fixed compact observable K x_n does not -> 0.
```

If the following three analytic statements are proved for the actual symbol,
1636 immediately yields a nonzero carrier kernel:

1. the Laguerre system is complete in the committed Hardy-side input space;
2. the finite-section defects converge to zero at one fixed positive lambda;
3. the rank-two rational observable has a strictly positive limiting lower
   bound on the normalized minimizing sequence.

The experiment does not prove any of these statements. In particular, finite
dimension 14 is not an infinite-dimensional limit, and the FFT truncation
must be removed analytically. The result is therefore a producer candidate,
not a carrier theorem.

## 5. Reproducibility

The main script is `scripts/carrier_laguerre_fixed_scale_1639.py`. The
supporting width-family calibration is retained in
`scripts/carrier_fixed_scale_rich_trial_1638.py`. Both use the same Fourier
convention and symbol evaluator as records 1630--1638.
