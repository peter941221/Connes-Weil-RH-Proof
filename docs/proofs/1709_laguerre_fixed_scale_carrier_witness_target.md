# 1709 — Fixed-scale Laguerre carrier witness target

Date: 2026-09-20.

Status: formal candidate specification, not a carrier theorem and not an RH
claim. Consumer: the healthy-`CompactLog` B5 carrier base and, downstream,
the S3 source-compressed energy route.

## 1. Exact target

Fix one `lambda` with `0 < lambda < 1`. For `n >= 0`, use the Hardy-side
Laguerre functions

```text
h_n(x) = exp(x/2) L_n(-x) 1_{x < 0}.
```

Their committed Fourier/Laplace columns are

```text
H_n(xi) = (-1/2 - 2*pi*i*xi)^n / (1/2 - 2*pi*i*xi)^(n+1).
```

Let `U_lambda` be the committed exponential-times-Gamma multiplier and
`P_minus` the opposite Hardy projection. The required fixed-scale witness
statement is:

```text
there exist normalized v_d in span{H_0,...,H_(d-1)} such that
  ||P_minus (U_lambda v_d)|| -> 0,
  and a fixed finite-rank observable K has liminf ||K v_d|| > 0.
```

The compact-observable lower bound prevents weak escape to zero. Completeness
then yields a nonzero Toeplitz-kernel vector, hence a nontrivial source Sonin
carrier for the healthy B5 consumer.

## 2. Continuous, non-grid formulation

For the prefix degree `d`, define

```text
G_d[i,j] = <H_i,H_j>,
M_d[i,j] = <P_minus(U_lambda H_i), P_minus(U_lambda H_j)>.
```

The proof must establish at one fixed positive scale:

```text
min generalized eigenvalue(M_d, G_d) -> 0
```

and a positive limiting lower bound for the same fixed finite-rank
observable. The free-shift model has an exact incomplete-Laguerre integral
matrix, but it is only a calibration and cannot substitute for the Gamma
multiplier.

## 3. Four obligations

1. Prove Laguerre completeness and normalization in the committed Hardy
   half-space.
2. Prove the fixed-scale Gamma-symbol finite-section defect tends to zero,
   without FFT or finite-grid limits.
3. Prove the fixed-observable lower bound for normalized minimizers.
4. Prove the compact-observable limit and transport the resulting kernel into
   `sourceSoninCarrier`.

Finite-dimensional tables from records 1639--1642 discharge none of these
obligations; they remain candidate evidence only.

## 4. Route status

This record does not change the binding route map. It names the next concrete
carrier-base producer target. If obligations 2--4 are proved, the existing
S3/B5 consumers can be used. If they fail analytically, the remaining route
is direct spectral positivity, which is RH-equivalent.

No carrier nontriviality, S3 estimate, SourceRH, or RH conclusion is claimed.
