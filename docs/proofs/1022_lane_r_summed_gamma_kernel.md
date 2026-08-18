# 1022 - Lane R summed Gamma_R kernel screen

Date: 2026-08-18.

Probe: `docs/proofs/1022_lane_r_summed_gamma_kernel_probe.py`.

## Verdict

The correct Gamma_R sign object is a constant plus a finite prefix of the
paired profile series, with a norm-controlled tail. The direct numerical
screen is strongly negative on the tested triple-vanishing prime-free space,
but high profile indices retain small positive directions. Thus neither a
termwise proof nor an autonomous tail-sign proof is valid.

This document records a reusable exact Lean decomposition and numerical route
screen. It is not a proof of universal Lane R, global spectral
nonnegativity, or RH.

## Exact Lean Owner

`Dev/C1XiCenterTwoGammaSummedKernel.lean` defines

```text
I_n(F) = integral_{y>0} gammaRArchProfileTerm(F,n,y) dy
T_N(F) = sum_{k>=0} I_(k+N)(F).
```

The public theorem
`integralOn_archimedeanIntegrand_eq_profilePrefix_add_tail` proves, for every
compact-log test `F`,

```text
integral_{y>0} archimedeanIntegrand(F,y) dy
  = sum_{0 <= n < N} I_n(F) + T_N(F).
```

The companion theorem
`archimedeanTerm_eq_constant_add_profilePrefix_add_tail_re` adds the exact
constant term `C = log(4*pi) + gamma`, and
`tendsto_gammaRArchProfileTail_zero` proves `T_N(F) -> 0`.

This is the same paired Gamma_R family already used by the center-2 readback:

```text
integralOn_archimedeanIntegrand_eq_tsum
normalized_gammaR_centerTwo_re_eq_archimedeanTerm
```

The new API only makes the finite-prefix/tail split explicit. It does not
produce a sign inequality.

WSL2 verification built the owner and import-facing probe at 3538/3539 jobs.
`#print axioms` reports only:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`, RH root axiom, or unconditional RH theorem is used.

## Numerical Object

The probe uses an L2-orthonormal sine basis on `[-r,r]`, then imposes the
three exact quadrature moment rows

```text
laplaceAt(g,0) = laplaceAt(g,1/2) = laplaceAt(g,1) = 0.
```

At `r = 0.345`, the convolution square radius is `0.690 < log(2)`, so the
sample is prime-free. Each paired profile uses the analytic inner integral of
`exp(-(2*n+1/2)*abs(x-y))`; Gauss-Legendre is used only for the remaining
smooth outer action. The independent direct calculation uses the compact
support archimedean density plus its analytic tail.

The table uses the exact Lean convention: prefix length `N` means indices
`0 <= n < N`. The tail column is the finite remainder from `N` through the
3201-term numerical reference, not a claim about the true infinite tail.

```text
+-----------------+-------------------------------+-------------------------------+
| prefix length N | constant + prefix spectrum    | tail to 3201-term reference   |
+-----------------+-------------------------------+-------------------------------+
|               1 | [+1.10844145, +1.11386176]    | [-3.53883600, -1.97803844]    |
|               2 | [+0.44278089, +0.47388384]    | [-2.87321520, -1.33740720]    |
|               3 | [+0.04458550, +0.11727769]    | [-2.47508181, -0.97990575]    |
|               4 | [-0.23853581, -0.11342461]    | [-2.19203589, -0.74828878]    |
|               6 | [-0.635083997, -0.38915884]   | [-1.79565406, -0.47109765]    |
|              21 | [-1.75237864, -0.80104678]    | [-0.67909728, -0.05927832]    |
|             161 | [-2.40739238, -0.86428297]    | [-0.02315926, +0.00014074]    |
|            1281 | [-2.43016959, -0.86442420]    | [-0.00021912, +0.00009925]    |
+-----------------+-------------------------------+-------------------------------+
```

The 3201-term profile reference has spectrum

```text
[-2.43038594, -0.86432766].
```

An independent direct archimedean calculation on a 6001-point uniform grid
has spectrum

```text
[-2.43040908, -0.86430999],
```

with maximum matrix-entry difference `2.373e-05`. This is a cross-check, not
a rigorous discretization certificate.

Quadrature sizes 600, 1800, and 3000 agree on the displayed prefix values;
the moment residual is at most `5.6e-17` and L2 orthonormality error at most
`8.9e-16` in the recorded runs.

## Consequence

The first finite prefix that is negative definite in this screen is `N = 4`.
That fact alone is not a theorem for the full compact-log test space. More
importantly, the small positive tail directions at `N >= 161` rule out the
following false target:

```text
T_N(g^* * g) <= 0 for every sufficiently large N.
```

The viable analytic target has two coupled estimates on the same
triple-vanishing prime-free owner:

```text
constant(F) + sum_{n<N} I_n(F) <= -epsilon * F(0)
abs(T_N(F)) <= epsilon * F(0).
```

Their sum would imply the desired archimedean nonpositivity. The first is a
finite constrained-kernel inequality; the second is a genuine tail norm
estimate. The Lean decomposition above is the interface for those two
producers. Numerical eigenvalues are evidence for choosing this target, not
facts transported into Lean.

## Reproduction

Run in WSL2:

```text
~/verify/probe-venv/bin/python \
  docs/proofs/1022_lane_r_summed_gamma_kernel_probe.py \
  --radius 0.345 --basis-size 16 --quadrature-size 1800 \
  --reference-length 3201 --direct-grid 6001
```

The `--prefix-lengths` argument uses the Lean convention above. Increasing
the reference length improves agreement with the direct archimedean check;
it does not convert the numerical result into a proof.
