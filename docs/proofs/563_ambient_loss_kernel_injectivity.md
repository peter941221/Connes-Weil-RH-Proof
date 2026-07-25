# Proof 563: Ambient Loss Has No Exact Zero Mode

Proof 562 showed that normalized Schur contractivity alone does not produce
the weighted graph-sine estimate. The next source-level question was narrower:
can the actual ambient loss column have an exact kernel on the real CCM24
carrier?

## Result

On the global logarithmic `L2` carrier, if `u` is supported in
`[log(lambda), infinity)` and `a > 0`, then

```text
(I + U_a) u = 0  ->  u = 0,
```

where `U_a u(t) = u(t + a)` is the genuine measure-preserving logarithmic
translation. The proof is an almost-everywhere (AE) induction. The support
condition gives zero below `log(lambda)`. Pulling the relation back by every
negative integer translation and using `ae_all_iff` gives a countable family of
valid relations. For any target `t`, choose `n` with
`t - n*a < log(lambda)`, then propagate the zero forward `n` steps.

The actual one-prime ambient loss column is

```text
ambientLossColumn(p,S) =
  primeEulerAmbientLossFactor(p)† * oldFrame(p,S),

primeEulerAmbientLossFactor(p)† =
  scale(p) * (I + U_(log p)),
```

with `scale(p) > 0`. The old polar frame image lies in the actual moving
Sonin intersection, whose first component is the real radial-support
subspace. Therefore:

```text
ambientLossColumn(p,S) x = 0  ->  oldFrame(p,S) x = 0  ->  x = 0.
```

The final step uses the existing polar-frame isometry, not an unproved inverse
on a larger carrier. The same channel identity then gives

```text
leftCoDefect(p,S) x = 0  ->  ambientLossColumn(p,S) x = 0  ->  x = 0.
```

## Lean Evidence

Source:
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedJuliaAmbientLossKernel.lean`

Audit:
`ConnesWeilRH/Dev/CCM24FiniteSCompletedJuliaAmbientLossKernelAudit.lean`

The four audited declarations are:

```text
ccm24LogRadialSupport_add_translation_injective
suffixEulerFrameAmbientLossColumn_eq_zero_imp_oldFrame_eq_zero
suffixEulerFrameAmbientLossColumn_injective
suffixEulerFrameLeftCoDefect_eq_zero_imp_eq_zero
```

## Boundary

Injectivity only removes an exact zero-mode obstruction. It does not imply
that the range is closed, that an inverse is uniformly bounded in `S`, or that
the raw signed row factors through the co-defect with a uniform norm bound.
Approximate kernels, Gate 3U, the finite-`S` sign, Burnol's identity, and RH
remain open.

Primary source context: Connes, Consani, Moscovici, "Zeta zeros and prolate
wave operators", arXiv:2310.18423v2,
https://arxiv.org/abs/2310.18423.
