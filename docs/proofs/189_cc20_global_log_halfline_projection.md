# Proof 189: Global Logarithmic Half-Line Projection

## Route obligation

Provide the genuine full-line logarithmic `L2` half-line projection needed by
the future crossing operator. The producer must be lower than the eventual
trace consumer and must not store a trace conclusion.

## What is proved

`ConnesWeilRH/Source/CC20Concrete/GlobalLogCrossing.lean` defines

```text
cc20PositiveHalfLineProjection : cc20GlobalLogCrossingL2 →L[ℂ]
  cc20GlobalLogCrossingL2
```

for `cc20PositiveHalfLine = Set.Ici 0`. Its construction uses
`memLp_indicator_iff_restrict`, with
`(Lp.memLp u).restrict cc20PositiveHalfLine` as the restricted-measure
`MemLp` witness. This is required because `Ici 0` has infinite Lebesgue
measure; a finite-window `indicatorConstLp` construction would not model the
desired half-line carrier.

The exported theorems are:

```text
norm_cc20PositiveHalfLineProjectionLinearMap_le
cc20PositiveHalfLineProjection_coeFn
cc20PositiveHalfLineProjection_idempotent
```

They establish respectively the contraction bound, the almost-everywhere
indicator formula, and `P_+^2 = P_+`.

## Verification

The import-facing audit is
`ConnesWeilRH/Dev/GlobalLogCrossingAudit.lean`. It checks the declarations and
prints their axioms. The output contains only:

```text
propext
Classical.choice
Quot.sound
```

Retained-cache WSL verification commands and results:

```text
lake build ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing
Built ... GlobalLogCrossing (2946 jobs)

lake env lean ConnesWeilRH/Dev/GlobalLogCrossingAudit.lean
axioms: propext, Classical.choice, Quot.sound

lake build ConnesWeilRH.Source.CC20Concrete
Built ... CC20Concrete (3505 jobs)
```

## Translation input

The same module defines

```text
cc20GlobalLogTranslation b : cc20GlobalLogCrossingL2 →ₗᵢ[ℂ]
  cc20GlobalLogCrossingL2
```

by reusing `measurePreserving_add_right volume b` and
`Lp.compMeasurePreservingₗᵢ`. The theorems
`cc20GlobalLogTranslation_coeFn`, `norm_cc20GlobalLogTranslation`, and
`cc20GlobalLogTranslation_neg_apply` prove
`U_b u(t)=u(t+b)` almost everywhere, exact norm preservation, and
`U_b U_(-b)=I`. The inverse proof uses
`QuasiMeasurePreserving.ae_eq` to pull an a.e. equality through the outer
translation; it does not substitute a shifted point into an untransported
a.e. statement.

## Crossing composition

The bounded operator

```text
cc20SingleCrossingOperator b = (I-P_+) U_(-b) P_+
```

is defined as a composition of continuous linear maps. The theorem
`cc20SingleCrossingOperator_apply` exposes that exact composition. The object
contains no stored crossing scalar, trace value, or trace-class certificate.
The theorem `cc20NegativeHalfLineProjection_coeFn` additionally identifies
`I-P_+` almost everywhere with the `Iio 0` indicator, making the intended
positive-to-negative half-line geometry explicit at the function level.

## Boundary

This proof does not establish that a smoothed composition involving the
crossing block is trace-class, prove trace cyclicity, or identify a basis trace
with the previously proved diagonal scalar integral. Therefore it does not
supply finite-S positivity, the post-`Q` compact remainder, or an unconditional
proof of `_root_.RiemannHypothesis`.
