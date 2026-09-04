# 1133 - finite power-polynomial integral engine

Date: 2026-09-05.

Status: PRE-REGISTRATION, committed before implementation/builds.
Consumer: the true `classMoment 0`/`classMoment 2` envelope producer of record
1132, hence the healthy `CompactLog` B5 Hbox chain.  RH is not claimed.

## 1. Purpose

Record 1132 provides the generic transport from two comparison functions to
an interval for the actual class moment.  A concrete high-precision producer
needs comparison functions whose integrals are independently checkable.  The
first such calculus layer is a finite sum of powers with real coefficients:

```text
P(x) = Σ k ∈ s, c(k) x^k
∫ₐᵇ P(x) dx
  = Σ k ∈ s, c(k) (b^(k+1) - a^(k+1))/(k+1).
```

This record fixes that identity in Lean and supplies an adapter which builds
an `IntegralEnvelope` from pointwise polynomial bounds and the displayed
finite-sum value bounds.  The adapter still requires the pointwise
inequalities; it does not assert or import a numerical approximation.

## 2. Registered declarations

1. `finitePowerPolynomial` is a finite power sum over an explicit `Finset`.
2. `finitePowerIntegralValue` is its displayed algebraic integral value.
3. `intervalIntegral_finitePowerPolynomial` proves the exact interval
   integral by finite-sum linearity and `integral_pow`.
4. `integralEnvelope_of_finitePowerBounds` packages two such polynomial
   comparisons into the 1132 envelope carrier.
5. A specialized class-moment adapter supplies the already proved
   integrability of `classMomentIntegrand`; it leaves the pointwise and value
   bounds as explicit premises.

## 3. No-go / honesty gates

- No `axiom`, `sorry`, `admit`, `True`, `Set.univ`, or hidden target field.
- The finite-sum value is a definition whose equality with the integral is a
  proved theorem; target moment bounds remain consequences of visible
  comparison hypotheses.
- This brick does not instantiate the registered `10^-15` intervals and does
  not alter any route-map conclusion.

## 4. Acceptance gates

- G1: owning module and paired audit module build through the canonical WSL
  resource runner with the success footer and zero `^error:` lines.
- G2: every audited declaration has exactly
  `[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.
- G3: a finite rational-coefficient fidelity example reduces to an exact
  interval integral.
- G4: staged-diff hygiene is clean and no local paths/private artifacts are
  committed.

The post-run addendum will report whether the exact polynomial engine and its
adapter landed.  The actual exponential bump envelope and RH remain open.

## 5. Post-run addendum (2026-09-05, after builds 1-3)

VERDICT: LANDED (calculus engine only).

The preregistration commit `df4bd82` preceded the implementation.  After two
Lean v4.30 syntax/API corrections, build 3 completed successfully (3662
jobs), with zero `^error:` lines and zero `sorryAx` occurrences.  The audit
printed all five registered declarations, each with exactly
`[propext, Classical.choice, Quot.sound]`.

The landed declarations are the finite power-sum integral identity, its
interval-integrability theorem, the generic adapter to `IntegralEnvelope`,
and the class-moment adapter.  The exact rational-coefficient fidelity
example also compiles.  No concrete exponential envelope, registered
`10^-15` base-moment interval, Hbox certificate, or RH conclusion was added.
