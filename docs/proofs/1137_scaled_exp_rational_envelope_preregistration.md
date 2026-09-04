# 1137 - scaled exponential rational envelope

Date: 2026-09-05.

Status: PRE-REGISTRATION, committed before implementation/builds.
Consumer: the true central `classMoment 0`/`classMoment 2` producer, hence the
healthy `CompactLog`, B5-shaped Hbox chain. RH is not claimed.

## 1. Purpose

The remaining central certificate must compare

```text
  exp (-2 / (1 - x^2))
```

with an exactly integrable rational function.  On `|x| <= 97/100`, put
`u = 2/(1-x^2)` and use `u/35 <= 1`.  A Taylor polynomial for
`exp (-(u/35))`, raised to the exact integer power `35`, gives a rational
function in `(1-x^2)⁻¹`; its pointwise error is controlled solely by
`Real.exp_bound` and a finite power-difference estimate.

This record lands only the pointwise approximation core.  The next integration
record will supply the rational-power antiderivative, the logarithm enclosure,
and the exact finite-sum comparison values.

## 2. Registered declarations

1. `expTaylor20` is the degree-19 Taylor sum on `[-1,1]`.
2. On `0 <= z <= 1`, its value is nonnegative and at most `1 + E20`, where
   `E20` is the explicit `Real.exp_bound` remainder.
3. The power-difference estimate transports the degree-19 error through the
   35th power without an unstated numerical constant.
4. `scaledClassWeightApprox` is pointwise within an explicit rational error of
   `classUnitWeight` on `Icc (-97/100) (97/100)`.
5. The same statement is provided for the order-2 integrand after multiplying
   by `x^2`.

## 3. Integrity gates

- No target moment, target interval, numerical oracle, `sorry`, `admit`, or
  RH conclusion is introduced.
- The only transcendental estimate is the explicit Taylor remainder already
  present in Mathlib; all scale factors and error budgets are rational.
- The central integral and its exact comparison value remain open after this
  record.

## 4. Acceptance gates

- G1: owning and paired audit modules build through the canonical WSL runner
  with the success footer and zero `^error:` lines.
- G2: every audited declaration has exactly
  `[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.
- G3: the scaling identity and pointwise error are proved from the class-bump
  definition, `Real.exp_bound`, and finite algebra.
- G4: staged-diff hygiene is clean and the route remains unclaimed.

The post-run addendum will state whether the pointwise core landed.  It will
not state that the central moments or RH are complete.

## 5. Post-run addendum (2026-09-05, after builds 1-9)

VERDICT: LANDED.

The preregistration commit `c26fb25` preceded the implementation.  The final
build used the canonical ext4 runner and completed successfully with 3666
jobs.  The log has zero `^error:` lines and zero `sorryAx` occurrences.  The
paired audit prints all five audited theorem declarations with exactly
`[propext, Classical.choice, Quot.sound]`; the remaining warnings are
pre-existing project or dependency warnings, with no warning from the new
modules.

The landed declarations are the pointwise degree-19 Taylor envelope, its
35th-power error transport, the `97/100` central-interval argument bounds,
and the resulting order-0 and order-2 class-moment integrand estimates.
The central rational integral, logarithm enclosure, target moment intervals,
true-data Hbox, the defect contraction, the same-detector semi-local gate,
and RH remain open.
