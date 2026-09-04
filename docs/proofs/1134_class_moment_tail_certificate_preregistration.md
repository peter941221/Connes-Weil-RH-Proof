# 1134 - class-moment exponential tail certificate

Date: 2026-09-05.

Status: PRE-REGISTRATION, committed before implementation/builds.
Consumer: the true `classMoment 0`/`classMoment 2` producer of records 1132
and 1133, hence the healthy `CompactLog`, B5-shaped Hbox chain.  RH is not
claimed.

## 1. Purpose

The class-moment integrand is supported on `[-1,1]`, and inside that interval
its weight is

```text
classUnitWeight x = exp (-2 / (1 - x^2)).
```

This record isolates the endpoint region before constructing the central
finite-power envelope.  For `r < |x| ≤ 1`, monotonicity of the exponential
gives a uniform bound by `exp (-2/(1-r^2))`; the interval-integral norm
estimate then controls both endpoint tails.  The registered rational choice
`r = 99/100` is paired with a proved Taylor bound for `exp (-1)` and repeated
exponential multiplication, yielding a tail bound below `10^-15`.

## 2. Registered declarations

1. An exact interior identity rewrites the squared class bump as the displayed
   exponential.
2. A generic pointwise tail bound controls `classUnitWeight` whenever
   `r ≤ |x| ≤ 1`.
3. The corresponding class-moment integrand norm bound is derived using
   `|x|^n ≤ 1`.
4. Right and left interval-integral tail bounds follow from the Mathlib norm
   integral estimate.
5. A concrete rational `r = 99/100` corollary proves each one-sided tail is
   strictly smaller than `10^-15`.

## 3. No-go / honesty gates

- No numerical integration, stored target moment, Hbox, M-side enclosure,
  `(iv)` defect bound, detector positivity, SourceRH, or RH conclusion is
  introduced.
- The tail result is only a reduction.  The central interval still requires
  an actual finite-power envelope and its exact integral comparison values.
- No route-map conclusion changes; this remains on the healthy class-window
  B5 consumer.

## 4. Acceptance gates

- G1: owning and paired audit modules build through the canonical WSL runner
  with the success footer, zero `^error:` lines, and zero `sorryAx`.
- G2: every audited declaration has exactly
  `[propext, Classical.choice, Quot.sound]`.
- G3: the exponential identity and tail inequalities are proved from the
  class-bump definition and order properties, not from a numerical oracle.
- G4: the `99/100` tail bound reduces to exact rational arithmetic after the
  explicit `Real.exp_bound` input.
- G5: staged-diff hygiene is clean and RH remains unclaimed.

The post-run addendum will state whether the generic and concrete tail
certificates landed.  The central moment enclosure and RH remain open.

## 5. Post-run addendum (2026-09-05, after builds 1-6)

VERDICT: LANDED.

The implementation is committed as `5795fd4`.  The final canonical focused
build was `build-6`: `Build completed successfully (3663 jobs)`, with zero
`^error:` lines, zero `sorryAx` occurrences, and zero warnings originating in
the two new modules.  The paired audit printed all seven registered
declarations, each with exactly `[propext, Classical.choice, Quot.sound]`.
The evidence log is `build-logs-1134_build6.log`.

The six-build sequence repaired only Lean elaboration/interface issues: an
over-broad rewrite, a closed branch with an extra tactic, strict-versus-weak
endpoint inequalities, negative-endpoint absolute-value normalization, the
argument order of `pow_lt_pow_left₀`, and two omitted namespace opens in the
audit.  No hypothesis was weakened and no numerical oracle was added.  The
`99/100` certificate uses only the explicit `Real.exp_bound` Taylor estimate,
exact rational arithmetic, and the proved exponential power identity.

This record closes the endpoint-tail part of the true `classMoment 0`/`2`
producer.  It does not close the central interval envelope, the M-side Hbox,
the real `(iv)` defect contraction, detector-specific semi-local positivity,
SourceRH, or RH.
