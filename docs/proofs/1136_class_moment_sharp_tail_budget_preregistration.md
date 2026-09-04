# 1136 - sharp endpoint budget for the true class moments

Date: 2026-09-05.

Status: PRE-REGISTRATION, committed before implementation/builds.
Consumer: the true `classMoment 0`/`classMoment 2` producer feeding the q28
interval transfer and the healthy `CompactLog`, B5-shaped Hbox chain.  RH is
not claimed.

## 1. Purpose

Record 1135 assembled a central certificate with the coarse endpoint budget
`2 / 10 ^ 15`.  That budget is too wide to imply the registered q28 moment
boxes, whose half-width is `1 / 10 ^ 15`.  The same explicit exponential
estimate in record 1134 actually gives a much smaller rational bound.  This
record exposes a `10 ^ 40` tail bound and transports it through the 1135
assembly layer.

For even moments the integrand is pointwise nonnegative.  The lower whole-line
bound therefore keeps the central lower endpoint unchanged; only the upper
bound pays the two one-sided tails.  This is the correct sign-sensitive
budget for the later q28 adapter.

## 2. Registered declarations

1. Reprove the existing rational estimate
   `(1 - 99/100) * exp (-(2/(1-(99/100)^2))) < 1 / 10 ^ 40`
   from `Real.exp_bound`, exact power identities, and rational arithmetic.
2. Derive right and left endpoint interval-integral norm bounds below
   `1 / 10 ^ 40` for every class-moment order.
3. Prove pointwise nonnegativity of `classMomentIntegrand n` for even `n` and
   nonnegativity of its two oriented endpoint integrals.
4. Transport any genuine central `IntegralEnvelope` for an even moment to
   `lo <= classMoment n` and
   `classMoment n < hi + 2 / 10 ^ 40`, with no fabricated central value.
5. Provide q28-facing adapters whose central upper endpoint is lowered by
   exactly `2 / 10 ^ 40`; the actual central envelope remains a separate
   producer obligation.

## 3. Integrity and scope

- No quadrature, floating-point input, target moment literal, Hbox/M-side
  certificate, `(iv)` defect bound, detector positivity, SourceRH, or RH is
  introduced.
- The `10 ^ 40` estimate is proved from the already explicit exponential
  Taylor bound and exact rational comparisons; it is not imported as data.
- The q28 adapters consume, rather than manufacture, central comparison
  envelopes.
- The route map is unchanged; this remains a true class-window input to the
  healthy B5 consumer.

## 4. Acceptance gates

- G1: owning module and paired audit build through the canonical ext4 runner
  with the success footer and zero `^error:` lines.
- G2: every audited declaration has exactly
  `[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.
- G3: a fidelity example uses a symbolic central envelope and the sharp
  assembly theorem to produce a valid coarse whole-line inequality.
- G4: staged-diff hygiene is clean and contains no local paths or private
  artifacts.
- G5: the final addendum states that the central q28 envelope itself remains
  open if it is not instantiated.

RH NOT claimed.

## 5. Post-run addendum (2026-09-05, after build 1)

VERDICT: SHARP TAIL BUDGET LANDED; CENTRAL ENVELOPE REMAINS OPEN.

The preregistration commit `0dd6712` preceded implementation commit
`5fe7886`.  The module `C1ClassMomentSharpTailBudget`, with its paired audit,
proves both one-sided q99 tail norms below `1 / 10 ^ 40` from the explicit
Taylor bound and rational arithmetic.  It also proves nonnegativity for every
even class-moment integrand and uses that sign in the central-to-whole-line
assembly.  The q28-facing declarations consume central envelopes with upper
endpoint lowered by exactly `2 / 10 ^ 40`; they do not construct those
envelopes.

The canonical focused build log is `build-logs-1136_build1.log`:

- `Build completed successfully (3665 jobs)`;
- zero lines matching `^error:` and zero `sorryAx` occurrences;
- no warnings attributable to either new module; and
- all 8 audited declarations have exactly
  `[propext, Classical.choice, Quot.sound]`.

The true central `I_0`/`I_2` comparison envelopes, Hbox, `(iv)`,
same-detector semi-local positivity, SourceRH, and RH remain open.  No
route-map conclusion changes.
