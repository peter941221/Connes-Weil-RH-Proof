# 1132 - class-moment integral certificate carrier

Date: 2026-09-05.

Status: PRE-REGISTRATION, committed before implementation/builds.
Consumer: the true `classMoment 0`/`classMoment 2` interval premises of record
1131, hence the healthy-`CompactLog` B5 Hbox chain.  RH is not claimed.

## 1. Purpose

Record 1129 reduces the actual class-Gram owner to the two integrals

```text
I0 = ∫ x, classUnitWeight x
I2 = ∫ x, x^2 * classUnitWeight x.
```

Record 1131 already transfers the two registered rational intervals to the
q28 Gram box, but deliberately leaves membership of the actual integrals
open.  This record fixes the proof-carrying interface for the missing analytic
producer.

The carrier is deliberately lower-level than a numerical value.  A certificate
will contain two globally integrable comparison functions, pointwise lower and
upper inequalities on the compact interval `[-1,1]`, and exact interval
integral values.  The generic theorem derives the target integral bounds from
those fields.  A future concrete certificate must prove its pointwise
inequalities from the actual `classBump` definition and must evaluate its
comparison integrals by proved calculus identities; a stored pair of target
bounds is not accepted as a producer.

## 2. Registered declarations

1. `IntegralEnvelope` is a data-bearing structure for a real integrand on an
   ordered interval.  It stores interval integrability of the lower/target/
   upper functions, their pointwise order on `Icc a b`, and the proposed lower
   and upper interval-integral values.
2. `integral_bounds_of_integralEnvelope` derives
   `lo ≤ ∫ f` and `∫ f ≤ hi` from the carrier.  The proof uses only
   `intervalIntegral.integral_mono_on` and the stored value inequalities.
3. `classMoment_bounds_of_integralEnvelope` specializes this to the actual
   whole-line `classMoment n`, using the already proved compact support and
   interval reduction for `x^n * classUnitWeight x`.
4. A concrete `I0`/`I2` producer is **not** claimed in this record.  The next
   implementation phase must supply finite polynomial/exponential envelopes
   and exact rational integral evaluations, then apply this carrier to the
   radius-`10^-15` intervals registered by 1131.

## 3. No-go / honesty gates

- No `axiom`, `sorry`, `admit`, `True`, `Set.univ` producer, or direct field
  equal to the target conclusion is allowed.
- Merely defining `lo`/`hi` to be the target integral is not a certificate;
  the comparison functions and their pointwise proofs must remain visible.
- The record does not widen or alter q28 boxes and does not change the route
  map.  If a concrete envelope cannot meet the registered radius, the result
  is a failed certificate attempt, not a route verdict.

## 4. Acceptance gates

- G1: the implementation and paired audit module build with the canonical
  WSL resource-runner; acceptance is the log footer plus zero `^error:` lines.
- G2: every exported declaration printed by the audit has exactly
  `[propext, Classical.choice, Quot.sound]` and the log has zero `sorryAx`.
- G3: a fidelity example instantiates the generic theorem for a symbolic
  interval envelope without introducing a new analytic assumption.
- G4: staged-diff hygiene has no local paths, private artifacts, or hidden
  conclusion fields; the source tree remains the authority.

The post-run addendum will state whether only the carrier landed or whether a
concrete base-moment producer also landed.  Until the latter is proved, 1131
and RH remain open.

