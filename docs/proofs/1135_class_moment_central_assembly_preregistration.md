# 1135 - central class-moment assembly and endpoint budget

Date: 2026-09-05.

Status: PRE-REGISTRATION, committed before implementation/builds.
Consumer: the true `classMoment 0`/`classMoment 2` producer feeding records
1132--1134 and the healthy `CompactLog`, B5-shaped Hbox chain.  RH is not
claimed.

## 1. Purpose

Record 1134 proves that each one-sided endpoint tail of every class moment at
radius `r = 99/100` has norm strictly below `10^-15`.  This record supplies the
exact assembly layer that consumes those bounds.  For an even moment, reflection
identifies the left and right tails, so the full moment is the central interval
integral plus twice the right tail.  The central interval is therefore the only
remaining analytic producer for the registered `I_0` and `I_2` boxes.

The point of this brick is ownership and error accounting, not a stored target
value.  A future central certificate must still provide visible lower and upper
comparison functions and prove their integral values through the 1132/1133
carrier.  This record merely transports such a central certificate to a whole-
line moment certificate with the explicit `2 * 10^-15` endpoint budget.

## 2. Registered declarations

1. Define the rational central radius `99/100` and the corresponding central
   interval integral of `classMomentIntegrand`.
2. Prove reflection of the class-moment integrand for even moment indices and
   identify the left endpoint tail with the right endpoint tail.
3. Prove the exact three-interval decomposition of `classMoment n` into left
   tail, central integral, and right tail.
4. Define a data-bearing central certificate using the existing
   `IntegralEnvelope`; do not store the whole-line conclusion as a field.
5. For even `n`, derive whole-line lower and upper bounds from the central
   envelope and the two 1134 tail bounds.  The concrete `I_0`/`I_2` interval
   membership remains a separate central-envelope obligation.

## 3. No-go / honesty gates

- No numerical integration, target moment literal, Hbox/M-side enclosure,
  `(iv)` defect bound, detector positivity, SourceRH, or RH conclusion is
  introduced.
- The endpoint budget is strict and explicit; no rounding from `2 * 10^-15`
  into the registered interval is silently permitted.
- The central envelope must retain its pointwise inequalities and exact
  comparison-integral values.  A structure containing only the desired whole-
  line bounds is not a producer.
- No route-map conclusion changes; this remains a true class-window input to
  the healthy B5 consumer.

## 4. Acceptance gates

- G1: the owning module and paired audit build through the canonical WSL
  resource runner with the success footer and zero `^error:` lines.
- G2: every audited declaration has exactly
  `[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.
- G3: a fidelity example constructs a symbolic central envelope and obtains
  the corresponding whole-line transport without introducing analytic data.
- G4: staged-diff hygiene is clean; no local paths or private artifacts enter
  the record.
- G5: the final addendum states clearly that only assembly landed if the
  central pointwise envelope is not yet instantiated.

The remaining true-data task after this record is the central interval
enclosure itself.  The Hbox chain, `(iv)`, same-detector semi-local positivity,
SourceRH, and RH remain open.

## 5. Post-run addendum (2026-09-05, after builds 1--5)

VERDICT: ASSEMBLY LANDED; CENTRAL TARGET ENVELOPE REMAINS OPEN.

The preregistration commit `8d52357` preceded implementation.  The landed
module is `ConnesWeilRH.Dev.C1ClassMomentCentralAssembly`, paired with its
audit module.  The implementation provides:

* the exact `99/100` central radius and three-interval decomposition;
* even-moment reflection of the two endpoint tails;
* a data-bearing `centralMomentEnvelope` adapter to record 1132; and
* strict whole-line transport with endpoint budget `2 / 10 ^ 15`, consuming
  record 1134's two one-sided tail bounds.

The audit also constructs the deliberately coarse symbolic envelope
`0 <= I_0 <= 2`.  This is a fidelity check for the assembly and is not the
registered `I_0`/`I_2` numerical producer.

Canonical build 5 on the ext4 mirror completed successfully with 3664 jobs,
zero `error:` lines, zero `sorryAx`, and no warnings originating in the new
modules.  Fourteen audited declarations printed exactly
`[propext, Classical.choice, Quot.sound]`.  The implementation chain after
the preregistration was `36441f8`, `f37f311`, `1ce89e6`, `bd12644`, and
`e1c0925`.

No route-map conclusion changes.  The genuine central interval envelope for
the registered `I_0` and `I_2` boxes, Hbox, `(iv)`, same-detector semi-local
positivity, SourceRH, and RH remain open.
