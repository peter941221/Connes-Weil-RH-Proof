# Record 1130: class Gram moment-polynomial consumer preregistration

Status: partial / landed for the algebraic consumer; the interval-transfer
producer remains pending.

Consumer: the healthy-`CompactLog`, B5-shaped detector-specific semi-local
chain, through the true-data class-window `Hbox-G` input consumed by
`C1T2Assembly`.

## 1. Motivation

Record 1129 proved that the unit class weight

```text
w(x) = classBump(x)^2,
I_n = ∫ x, x^n * w(x)
```

has zero odd moments and that every even moment after `I_2` is determined by
the exact recurrence.  The remaining Gram-side work must now make the
polynomial calculation explicit at the owner boundary.  This avoids treating
the 20 same-parity Gram entries as independent numerical facts and gives a
single, auditable consumer for the two base moments `I_0` and `I_2`.

## 2. Registered targets

1. Expose the unit-scale identity
   `classGramUnitEntry i j = ∫ x, P_i(x) * P_j(x) * w(x)` for the first eight
   recursively defined Legendre polynomials.
2. Prove in Lean the finite polynomial expansions for all first-eight
   same-parity products, using the actual `legendrePoly` definition and the
   `classMoment` owner.  Odd products must continue to reduce to zero through
   the already landed parity theorem.
3. Use `classMoment_even_step` to derive the finite moments needed by those
   products from `I_0` and `I_2`, with exact rational coefficients.
4. Provide a theorem of the form
   `q28_classGram_bounds_of_baseMomentBounds`: if two explicit rational
   intervals contain the actual `I_0` and `I_2`, then the committed q28 `GLo`
   and `GHi` boxes contain the actual scale-2 class Gram matrix.
5. Keep the base-moment inequalities themselves as a separate producer
   obligation unless a fully checked analytic interval certificate is included
   in this record.  A proposition carrying those inequalities as fields is an
   interface, not evidence that the inequalities are true.

## 3. Integrity and scope

All identities are exact real equalities or exact rational implications.  No
floating-point value, quadrature output, stored Gram entry, `Hbox`, M-side
bound, `(iv)` defect estimate, detector-specific positivity, `SourceRH`, or RH
theorem is claimed merely by installing this consumer.  The record may close
the Gram side only if its interval producer proves the base inequalities from
the actual `classBump` integral rather than assuming them.

The theorem serves the healthy-`CompactLog` B5 consumer and does not create a
universal B1 positivity theorem, a density lemma, or a ROOT-to-detector arrow.

## 4. Acceptance gates

G1. The owner and paired audit build through the resource runner with the
success footer, zero `^error:` lines, and zero `sorryAx`.

G2. Every audited declaration has exactly
`[propext, Classical.choice, Quot.sound]`.

G3. The polynomial-to-moment bridge unfolds the actual class-window and
class-weight definitions; no Gram entry is replaced by a named hypothesis or
by committed numerical data.

G4. Any base-moment interval producer is accepted only when its inequalities
are proved from a displayed analytic certificate with exact rational
arithmetic.  A conditional consumer theorem alone is labelled as such.

G5. Staged-diff hygiene finds no private paths, generated build artifacts, or
hidden proof terms.

RH NOT claimed.

## 5. Post-run addendum (2026-09-05, after build 39)

VERDICT: PARTIAL / LANDED.

Targets 1--3 are implemented in the paired modules
`C1ClassGramMomentConsumer.lean` and `C1ClassGramMomentModel.lean`, with
corresponding audit modules.  The landed declarations expose the weighted
polynomial integral, its finite moment expansion and linearity bridges, the
unit Gram-entry identity, and the exact first-eight class Gram matrix model
in terms of `classMoment 0` and `classMoment 2`.  The even-moment recurrence
is consumed explicitly; the model is not imported as stored numerical data.

The initial hand-entered model table contained coefficient mistakes.  Exact
rational reductions and the Lean residual goals detected them during the
focused build sequence; the table was corrected before the accepted build,
and no incorrect table was committed as the final implementation.

Build-39 evidence is the ext4-mirror log `1130_build39.log`: success footer
`Build completed successfully (3660 jobs)`, zero `^error:` lines, zero
`sorryAx`, and zero warnings from the four 1130 modules.  The paired audits
reported 36 unique declarations in total, each with exactly
`[propext, Classical.choice, Quot.sound]`.

Target 4 is deliberately not claimed.  No theorem
`q28_classGram_bounds_of_baseMomentBounds` was installed, and this record
does not assert that the committed q28 boxes contain the actual class Gram
matrix.  The required exact base-moment interval producer is also absent.
Accordingly, the true-data `Hbox-G` input, the M-side input, the 1116c defect
estimate, the same-detector semi-local positivity step, `SourceRH`, and RH
remain open.

The integrity and route gates remain unchanged: this is an algebraic
consumer for the healthy-`CompactLog` B5 chain, not a universal B1 result,
not a density lemma, and not an RH claim.
