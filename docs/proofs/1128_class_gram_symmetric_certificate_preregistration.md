# Record 1128 - symmetric reduction of the class Gram certificate

Date: 2026-09-04.  Status: PRE-REGISTRATION committed before code.

Consumer: the healthy-`CompactLog`, B5-shaped single-window Stage-B chain,
specifically the true-data `Hbox-G` certificate for the class-window Gram
owner.  This is certificate-size reduction on the active owner, not a
ROOT-window or universal B1 campaign.

## 1. Motivation

Record 1125 proves that the real class Gram matrix is symmetric, and record
1127 proves the opposite-parity entries are exactly zero.  The committed
q28/q38/q48 G endpoint matrices are also symmetric.  Therefore a future
integral certificate needs to establish bounds only on the upper triangle;
the lower triangle follows by exact rewriting, and the opposite-parity
upper-triangle entries are already discharged by parity.

## 2. Registered targets

1. Expose the entrywise symmetry of `classGramMatrix` in a rewrite-friendly
   form.
2. Prove exact transpose symmetry of `GLo` and `GHi` for q28, q38, and q48.
3. Prove a generic upper-triangle-to-full entrywise-bound theorem using the
   actual Gram symmetry and symmetric endpoint matrices.
4. Provide a q28 Hbox-G-facing wrapper whose only supplied integral bounds
   are for `i ≤ j` with opposite parity excluded; odd entries are discharged
   through record 1127.

The remaining same-parity integral inequalities are not proved here; this
record only reduces their independent count from 32 ordered entries to 20
upper-triangle entries.

## 3. Non-goals and integrity boundary

No quadrature, floating-point output, integral enclosure, M-side bound,
Stage-B defect estimate, detector-specific semi-local positivity,
`SourceRH`, or RH theorem is claimed.  No endpoint is widened or changed.

## 4. Acceptance gates

G1. The owning module and paired audit build through the resource runner with
the success footer, zero `^error:` lines, and zero `sorryAx`.

G2. Every declaration printed by the audit has exactly
`[propext, Classical.choice, Quot.sound]`.

G3. The wrapper consumes the actual q28 box endpoints and the actual record-
1127 odd-entry discharge, with the full conclusion still an entrywise bound
on `classGramMatrix`.

G4. Staged-diff hygiene finds no private paths, generated build artifacts,
hidden proof terms, or stored numerical conclusions.

RH NOT claimed.

## 5. Post-run addendum (2026-09-04, after builds 1-2)

VERDICT: LANDED.

The preregistration commit was `75b541c`; the module and audit were added in
`2ea39a5`, and the build-1 transpose-orientation fix was committed as
`93b39ff` before the accepted run.  The final resource-runner log is
`build-logs-1128_build2.log`.

Build 2 completed successfully (3657 jobs), with zero `^error:` lines and no
`sorryAx`.  The audit printed 9 declarations; after rejoining wrapped output,
all 9 had the unique axiom set
`[propext, Classical.choice, Quot.sound]`.  No declaration in the new module
introduced a warning.

The landed result is the exact Gram-entry symmetry, six q-endpoint symmetry
lemmas, a generic upper-triangle-to-full transport theorem, and the q28
Hbox-facing wrapper.  The wrapper leaves 20 same-parity upper-triangle
integral bounds to be supplied by a future true-data certificate.  No
integral enclosure, Hbox-G discharge, M-side result, defect estimate,
semi-local positivity, SourceRH, or RH theorem was claimed.
