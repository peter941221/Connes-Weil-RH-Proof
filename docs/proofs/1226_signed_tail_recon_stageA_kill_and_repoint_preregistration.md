# 1226 - Signed-tail recon Stage A: aggregate-socket kill and route re-point (preregistration)

Date: 2026-09-09.

Status: PREREGISTERED before any Lean build or run for this record (law 42).
RH is not claimed.

Authority: Peter's 2026-09-09 directive to open the 1209 signed-tail
reconnaissance (the alternative branch of the record 1224 section 3g decision
point).  This record executes the recon's Stage A as a 1225-style Stage-0
target-satisfiability audit FIRST - the discipline mandated by record 1225
and by the 1222/1223 orphaned-campaign lesson: audit the target's
satisfiability from committed sources before spending the campaign week.

The audit terminated the recon's planned scope on day one: the primary exit
named by record 1209 ("a genuine signed trace/tail lower bound") is FORMALLY
DEAD for every healthy detector, by a three-line composition of committed
theorems, with no fourth-order machinery needed.  The secondary exit ("a
different aggregate decomposition") is classified, and its only surviving
shape is the universal non-bundled contract - the same re-point shape record
1225 established for the B5 side.  Sections 1-3 record the findings basis
(all file:line evidence, zero new numerics); section 4 registers the small
Lean landing; sections 5-7 register falsifiers, branches, and non-claims.

## 1. Findings basis (committed sources only)

F-A. The aggregate socket and its unconditional positivity readback.
`BombieriQuadraticAggregateP2BridgeData` (`C1BombieriP2Bridge.lean:149-165`)
carries fields `(n, t, ht, gamma, z, N)` plus two properties:

```text
field1  qw g = Re(star w ⬝ᵥ (bombieriHMatrix gamma t).mulVec w)
              + Re(shell-tail of spectralTerm g.convSq from N)
field2  -(Re finite form) <= Re(shell-tail)
```

`qw_nonneg_of_bombieriQuadraticAggregateP2BridgeData`
(`C1BombieriP2Bridge.lean:198-206`) proves `0 <= qw g` from the socket ALONE
- no eigen relation, no healthiness, no spectral hypothesis.  Its engine
`bombieriHMatrix_quadraticForm_eq_ofReal_nonneg`
(`C1BombieriFiniteQuadraticBridge.lean:75-84`) is unconditional in
`(t > 0, gamma, z)`: the finite weighted Hermitian form equals a nonnegative
real `S` (K*-Gram norm-square route).  Record 1208 states the design intent
verbatim: "The finite Hermitian term is nonnegative by the existing Bombieri
matrix theorem, so this lower bound closes `qw(g) >= 0`".

F-B. The healthy-detector sign.  `qw_neg_of_healthyDetectorData`
(`C1B5TargetSatisfiability.lean:63-71`, record 1225 L1): for EVERY `rho` and
`g`, `HealthyYoshidaDetectorData rho g` implies `qw g < 0` - empty context,
no zero-configuration hypothesis (the sign field reads through
`weilSquareSumPositive_iff_spectralWeilValue_neg` and the center-2 readback).

F-C. The missing guard.  `C1BombieriP2Bridge.lean` commits
`not_..._of_healthyDetectorData` guards for ALL five sibling sockets
(`:574` quadratic, `:627` mass, `:634` residual, `:641` spectral-tail,
`:648`/`:655` canonical variants) - but for the AGGREGATE socket only the
CONDITIONAL fourth-order no-go
`not_bombieriQuadraticAggregateP2BridgeData_of_fourthOrderTail_and_prefix`
(`:306-323`, record 1209), which needs `htail : FourthOrderSpectralTail`,
`hprefix` (orbit-controlled prefix anchor), and `hsmall` (geometric budget
below multiplicity).  The unconditional aggregate guard is derivable in
three lines from F-A + F-B but was never named.  Record 1226 lands it.

F-D. The consumer.  `sourceRH_of_right_bombieriQuadraticAggregateP2BridgeData`
(`C1BombieriP2Bridge.lean:749-762`) requires, for every right-of-line source
zero, ONE `g` carrying BOTH `HealthyYoshidaDetectorData rho.1 g` AND
`Nonempty (BombieriQuadraticAggregateP2BridgeData g)`.  This is the same
bundled shape record 1225 killed on the B5 side (L1+L2).

F-E. Fourth-order tail status (context, not load-bearing).
`exists_fourthOrderTail_halfDensityShift_convolutionSquare`
(`C1HealthyDetectorRootSupportExit.lean:150-155`) makes
`FourthOrderSpectralTail` a theorem for every compact-log test (explicit
`T = max 1 (|rho.im|+1)`, `epsilon = 1 + 81*C*(2*pi)^2`), and
`exists_dyadic_tail_start_with_budget_lt_xiMultiplicity`
(`C1SpectralTailBound.lean:284-290`) drives the absolute budget below any
multiplicity at a large enough dyadic start.  These remain valid for their
own content; section 2 shows the route ruling no longer needs them.

## 2. The kill algebra (exit (a) formally dead)

For ANY `g`, ANY parameter choice `(gamma, z, t, N)`:

```text
field1  =>  Re(tail) = qw g - form
field2  =>  Re(tail) >= -form
compose =>  qw g - form >= -form  =>  0 <= qw g          (committed :198-206)
healthy =>  qw g < 0                                      (committed L1)
---------------------------------------------------------
healthy /\ socket  =>  False        (empty context, all parameters)
```

Consequences, in order of strength:

(K1) The signed-tail lower bound (field2, the producer obligation record
1209 named as exit (a)) is REFUTED for every healthy `g` at every
`(gamma, z, t, N)`: were it true together with field1, `0 <= qw g` would
follow, contradicting L1.  The producer's entire finite-matrix freedom
(the choice of `gamma, z, t, N`) cannot rescue field2 - the algebra
collapses it to the gate sign itself.  Exit (a) is not 15% survival; it is
formally empty, exactly the "survival estimate estimated the wrong event"
pattern of record 1225's Cand-B withdrawal.

(K2) The consumer premise of F-D has no witness for any right-of-line zero
(`¬ ∃ g, healthy ∧ Nonempty(socket)` - empty context).  The consumer can
hold only vacuously (no right-of-line zero at all): it is RH-equivalent in
the circular sense, admitting no constructive production program.  This is
the record 1225 L3 ruling, re-derived on the Route-1 side.

(K3) The record 1209 no-go is SUPERSEDED-IN-CONTEXT: within the bundled
consumer, its spectral hypotheses (`htail`, `hprefix`, `hsmall`) are
unnecessary - the unconditional guard kills the conjunction without them.
Honest scope note: 1209's theorem is not literally implied by the guard
(its hypothesis set differs - it derives `qw < 0` spectrally without
assuming healthiness, and remains a valid standalone result about
spectralWeilValue negativity); what is superseded is its ROLE as the route
ruling for the aggregate socket.

## 3. Exit (b) classification (different aggregate decompositions)

Criterion (record 1225 section 5, re-used): a producer target is LIVE only
if its per-instance obligations can be TRUE - a conjunction that must carry
both signs on one test is dead regardless of construction skill.

(C1) Any successor socket `S` bundled with healthiness on the same `g` and
carrying an unconditional theorem `S => 0 <= qw g` dies by K1/K2 verbatim.
This covers every socket currently in `C1BombieriP2Bridge` (all have
committed `qw_nonneg_of_...` theorems) and any future socket of the same
bundled shape.  No new aggregate decomposition of the socket kind survives.

(C2) The surviving shape is the UNIVERSAL NON-BUNDLED contract: positivity
obligations quantified over the triple-vanishing class, never conjoined
with healthiness on one `g` - the L4 re-point of record 1225.  Its
instances can be true (the 1225 section 4 positive control exhibits a
MODEL witness: root-supported triple-vanishing `g` with `qw = +1.895768e-02
> 0`; law 65, MODEL only).

(C3) The aggregate-side analogue of L4 is landable by the identical
composition: `forall g` triple-vanishing `=> Nonempty(aggregate socket g)`
implies `SourceRH` through the committed capstone
`healthy_sourceRH_of_right_healthyDetectorData_and_spectral_nonneg` (the
same capstone L4 consumes, `C1B5TargetSatisfiability.lean:118-135`).  It is
registered below as declaration A4.  Honest content note: for a
triple-vanishing `g`, the socket obligation instance-reduces to `0 <= qw g`
plus the exact-identity plumbing of field1 (realizing `form = qw - tail` by
the `c^2`-scaling of `z` requires a strict-positivity base form - a
realizability question this record does NOT audit and no investment should
consume before its own Stage-0 audit).  A4 is therefore a formal re-point
marker, not a campaign recommendation; whether the Route-1 universal shape
or the L4 projection shape receives the next investment is Peter's fork at
the verdict.

## 4. Registered Lean landing (Stage A deliverable)

New module `ConnesWeilRH/Dev/C1AggregateSocketSatisfiability.lean` +
paired `...Audit.lean`.  Imports consume committed files read-only:
`C1BombieriP2Bridge`, `C1B5TargetSatisfiability`.  NO edit to any frozen
Line-B file.  Declarations:

```text
A1  not_healthy_of_bombieriQuadraticAggregateP2BridgeData
      {rho g} (p : Nonempty (BombieriQuadraticAggregateP2BridgeData g))
      (hg : HealthyYoshidaDetectorData rho g) : False
A2  no_rightZero_aggregateProducer_witness
      (rho : sourceNontrivialZeroSet) (_hright : 1/2 < rho.1.re) :
      ¬ ∃ g, HealthyYoshidaDetectorData rho.1 g ∧
             Nonempty (BombieriQuadraticAggregateP2BridgeData g)
A3  aggregateGuard_needs_no_spectralHypotheses
      {g} (p : BombieriQuadraticAggregateP2BridgeData g) {rho}
      (hg : HealthyYoshidaDetectorData rho g) : False
      -- the unconditional guard completing the not_ family of :574-:660;
      -- docstring records the K3 superseded-in-context relation to :306
A4  sourceRH_of_all_vanishing_aggregateSockets
      (hsockets : ∀ g, CC20VanishesOn C1.healthyCC20TestSpace
          cc20TripleFiniteVanishingSet g →
            Nonempty (BombieriQuadraticAggregateP2BridgeData g)) :
      RHDefinitionBridge.standard.SourceRH
```

Audit: `#print axioms` on A1-A4, each exactly
`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.

Build protocol: focused acceptance build of the two new modules on the warm
mirror (`/home/peter/rh`, ext4), acceptance by LOG CONTENT (success footer,
zero `error:` lines, axiom prints), not exit code.  Resource note: the
record 1225 section 4 official probe (invocation 3) may still be running on
the same machine; the focused build is cache-warm and light, expected to
slow the probe marginally - disclosed, accepted.

## 5. Falsifiers and branches

F1 (elaboration falsifier): any of A1-A4 fails to elaborate from the
committed parts as stated (e.g. a hidden hypothesis in
`bombieriHMatrix_quadraticForm_eq_ofReal_nonneg` or a capstone type mismatch
in A4) => the finding basis of section 1 is wrong somewhere; ABORT, diagnose
from the error, register a corrected amendment BEFORE any rerun (law 42).

F2 (audit falsifier): any audit line shows a nonstandard axiom or `sorryAx`
=> ABORT, fix root cause, rerun.

Branches (no third branch beyond these):
- FULL-LANDING: A1-A4 green + audit clean => verdict record 1226 with the
  route ruling (exit (a) dead, exit (b) classified, A4 re-point marker) and
  doc sync.
- PARTIAL: A1-A3 green, A4 blocked => land A1-A3, register A4's blocker as
  a finding, verdict records the same route ruling (A4 is a marker, not
  load-bearing for K1-K3).
- ABORTED-FINDING-INVALID: F1 fires on A1/A2/A3 => the kill algebra itself
  is in question; full diagnosis record before any further step.

## 6. Budget

Module + audit: ~150 lines total.  Focused build: 1-2 iterations, under one
hour on the warm mirror.  Verdict record + doc sync (map/freeze-card/README
touch only where the Route-1 ruling changes committed text): same window.
The planned ~1-week recon is NOT spent: Stage A terminated it from committed
sources, which is the outcome the 1225 Stage-0 discipline exists to produce.

## 7. What this record does NOT claim

No RH.  No witness of any socket or contract, universal or bundled.  No
claim that field1 of the aggregate socket is realizable for any concrete
`g` (the C3 scaling question is unaudited).  No retraction or edit of the
record 1209 fourth-order theorem, the 1207/1208 socket interfaces, or any
frozen Line-B module (all consumed read-only).  No interaction with the
running record 1225 section 4 probe - different files, different toolchain,
independent verdicts; the 1225 MATCH/MISMATCH outcome does not change any
finding registered here, and none of A1-A4 consumes any probe number.  All
model-level statements quoted (the +1.895768e-02 control value) remain
MODEL twins under law 65.  Line-B frozen modules stay frozen; this record
acts on the Route-1 socket file only through Peter's 2026-09-09 recon
directive and consumes it read-only.
