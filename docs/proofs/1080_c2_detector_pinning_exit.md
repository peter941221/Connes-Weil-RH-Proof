# 1080 - consumer #2 EXIT: the pinned healthy log detector, landed in Lean

Date: 2026-09-01. Follows 1077/1078/1079 (numerical pinning of the detector at
zero #2).  This record lands the LEAN half of the station named by
`RH_MAINLINE_FREEZE.md` "Allowed Work" item 2: *a genuine compact-log detector
with explicit support radius and finite visible-prime set*.

## 1. Scope decision (what "closing consumer #2" means)

The freeze doc splits the healthy-owner chain as

    C2: selected detector + finite visible primes   [healthy CompactLog owner]
    C3: detector-specific semi-local positivity

Inspection of the owner (`C1HealthyYoshidaDetector.lean`,
`C1HealthyYoshidaMinimalInterpolation.lean`, `C1SameOwnerWeil.lean`) shows the
detector OBJECT is exactly the existentially packaged test - the sign field
(`weilSquareSumPositive` = `0 < archimedeanTerm g.convolutionSquare`, via the
already-landed reduction lemmas) is consumer 3's opening obligation, not part
of the C2 deliverable.  Consumer #2 is therefore closable WITHOUT any sign
proof, by promoting the two remaining implicit facts to explicit named
statements: the explicit support radius (already a hypothesis of the
interpolation theorem) and the finite visible-prime set (previously only an
indirect corollary `finitePrimeSum = 0`).

## 2. What landed (`ConnesWeilRH/Dev/C1HealthyDetectorPinning.lean`)

1. `convolutionSquare_support_logTwo_of_rootSupport_logTwoHalf` - square
   support transport: root window `[−log 2/2, log 2/2]` implies the Hermitian
   square sits in the open prime-free window `(−log 2, log 2)`.
2. `globalPrimeIndexSet_eq_empty_of_support_subset_open_log_two` - a square
   supported in the open window has an EMPTY visible prime-power index set
   (`globalPrimeIndexSet F = ∅`): every prime power `n >= 2` has
   `log n >= log 2`, outside the window on both sides.  This is the finite
   visible-prime set in its minimal form, stated as data, not as a sum
   vanishing.
3. `exists_pinnedHealthyDetector_rootWindow` (CONSUMER #2 EXIT) - for EVERY
   off-line source zero `rho` there is a `g : CompactLogTest` with
     - triple vanishing on `cc20TripleFiniteVanishingSet`,
     - detection `laplaceAt g rho = -1` (nonzero a fortiori),
     - explicit support radius: `support g.test ⊆ Icc(−log 2/2, log 2/2)`,
     - explicit finite visible primes: `globalPrimeIndexSet g.convolutionSquare = ∅`.
4. `selectedDetectorArchimedeanGate` + `healthyDetectorData_iff_...` (C2→C3
   HANDOFF) - on a pinned detector, the full `HealthyYoshidaDetectorData`
   package is EQUIVALENT to the single scalar inequality
   `0 < archimedeanTerm g.convolutionSquare`.  Consumer 3 owes exactly one
   inequality, with no other structural obligation.
5. `exists_healthyDetectorData_of_gate_of_pinnedHealthyDetector` - the C3
   entry point: gate + pinning yields `∃ g, HealthyYoshidaDetectorData rho g`.

## 3. Build evidence

WSL ext4 mirror build through the resource runner
(`build-logs/c2_pinning2.log`):

    Build completed successfully (3608 jobs).
    zero `^error:` lines on the module; zero `sorryAx` in the log.

Focused axiom audit (`C1HealthyDetectorPinningAudit.lean`) - all five
declarations depend on exactly the three standard axioms
`[propext, Classical.choice, Quot.sound]`:

    convolutionSquare_support_logTwo_of_rootSupport_logTwoHalf  OK
    globalPrimeIndexSet_eq_empty_of_support_subset_open_log_two OK
    exists_pinnedHealthyDetector_rootWindow                     OK
    healthyDetectorData_iff_selectedDetectorArchimedeanGate     OK
    exists_healthyDetectorData_of_gate_of_pinnedHealthyDetector OK

First build iteration caught two authoring defects (both semantic, fixed):
the empty-primes lemma was applied to `g` instead of `g.convolutionSquare`
(type mismatch caught by the kernel), and the gate definition carried an
unused `rho` binder (now `_rho`; the gate stays zero-parameterized by
interface).

## 4. Relation to the numerical chain (no numerics consumed)

Records 1077-1079 measured the C3 gate for the second source zero on an
explicit named family: `fl2 = −1.294` (sink 33.78% of lever), node residual
4.5e-18, empty visible primes, support in the same window.  No theorem here
consumes any of that; the gate remains an open Lean obligation - it is the
named frontier where a future directed-interval certificate (or an
algebraic sign theorem for a structured family) lands.  That is the
consumer-3 station, not consumer 2.

## 5. What is NOT here

`archimedeanTerm > 0` is NOT proven for any specific test; RH is NOT
claimed; no frozen namespace was touched; the capstone premises are
unchanged.  The coverage root remains RH-equivalent, not a density lemma.
