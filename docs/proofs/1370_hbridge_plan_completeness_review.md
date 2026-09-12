# 1370 - HBridge plan completeness review and conditional completion contract

Date: 2026-09-12. Class: source-level and paper-only design review.
Owner instruction: repair map 008 so that proving every required mathematical
task implies unconditional RH. No proof of feasibility is requested or claimed.
No Lean source changed; no build or numerical experiment was run for this record.

## 1. Evidence and corrections

| Finding | Evidence and scope | Plan correction |
|---|---|---|
| The A2 exit requires two inputs | FORMAL SOURCE READBACK: `sourceRH_of_A2Bridge` in [C1H2Corridor](../../ConnesWeilRH/Dev/C1H2Corridor.lean) takes `hBridge` and `hA2` | Separate actual geometry and count/exclusion producers from the analytic bridge; neither input is proved by the conditional theorem |
| A is not interpreted geometry | FORMAL SOURCE READBACK: [C1TargetA2](../../ConnesWeilRH/Dev/C1TargetA2.lean), `targetA2Schema`; `sourceRH_targetA2_margin_reduction` explicitly assumes RH | Require a concrete spread definition and a theorem relating it to actual source zeros; the RH-side control cannot produce hA2 |
| Full-space finite sampling has a kernel | PAPER ARGUMENT, detailed in 008 S0a: finitely many linear constraints on compact smooth tests in a fixed interval leave an infinite-dimensional kernel | Reject positive full-space coercivity in that literal shape; require a restricted space plus complement/cross estimates or a different precise inequality. Not a Lean-certified no-go or a rejection of all B5 mechanisms |
| The old controls use the wrong extremum and owner | SOURCE READBACK of MODEL evidence: [1353 section 4](1353_c6_placement_audit_and_nlle_spec_repair.md) defines lambda_1 by a maximum of continuous interval concentration | Withdraw those readings as positive/negative controls for a discrete minimum sampling bound; no new digits or numerical verdict |
| Complex quartet shorthand is too strong | FORMAL SOURCE READBACK: [C1N1SamplingContest](../../ConnesWeilRH/Dev/C1N1SamplingContest.lean), `quadOrbit_re_sum`, uses two Hermitian pairs; its header records the real-g specialization | D5 must retain both pairs, exact conjugations and multiplicity; factor 4 needs a proved additional symmetry |
| Counts and mass have different weights and regions | FORMAL SOURCE READBACK: A2 uses `Set.encard`, while [C1SpectralWeil](../../ConnesWeilRH/Dev/C1SpectralWeil.lean) uses `xiMultiplicity`; [C1A2WindowSplit](../../ConnesWeilRH/Dev/C1A2WindowSplit.lean) sums all off-line terms | Require weighted conversion, low/negative heights, far-off-line mass, endpoints and variable-width compatibility |
| A=0 does not admit the strict nonvoid schema | PAPER DEFINITIONAL READBACK: `fstar_zero` and the nonnegative ENNReal left side make the required strict inequality impossible | Remove the earlier 'A=0 forces zero off-line zeros' wording for this schema |
| Per-window balance is RH-strength | LOGICAL COMPOSITION of existing `sourceRH_of_windowMassBalanceBridge` and `sourceRH_windowMassBalance` | No claim that a single named interface is an easier theorem; preserve the selected-detector B5 consumer |

The revised task ledger and phase plan are in
[008](../map/008_l2_hbridge_bone_attack_plan.md). D0-D9 are planned
obligations, not newly formalized declarations. The explicit assembly is:
prove a same-detector gain/loss/error inequality covering all integer windows,
prove the budget closes, obtain `windowMassBalance`, apply the committed
same-owner `qw` assembly, and close against detector negativity. Actual
geometry and exclusion inputs and every complement estimate remain OPEN.

## 2. Status and provenance boundaries

CB-HB1 returns to NEEDS-ANALYSIS at a paper-only Stage-0 gate. Its old numerical
P0, controls, success prior and time estimates do not govern new work. No
blanket mathematical death is entered: the finite-rank argument matches only
the literal full-space lower bound, and historical MODEL configurations do
not by themselves refute a theorem about actual zeta zeros.

Record 1370 was an unexecuted future numerical-preregistration reservation in
008; this revision uses it for the review instead. Any later useful numerical
task needs a fresh available number and its own preregistration. This record
contains no experimental results.

The route authority of 003, the endpoint scope of 004, and the quantifier
guards of 007 are unchanged. The global project status remains RH unproved,
C3 open, no same-detector positivity producer. Accordingly the root README
status, AGENTS route ruling and RH_MAINLINE_FREEZE remain unchanged; this is
an internal candidate-plan correction, synchronized in the map index and 006
registry, not a new route or an RH-status promotion. The root README's layout
and math panels are outside this requested repair.

## 3. Acceptance of this documentation change

Read back the exact source theorem signatures and check the revised D0-D9
dependency chain, relative links, stale candidate-card references and
`git diff --check`. No Lean acceptance is claimed for this documentation
review. Final unconditional RH acceptance is separately specified in 008
section 7 and requires all analytic producers plus the final hypothesis-free
Mathlib theorem and its complete three-standard-axiom audit.
