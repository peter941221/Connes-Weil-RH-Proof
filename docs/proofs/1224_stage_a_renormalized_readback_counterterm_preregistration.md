# Record 1224 — Stage A: counterterm specification for the projection-cutoff B5 producer

Date: 2026-09-08.
Status: PRE-REGISTRATION, committed BEFORE any new numerical run or Lean
build in this campaign (law 42).  This is the Stage A brick of record 1223
section 3/4.  RH is not claimed; no positivity, convergence, or
value-match is asserted anywhere below.

Consumer named (verbatim target):
`sourceRH_of_healthyDetector_p2ProjectionCutoffLimitContracts`
(`ConnesWeilRH/Dev/C1P2BilateralProfileExit.lean:711`).  Per hypothetical
right-half off-line zero it must be fed
`Nonempty (ProjectionCutoffLimitContracts g lambda S globalBasis)`
(`ConnesWeilRH/Dev/C1Stage3ProjectionOperatorFamily.lean:182-196`) for the
same healthy `CompactLog` detector.

## 1. Structural facts from the read-only ledger audit

All facts below are re-read from committed Lean and committed verdict
records; nothing here is new numerics.

F1 — the contract has NO external counterterm slot.  Its two fields are
`remainder_tendsto_zero` and
`readback_tendsto_qw : Re Tr(P_n) - remainder n -> qw g`, so the contract
is literally `Re Tr(P_n) -> qw(g)` (a CONVERGENT trace).  The B5 engine is
limit-of-nonnegatives: `positive : forall n, (traceOperator n).IsPositive`
gives `0 <= Re Tr(P_n) - remainder n` and
`le_of_tendsto_of_tendsto'` transfers it to `0 <= qw g`
(`ConnesWeilRH/Dev/C1PositiveTraceLimitBridge.lean:213-222`).  Consequence
(amending record 1223 section 3.1): a trace-level readback
`Re Tr(P_n) - B_n - Re Tr(R_n) -> qw` with a divergent external `B_n` is
FORMALLY DEAD as a contract shape (Fork A): the subtraction destroys the
positivity transfer.  Any counterterm must be realized at OPERATOR level
inside a family that stays positive at every cutoff (Fork B).  Record 1223
section 2's "moving finite-part / renormalized response" is therefore read
operatorially throughout this record.

F2 — the bulk term is identified, not postulated.  The committed
telescoping decomposition (`C1Stage3ProjectionContractObstruction.lean:93-103`)
is
`Re Tr(P_n) = Re Tr(R) + Re Tr(D1_n) + Re Tr(D2_n)` with the FIXED
whole-line response `R = projectionResponse owner lambda S`
(`C1Stage3ProjectionTraceLedger.lean:94-97`),
`D2_n = windowedBoundaryDetector g (lo_n) (hi_n) - R`
(`C1Stage3ProjectionResponseBridge.lean:196-201`), and
`D1_n = P_n - windowedBoundaryDetector_n` (`cutoffKernelInsertionSandwich`,
norm-bound `<= ‖C_n‖^2 * ‖kernelInsertionDefect‖`,
`C1Stage3ProjectionDefectBounds.lean:313-319`).  Re-grouping:
`Re Tr(P_n) = Re Tr(windowedBoundaryDetector_n) + Re Tr(D1_n)`.  The bulk
is exactly `Re Tr(windowedBoundaryDetector_n)`, `windowedBoundaryDetector g a c
= (fullBoundaryRootFactor g a c)† ∘L fullBoundaryRootFactor g a c`
(`Source/CC20Concrete/CompactRootHalfLinePair.lean:1353-1356`); its trace
is monotone and cofinally unbounded in the cutoff for `g.test ≠ 0`, with
mass `∫ normSq (g.test)` (`Dev/C1PositiveTraceCutoffGrowth.lean:403-415`);
record 1210 measured the slope `tr ~ 2 R_n * f0` with `R_n = supportRadius g +
n + 1`.

F3 — the 1211 no-go already carries the moving-response hypothesis.
`cutoffWindowToMovingResponseDefect_trace_re_cofinal_unbounded_of_sourceTest
_ne_zero` (`C1Stage3ProjectionDefectBounds.lean:616-627`) is stated for an
ARBITRARY family `response : Nat -> carrier ->L[ℂ] carrier` whose real
trace is merely bounded ABOVE.  Therefore any viable candidate must have
`Re Tr(R_n)` UNBOUNDED above, tracking the F2 bulk coefficient exactly;
"bounded response / zero counterterm / bulk-coefficient mismatch =
immediate no-go" (record 1223 section 3.2) is formalizable verbatim as
this theorem plus the F2 identity.

F4 — model evidence separates convergence from value.  Record 1213 (the
1116-k=1 MODEL twin, law 65): the sandwiched trace `T_n^cont` is
window-INDEPENDENT to ~2e-4 relative over n = 8..64 (the projection kernel
absorbs the linear bulk inside `D1_n`; residual slope 1.6e-5..1.9e-5 of
the constant part), so NO divergent counterterm arises and cannot be
"retained" — exit A's scalar form is closed (1213 Q1, verdict H2).  The
finite part settled at `FP_inf / qw = -3.321` (opposite sign, 3.32x
magnitude; 38x outside the H1 band): the failure mode is the VALUE of the
limit, not its existence (1213 Q2).  A candidate must therefore be
adjudicated by a finite-part VALUE check, and the -3.321 ratio is the
registered warning that the existing family's limit need not read back to
`qw g`.

## 2. Registered candidates (operator-level, Fork B shape)

Both candidates are families `Q_n` of bounded operators on
`projectionCarrier = cc20GlobalLogCrossingL2` intended to satisfy, on one
healthy-`CompactLog` owner:

  (pos)   `Q_n = B_n^† ∘L B_n`-form witness, i.e. `0 <= Q_n` per n, and
           `IsTraceClassAlong globalBasis Q_n` per n;
  (read)  `Re Tr(Q_n) -> C1SameOwnerWeil.qw g` — realized as the contract
          with `remainder n := Re Tr(Q_n) - qw g` and the requirement
          `remainder -> 0`;
  (owner) all identities on the SAME detector `g`, scale `lambda`, visible
          list `S` consumed by the F1-spine consumer; `S` and `lambda`
          remain the universal parameters of the consumer theorem and are
          NOT tuned per n.

Cand-A (existing family, value test).  `Q_n := cutoffProjectionOperator
g lambda S globalBasis n` unchanged; the only obligation is (read).  By
F2 this is `Re Tr(detector_n) + Re Tr(D1_n) -> qw g`, i.e. the absorption
observed in 1213 Q1 promoted to the real owner, PLUS a finite-part value
identity against the Gate-2 response ledger
`Re Tr(R) = sum of finitePrimeTerm + Re Tr(sameObjectResidual)`
(`C1Stage3ProjectionTraceLedger.lean:119-135`, the committed
`stage3TraceLedger_projectionResponse_eq_finitePrimeSum_add_residual`).
No new contract field, no module-boundary change.

Cand-B (window-matched moving response).  When Cand-A fails the value
check, the registered correction shape is
`Q_n := C_n^† ∘L (stage3ProjectionKernel lambda S + M_n) ∘L C_n` with the
counterterm carried by an n-dependent self-adjoint correction `M_n` whose
sandwiched trace satisfies the EXACT finite-part identity
`Re Tr(C_n^† M_n C_n) = qw g - FP_g + o(1)`, where `FP_g` is the Cand-A
limit if it exists.  Admission (section 3) requires `M_n` to be built from
the existing cutoff ledger terms (the `kernelInsertionDefect` /
`sameObjectResidual` owners) — a free-floating `M_n` is not a candidate —
and requires (pos) to be re-proved for the corrected kernel.  If Cand-B
survives to Stage C it needs a NEW Lean operator family (and possibly a
contract variant taking the n-dependence internally): that is a
mainline-spine module-boundary change and is explicitly gated on Peter's
approval of this record BEFORE any such Lean work.

## 3. Admission falsifier protocol (Stage B; run before any large grid)

V1 (bounded-response kill, formal).  Instantiate F3 on the candidate: if
`Re Tr(R_n)` [response read into the defect] is bounded above, the defect
trace is cofinally unbounded above, and with `D1_n -> 0` the contract is
impossible by the committed
`not_projectionCutoffLimitContracts_of_fixedResponse_and_traceDefect_vanishing`
(`C1Stage3ProjectionContractObstruction.lean:38-51`).  Kill, report.

V2 (bulk-coefficient match).  Compute/prove on the selected owner that the
candidate's leading cutoff growth equals `Re Tr(windowedBoundaryDetector_n)`
F2-coefficient (mass `∫ normSq (g.test)`, slope `2 R_n` per 1210) — as an
IDENTITY, not an inequality.  Mismatch kills the candidate.

V3 (finite-part value test).  Decide whether the renormalized limit of
`Re Tr(Q_n)` equals `qw g` via the Gate-2 ledger bridge (the finite-prime
sum plus the residual, same owner).  Model expectation from F4: expect
FAIL for Cand-A unless the same-owner bridge identifies
`FP = qw g`; a confirmed mismatch kills Cand-A and instantiates Cand-B's
`M_n` target.  Any small-grid check here is exactly of the 1212 ladder
class (n ∈ {8,16,32,64}, model twin labeled MODEL, law 65); NO large
exact-Fraction grid is justified by this record, and none may be launched
under it.

Verdict branches (pre-registered, no third branch, law 42):
GO-A (V2+V3 pass on Cand-A) -> the contract holds for the EXISTING
family; Stage C is a Lean composition record only.
GO-B (V3 fails with a computed FP; Cand-B's M_n survives V1-V2) ->
propose the operator-family amendment; STOP for Peter's boundary gate.
NO-GO (V1 or V2 fires for both candidates) -> record and return to the
1223 section 2 fork; no numerics escalation.
ABORTED-UNINFORMATIVE -> 1097 protocol, no verdict either way.

## 3a. Registered Stage B instantiation: model-level dial-sensitivity sweep
(added BEFORE implementation and before any run; law 42)

Context facts (all committed): (i) for any positive family, every finite
trace is >= 0, so a convergent limit is >= 0; (ii) under the off-line-zero
hypothesis the consumed healthy detectors have formal `qw g < 0`.  Hence no
dial choice can make a positive-family contract converge to `qw g` on a
negative-qw detector, and a model-level GO is structurally impossible.  The
ONLY registered purpose of this sweep is a MECHANISM probe: whether and how
the existing family's finite part FP(lambda, S) depends on the Sonin scale
and the visible-prime list — this tells the Stage C value identity which
dial-dependent ledger terms it must contain.  Detector g is
dial-independent by construction (1116 twin: rho/gammas/NEXP only), so
FP/qw sensitivity is entirely the kernel's.

Dials: lambda in {0.5, 1.0, 2.0} x S in {{2}, {2,3,5}, {2,3,5,7,11,13}};
grid = {(0.5,{2,3,5}), (1.0,{2,3,5}), (2.0,{2,3,5}), (1.0,{2}),
(1.0,{2,3,5,7,11,13})}; the (1.0,{2,3,5}) entry is a baseline REPLAY and
must reproduce record 1213's headline `sn_dt(n=64,fine) =
-1.11622981e+37`-class values within the ~2e-4 registered stability
(a regression gate on the edit itself).

Implementation (minimal diff to the committed 1212 script):
(a) `PROBE_LAMBDA` / `PROBE_S` env reads with 1213-registered defaults;
(b) `P_r` threshold `t >= 0.0` becomes `t >= log lambda` in the grid's
`pos` mask (single site; the S0.6 range gate follows it);
(c) assertion that `qw_terms(g)` is bit-identical across all five dials;
(d) ladder n in {8,16,32,64}, both grades (1212 settings unchanged);
(e) every dial passes the full S0 gate set (S0.1-S0.6 + dense validation)
before any ladder rung; an S0 failure on a dial is
ABORTED-UNINFORMATIVE-for-that-dial (1097 protocol), not a candidate
verdict;
(f) output goes to NEW files `1224_dial_<lambda>_<S>.json` only; the
committed official `1212_probe_results.json` is never written.

Readouts: FP_dial = sn_dt at n=64 fine (the 1213 normalization);
relative responses dFP(lambda) = (FP(2) - FP(0.5))/|FP(1)| and
dFP(S) = (FP(S6) - FP(S1))/|FP(S3)|.

Adjudication (pre-registered, no third branch):
PINNED — all |dFP| < 1e-3: the existing family's limit is dial-invariant;
the Cand-A value identity does not run through (lambda, S); the next probe
must target the n-lever inside the Cand-B `M_n` shape (new prereg).
MOVES — any |dFP| >= 1e-3: a dial-dependent term exists; a SECOND addendum
(committed before any further run) does the algebraic identification of
which ledger term matches the FP response shape.
ABORTED-UNINFORMATIVE — baseline replay fails its regression gate or >= 2
dials fail S0.

Budget: 5 dials x ~20-25 min WSL2, MODEL-labeled (law 65), certifies
nothing about the true owner, feeds only the 1224 Stage B adjudication.
No large exact-Fraction grid anywhere in this sweep.

## 4. What this record does NOT claim

It does not claim the required renormalized response exists (1223 section
4).  It claims no sign of `qw g` anywhere, no positivity of any corrected
kernel, and no contract instance.  The 1217 boxes, 1218 chain, and 1219
E1 module are unchanged; the E2 entrywise campaign stays SUSPENDED — no
output of this record feeds it.  The -3.321 ratio is MODEL-level (law 65)
and is booked only as the registered warning F4.
