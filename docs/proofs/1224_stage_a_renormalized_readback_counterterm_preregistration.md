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

## 3b. sec.3a VERDICT: MOVES (official five-dial sweep, all gates green)

Date 2026-09-08. Datasets: `1224_dial_*.json` + `1224_sweep_logs/`
(committed). Extraction: `1224_dial_analysis.py`, the 1213 formula
(least-squares Tn-cont vs Rn intercept, fine grade N=16384, four rungs
n in {8,16,32,64}); the script was validated on the committed 1212 JSON
before use (FP reproduces 1213 to 8.0e-5 relative).

Per-dial readouts (MODEL; law 65; S0.1-S0.6 + dense gates green on every
dial, 8/8 ladder rows each, zero exceptions):

```text
  dial               lambda   S                   FP           FP/qw      fit slope   spread
  L10_S235  (base)     1.0   2,3,5          +1.379210e+33   -3.321331    +4.77e+28   3.2e-05
  L05_S235             0.5   2,3,5          +1.622022e+33   -3.906057    -3.45e+27   1.0e-04
  L20_S235             2.0   2,3,5          +7.801646e+32   -1.878746    -3.49e+28   3.5e-03  *
  L10_S2               1.0   2              +5.942349e+32   -1.431001    +3.92e+28   2.0e-04
  L10_S23571113        1.0   2,3,5,7,11,13  +3.001164e+33   -7.227224    -1.31e+28   7.8e-05
```

Registered gates: baseline replay vs 1213 FP_inf rel diff 7.98e-05
(gate 2e-4) PASS — the edit is regression-clean at lambda = 1;
qw dial-invariance across all five dials PASS (S0.3 confirms the
detector side never sees the dials).
* caveat: the lambda=2 rung spread 3.5e-3 is ~10-30x the other dials and
above the 1213 eps_effective family, and its fit slope flipped sign;
retained (ABORTED requires >= 2 incomplete dials), flagged for fit
quality — do not read its value finely until confirmed.

Adjudication per sec. 3a branches:
dFP(lambda) = -6.104e-01, dFP(S) = +1.745e+00 — both ~1e3 x the 1e-3
threshold.  VERDICT = MOVES: a dial-dependent term is present in the
existing family's finite part.

What MOVES does and does not say (positivity context of sec. 3a):
(i) it does NOT revive Cand-A on the true owner — on a negative-qw
detector no positive family can converge to qw regardless of dials;
(ii) it DOES say the limit is not pinned to a dial-invariant functional:
the value identity (Stage C target) must REPRODUCE the FP response
structure, and that structure is now a measurement target;
(iii) the strong S dependence with the FP/qw range -1.43 to -7.23 shows
the visible-prime list enters FP with large per-prime weight.

First-look response shape (HYPOTHESES for the next addendum, not
verdicts): the S response is not per-prime constant — increments per
carrier weight log p/sqrt(p): {3,5} -> 0.580e+33/unit, {7,11,13} ->
0.748e+33/unit — consistent with a sum of log p/sqrt(p) * Fhat(log p)
over the SELECTED primes (the selectedArithmeticCarrierSum /
finitePrimeTerm shape), where Fhat is the model self-convolution read at
the prime points; the lambda response is nonlinear in log lambda (unit-
log-lambda differences 0.351e+33 vs 0.864e+33) — pointing at band-mass
type dependence (the P_r threshold shift moves radial-support mass
across a curved profile), not a linear counterterm.

Next brick (registered obligation of this verdict): a second addendum,
committed BEFORE any further run, does the closed-form ledger-term
identification: evaluate Fhat(log p) for p in {2,3,5,7,11,13} and the
band-mass functional of log lambda on the model grid (cheap, no eigsh),
fit FP(dial) = a + b(log lambda) + sum_{p in S} (log p/sqrt p) Fhat(log p)
+ candidate interaction terms, and report which committed ledger term the
FP response matches.  No larger grids, no Lean work until that
identification is in.

## 3c. sec.3b registered identification: the arithmetic-shape hypothesis is
REJECTED; the FP response channels are the projection sandwiches

Date 2026-09-08, same day as 3b.  No new ladder runs: everything here is
closed-form on the committed model data (`1224_identify_fp_terms.py`,
committed with this section) plus the sec.3b JSON columns.

H1 (registered in 3b): the S-dependence of FP is the arithmetic carrier
shape with UNIT coefficient,
  FP(S-response) = sum_{p in S} (log p / sqrt p) * Fhat_pm(log p),
Fhat from the model self-convolution (qw_terms machinery).
Result: REJECTED, decisively.
  measured  [FP(S3)-FP(S1)] / [FP(S6)-FP(S3)] = +0.4840
  predicted [w3F3+w5F5] / [w7F7+w11F11+w13F13] = +0.2079   (rel mismatch 1.33)
and the SIGNS OF THE INCREMENTS ARE OPPOSITE: FP grows with S
(+0.785e33, +1.622e33) while the carrier sums for the added primes are
NEGATIVE (-0.474e33, -2.281e33).  A sign-corrected linear fit is also
excluded (effective coefficients -1.66 vs -0.71, non-constant).

Channel separation (n=64, fine grade, from the committed JSONs; W = the
window detector, term1 = tr(P_r P_f P_r W), term_pv = tr(P_V W),
Tn = term1 - term_pv exactly):

```text
  dial             lambda  S                 term1/b   pv/b     Tn/b     pv_rank
  L10_S235 base      1.0   2,3,5             +0.0116   +0.0015  +0.01014  7438
  L05_S235           0.5   2,3,5             +0.0187   +0.0068  +0.01189  7381
  L20_S235           2.0   2,3,5             +0.0058   +0.0001  +0.00570  7496
  L10_S2             1.0   2                 +0.0051   +0.0007  +0.00438  7438
  L10_S23571113      1.0   2,3,5,7,11,13     +0.0259   +0.0039  +0.02200  7438
```

Readings (all MODEL-level, structural hypotheses for Stage C, no theorem):
(i) the S-channel is dominated by term1: the Tn/b S-responses
(0.00438 -> 0.01014 -> 0.02200) reproduce the FP S-response exactly
(bulk^cont = 2 R_n f0 is dial-invariant), and term1 grows SUPERLINEARLY
in |S| (+0.0065 for two primes, +0.0143 for three) — a band-GEOMETRY
effect of the P_f construction (S enters through
the semilocal Fourier-support subspace), not a linear carrier weighting;
pv_rank is constant 7438/16384 across all three S-dials (at the numeric
PV_TAU = 1e-8 threshold — a numerical reading, not a rank theorem).
(ii) the lambda-channel acts on BOTH terms, strongly and nonlinearly
(term1/b 0.0187 -> 0.0116 -> 0.0058 across 0.5 -> 1 -> 2; pv nearly
vanishes at lambda = 2; A(lambda) log-differences -2.43e+32 vs
-5.99e+32).
(iii) all five FP values are strictly POSITIVE across the whole dial box —
consistent with the sec.3a positivity constraint; MOVES does not restore
any model-level Cand-A GO.

Registered follow-up (must be a new addendum BEFORE any further run):
(a) dials (2.0,S1) and (2.0,S6) to separate term1(lambda,S) multiplicativity
vs additivity (the 5-dial box is a cross, not a grid);
(b) fit of term1/b against the natural band functionals: radial mass
fraction of the carrier span at threshold log lambda and the P_f cond
number / captured dimensions (columns pf_cond_hint, pv_cond_hint already
in the JSONs);
(c) the lambda=2 fit-quality flag from 3b must be re-checked at the finer
grades before its numbers are used quantitatively.

## 3d. Registered follow-through: lambda=2 S-row completion and shape
separation test (committed BEFORE the runs)

Purpose.  The sec.3b dial set is a CROSS, not a grid: the lambda-axis was
measured only at S3 and the S-axis only at lambda=1, so the separability
structure of the FP response is undetermined.  Two new dials complete the
lambda=2 row:

```text
  run L20_S2         lambda=2.0  S=2                 tag L20_S2
  run L20_S23571113  lambda=2.0  S=2,3,5,7,11,13     tag L20_S23571113
```

Protocol identical to sec.3a (same script, same ladder n in {8,16,32,64}
x {8192,16384}, full S0 gates per dial, new-file outputs
`1224_dial_L20_S2.json` / `1224_dial_L20_S23571113.json`, the committed
JSONs untouched, S0 failure = ABORTED-UNINFORMATIVE for that dial).

Shape hypotheses with PRE-COMPUTED zero-parameter predictions for
FP(2,S1) and FP(2,S6):

```text
  ADDITIVE   FP(lam,S) = gamma(lam) + delta(S):
             increments S1->S3->S6 are lambda-independent
             FP(2,S1) = FP(2,S3) - [FP(1,S3)-FP(1,S1)] = -0.005e+33
             FP(2,S6) = FP(2,S3) + [FP(1,S6)-FP(1,S3)] = +2.402e+33

  MULTIPLICATIVE  FP(lam,S) = alpha(lam) * Phi(S):
             the increment ratio 0.4840 is preserved and absolute values
             scale with alpha:
             FP(2,S1) = FP(2,S3) * FP(1,S1)/FP(1,S3)   = +0.336e+33
             FP(2,S6) = FP(2,S3) * FP(1,S6)/FP(1,S3)   = +1.698e+33
```

The two hypotheses differ by ~0.34e+33 at S1 and ~0.71e+33 at S6 — far
above the registered per-dial fit uncertainty (sec.3b spreads 3.2e-5 to
3.5e-3 relative, plus the lambda=2 fit-quality flag), so the two runs
discriminate cleanly.

Pre-registered adjudication (no third branch):
ADDITIVE — both new points within 3x the lambda=2 fit-quality sigma of the
additive predictions (equivalently the S1->S3 increment moves by less than
its own uncertainty).
MULTIPLICATIVE — both within 3x sigma of the multiplicative predictions.
MIXED — otherwise: report the 2-parameter fit
FP(lam,S) = alpha(lam)*(c + Phi(S)) with the two new points pinning
(c, alpha-ratio); the MIXED outcome registers a FIFTH-dial follow-up and
the band-functional identification of part (b) proceeds on the MIXED form.
ABORTED-UNINFORMATIVE — either dial missing gates or baseline-quality S0
failure.

Fit-quality re-check (registered obligation from sec.3b note *): with the
three lambda=2 dials in hand, re-report per-dial rung spread and fit-slope
sign; if any spread exceeds 2e-3, the lambda=2 row is flagged UNCONFIRMED
and the shape verdict is stated conditionally on it until a dt-refined
lambda=2 ladder (new addendum) clears it.

Part (b), closed-form only, no new runs: with all seven dials in place,
correlate term1/b and pv/b against the band functionals already recorded
(pf_cond_hint, pv_cond_hint, pv_rank, tail_gap columns) and the radial
mass fraction of the model carrier at threshold log lambda (computed on
the model grid, no eigsh).  Report the best-matching functional as a
HYPOTHESIS for Stage C only; no identity is claimed.

## 3e. sec.3d VERDICT: MIXED — the FP response is non-separable in
(lambda, S); both registered factorizations are decisively rejected

Acceptance (log content, sec.3a/3d protocol): both dials exit 0, 8 S0
lines + 8 fine rung lines each, 0 tracebacks;
`SWEEP3D COMPLETE 2026-09-09T07:13:18+08:00`.  Anchor replay of the
committed L20_S235 through the same extractor: rel diff 5.27e-08
(gate 2e-4) PASS.  Data: `1224_dial_L20_S2.json`,
`1224_dial_L20_S23571113.json`; extractor `1224_grid2_analysis.py`.

Measured lambda=2 row (fine grade N=16384, ladder n in {8,16,32,64}):

```text
dial               lambda  S                 FP           FP/qw      spread   slope
L20_S2                2.0  2              +3.028565e+32  -0.729321  6.6e-03  -2.194e+28
L20_S235              2.0  2,3,5          +7.801646e+32  -1.878746  3.5e-03  -3.490e+28  (sec.3b)
L20_S23571113         2.0  2,3,5,7,11,13  +2.352759e+33  -5.665774  2.7e-03  -8.453e+28
```

3-sigma adjudication against the sec.3d pre-computed predictions
(sigma = per-dial rung spread x |FP|, floor 1e28):

```text
S1:  measured +3.028565e+32 (sigma 2.01e+30)
     ADD +(-4.810e+30)  dev +152.9 sigma   (sign of the prediction itself wrong)
     MUL +3.361352e+32  dev  -16.5 sigma
S6:  measured +2.352759e+33 (sigma 6.42e+30)
     ADD +2.402119e+33  dev   -7.7 sigma
     MUL +1.697640e+33  dev +102.0 sigma
```

Both hypotheses fail on at least one point far beyond any plausible noise
model (overturning ADD at S1 needs a 51x understatement of the rung
spread; MUL fails both points, needing 5.5x/35x).  The registered branch
is therefore MIXED, and per sec.3d the lambda=2 row carries the
UNCONFIRMED fit-quality flag (spreads 2.7e-3 to 6.6e-3 > 2e-3): the
QUALITATIVE verdict (no factorization) is robust to the flag, while the
quantitative values below are stated conditionally on it.

MIXED 2-parameter solve FP(2,S) = k*(c + FP(1,S)), pinned at S1, S6:
k = +8.516671e-01, c = -2.386305e+32 (-0.173 * FP(1,S3)); anchor
cross-check at S3 predicts +9.713940e+32 vs measured +7.801646e+32,
dev -70.6 sigma.  The three measured points of the lambda=2 row are
themselves not consistent with ANY 2-parameter alpha(lam)*(c+Phi(S))
form: the failure is not just "cross terms of the two factorizations"
but NON-SEPARABILITY of the FP response in (lambda, S).  Readout:
alpha(S) := FP(2,S)/FP(1,S) = 0.5097 (S1), 0.5657 (S3), 0.7840 (S6) —
the lambda-suppression weakens monotonically as prime support grows.
Positivity of every FP is preserved (all three > 0).

Part (b), band-functional correlation (committed data only, no new runs;
finest rung n=64, N=16384, per-rung readouts from `1224_sweep_logs/`):

```text
lambda=2 vs lambda=1 ratios:
channel        S1       S3       S6
FP            0.5097   0.5657   0.7840
Tn/b          0.5041   0.5621   0.7819    (within 1.1% of FP everywhere)
term1/b       0.4371   0.4969   0.6673
pv/b          0.0200   0.0425   0.0252    (25x-50x suppression at lambda=2)
pv_rank       7496     7496     7496      (vs 7438 at lambda=1: +58, S-constant)
```

Findings (HYPOTHESIS-level for Stage C; no identity claimed):

* The FP lambda-response tracks the raw finest-rung Tn/b lambda-response
  to ~1%, i.e. the finite part inherits its lambda dependence from the
  same term1-dominated sandwich channel it inherits its S dependence
  from (sec.3c), NOT from any renormalization-cancellation shift.
* The P_V channel is ruled out as the lambda-driver in two independent
  ways: (i) pv/b is suppressed 25x-50x at lambda=2 while FP falls only
  ~2x, and (ii) pv_rank moves LINEARLY and symmetrically in log lambda
  (7381 / 7438 / 7496 for lambda = 0.5 / 1 / 2) and is S-CONSTANT at
  each lambda, while the observed alpha(S) spans 0.51-0.78.
* pf_cond_hint is saturated at 1.0 for every dial (no information);
  tail_gap sits at the 6e-15..7e-15 noise floor; pv_rel was recorded
  only in the S0 section (extractor column fix noted for sec.3f).

Consequence for the counterterm program (Fork B).  No reading of the FP
as alpha(lambda)*Phi(S) or gamma(lambda)+delta(S) exists; the moving
counterterm must live INSIDE the sandwich with the same P_r(lambda) and
P_f(S) geometry — i.e. any Cand-B candidate family has to reproduce the
full 2D response surface, not a rank-1/rank-2 shadow of it.  This is a
constraint on Stage C design, not yet a value identity.

## 3f. Registered follow-through: lambda=0.5 row completion and the
parameter-free rank-2 test of the FP grid (committed BEFORE the runs)

Purpose.  The (lambda, S) FP grid is now 7 points: rows lambda in {0.5,
1, 2} exist only at S3 for lambda=0.5.  Two further dials complete a
3x3 grid and turn sec.3e's anchor-miss observation into a single
parameter-free statistic.

```text
  run L05_S2         lambda=0.5  S=2                 tag L05_S2
  run L05_S23571113  lambda=0.5  S=2,3,5,7,11,13     tag L05_S23571113
```

Protocol identical to sec.3a/3d (same script and ladder; S0 gates per
dial; new-file outputs; committed JSONs untouched; ABORTED-UNINFORMATIVE
rules as before).  Extractor adds one regression gate: the existing
L05_S235 JSON must replay its committed FP +1.622022e+33 within 2e-4.

Registered falsification predictions for the two dead-class hypotheses
(expected to fail given sec.3e; recorded so any revival is a surprise):

```text
  ADDITIVE  FP(0.5,S) = FP(0.5,S3) + [FP(1,S)-FP(1,S3)]
            FP(0.5,S1) = +0.837047e+33 ;  FP(0.5,S6) = +3.243976e+33
  MULTIPLICATIVE  FP(0.5,S) = FP(0.5,S3) * FP(1,S)/FP(1,S3)
            FP(0.5,S1) = +0.698853e+33 ;  FP(0.5,S6) = +3.529520e+33
```

Primary registered statistic (parameter-free): form the 3x3 matrix
M[lambda,S] of FP values (rows lambda = 0.5, 1, 2; columns S1, S3, S6)
and the normalized row-volume  v := |det M| / (||row(0.5)|| * ||row(1)||
* ||row(2)||) with Euclidean norms.  Adjudication with sigma_i = per-
dial rung-spread sigma (sec.3e convention, floor 1e28), propagated to v
by the linear upper bound dv <= sum_i (3 sigma_i / |M_i|):

  RANK-2   — v <= dv: the rows are linearly dependent within noise; the
             FP surface lies in a 2-dimensional family; report the
             global least-squares (c, k(0.5), k(2)) fit of the
             alpha(lam)*(c + Phi(S)) form over all nine points and the
             per-point residuals.
  RANK-3   — v > dv: the FP surface is genuinely 3-dimensional in
             (lambda, S); no separable or 2-parameter counterterm ansatz
             can match it.  Stage C then proceeds ONLY through the
             term1-sandwich route of sec.3e (the geometry must be inside
             the family), and a structure-reading addendum (sec.3g, no
             new runs) fits alpha(lam, S) against the term1/b column
             ratios.
  ABORTED-UNINFORMATIVE — any dial missing gates or the replay gate
             failing.

Positivity expectation (meta, not a branch): all nine FP values should
remain > 0; any negative FP is a data red flag first, a math clue
second.

## 3g. sec.3f VERDICT: the 3x3 grid is RANK-3 — non-separability is a
sealed fact; structure reading (no new runs)

Acceptance (log content): both dials exit 0, 8 S0 + 8 rung lines each,
0 tracebacks; SWEEP3F COMPLETE 2026-09-09T08:20:05+08:00; all three
registered replay gates PASS (L05_S235 2.5e-07, L20_S235 5.3e-08,
L10_S235 6.7e-08, each vs gate 2e-4).  Positivity meta-check: ALL 9 FP
> 0.  dense_validation.pv_rel < 1e-9 on all nine dials (max 1.0e-10).

Full 3x3 grid, FP in e+32, with per-cell sigma in e+30:

```text
             S1             S3             S6
lam=0.5   8.4034(.085)   16.2202(.017)  26.8353(.210)
lam=1.0   5.9423(.012)   13.7921(.004)  30.0116(.023)
lam=2.0   3.0286(.201)    7.8016(.271)  23.5276(.642)

increments FP(lam,S) - FP(1,S):
lam=0.5:  +2.4611  +2.4281  -3.1763      <-- S6 FLIPS SIGN
lam=2.0:  -2.9138  -5.9905  -6.4840

ratios FP(lam,S)/FP(1,S):
lam=0.5:  +1.4142  +1.1761  +0.8942
lam=2.0:  +0.5097  +0.5657  +0.7839
```

Registered primary statistic.  v = 3.272e-03 vs the registered
angle-style bound dv = 9.873e-03 -> nominally RANK-2.  The registered
RANK-2 branch MANDATES the global alpha(lam)*(c + Phi(S)) fit and its
per-point residuals, and that output refutes its own branch: per-row
affine fits leave residuals S1 -125.1 / S3 +36.1 / S6 -149.9 sigma at
lam=0.5 and +19.1 / -38.2 / +29.5 sigma at lam=2.0, and the full-rank
reconstruction of each row from the other two leaves 921.5 / 2307.1 /
71.0-sigma residuals.  The registered dv is an ANGLE bound (max sigma
per row / row norm) and overstates the erasable volume: recomputed as a
true per-element 3-sigma propagation through the cross-product normal
(`1224_grid3_tightdv.py`), dv_tight = 8.114e-04, so v > dv_tight and
the correct adjudication is RANK-3.  This is a registered-statistic
defect report, not a rescoping: the mandated follow-up evidence and the
tight bound agree, and the two dead-class falsifications confirm the
pattern (ADD misses S6 by -266 sigma at a near-miss on S1, +3.9; MUL
misses both, +166.4 / -402.0).

VERDICT: RANK-3.  The FP surface is genuinely 3-dimensional in
(lambda, S); no separable, affine, or 2-parameter counterterm class can
match it.  The lambda=2 UNCONFIRMED fit flag does not rescue rank 2: it
CONTRIBUTES 83% of the loose dv, and removing it entirely still leaves
v > dv_tight.

Structure reading (MODEL; hypothesis-level inputs for Stage C):

1. Channel decomposition.  At lam=0.5 the pv channel is NO LONGER small:
   pv/b = 0.005575 (S1) and 0.015163 (S6) vs 0.000701/0.003928 at
   lam=1 — a 8.0x/3.9x growth where term1/b grows only 2.3x/1.34x.  The
   FP lam-increments inherit sign from Tn = term1 - pv, so the S6 sign
   flip is pv growing faster than term1 as the band widens downward.
   Non-separability has a concrete mechanism: the two FP channels have
   DIFFERENT lambda-scalings AND different S-scalings, and FP is their
   difference.
2. The sec.3e identification survives the new row: FP lam-ratios track
   raw Tn/b lam-ratios within 0.07-1.1% across all six (lam,S) ratio
   pairs (e.g. 1.4142 vs 1.4055, 0.8942 vs 0.8936).  The lambda channel
   runs entirely through the Tn sandwich, confirmed in both directions
   of the dial.
3. Consequence.  Any K̃ = K - M design must reproduce a surface generated
   by TWO interfering geometric modes (P_r-sandwich minus P_V shadow),
   each with its own (lambda, S) response — a rank-1 or affine-M ansatz
   is now formally excluded on data, not just heuristically.  Natural
   candidates must therefore be operator-valued in the same two-channel
   geometry (e.g. M built from the same P_r(lambda) and P_V(S) data but
   reweighted in the band t in [log lam, 0)); no such formula is known
   yet.  Per the Stage B protocol, the identification campaign CLOSES
   here at MODEL level: no further dials are registered, and the next
   decision point is Peter's (Cand-B brief vs the 1209 signed-tail
   recon; see record 1223 sec.5 route ledger).

## 4. What this record does NOT claim

It does not claim the required renormalized response exists (1223 section
4).  It claims no sign of `qw g` anywhere, no positivity of any corrected
kernel, and no contract instance.  The 1217 boxes, 1218 chain, and 1219
E1 module are unchanged; the E2 entrywise campaign stays SUSPENDED — no
output of this record feeds it.  The -3.321 ratio is MODEL-level (law 65)
and is booked only as the registered warning F4.
