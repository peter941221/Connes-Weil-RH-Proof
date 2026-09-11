# Record 1340 — L4 Fork B Stage-0 reconnaissance: what a surviving positive family must already have passed

Date: 2026-09-11.
Status: READ-ONLY PAPER RECON (no Lean brick, no numerics, no Source change,
nothing self-authorized). Executes the pivot clause of record 1339 section 4
first item: open the L4 Fork B lane with the map-006/U1 discipline -
a Stage-0 audit of the SATISFIABILITY surface of the surviving obligation
before any construction is attempted. Every statement below is a pointer
into committed files. RH is not claimed.

## 1. The surviving obligation, in its canonical form

After records 1225 (quantifier repair, map 007), 1226 (A4 twin) and 1339
(radial leg closed), the `0 <= qw(g)` gate has exactly two formal entry
surfaces. L4, projection side, per map 007 section 2:

```text
L4   forall g in the healthy triple-vanishing class,
       Nonempty (ProjectionCutoffLimitContracts g lambda S globalBasis)
     -> SourceRH        [committed re-point
                         C1B5TargetSatisfiability.lean:118-135]
```

KEY OBSERVATION (recon finding R1): the pinned-family contract is NOT the
canonical obligation. The committed bridge chain consumes the
FAMILY-GENERAL contract

```text
CC20Concrete/PositiveTrace:
  structure PositiveTraceOperatorLimitFamily (basis) (g)  where
    traceOperator : Nat -> H -L[ℂ]-> H          <- DATA, any moving family
    traceClass   : forall n, IsTraceClassAlong ...
    positive     : forall n, (...).IsPositive   <- per-n, by construction
    remainder_tendsto_zero
    readback_tendsto_qw : Re Tr(traceOperator n) - remainder n -> qw g
  (ConnesWeilRH/Dev/C1PositiveTraceLimitBridge.lean:79-93)
```

via `qw_nonnegative_of_positiveTraceOperatorLimitFamily` (same file;
consumed at `C1Stage3ProjectionOperatorFamily.lean:221` and through the
capstone `healthy_sourceRH_of_right_healthyDetectorData_and_spectral_-
negativity`, `C1HealthyYoshidaSpectralNegativity.lean:585-610` as used in
the L4 proof body). `ProjectionCutoffLimitContracts` is just the pinning of
`traceOperator := cutoffProjectionOperator g lambda S globalBasis`
(`C1Stage3ProjectionOperatorFamily.lean:182-223`). So the honest L4 target
ladder re-points to:

```text
L4'  forall g vanishing, exists A MOVING positive trace-class family
     Q_n(g) with the two limit fields.        [family = construction space]
```

A one-line `sourceRH_of_all_vanishing_positiveTraceFamilies` brick
(~10 lines over committed parts) would make this re-point committed rather
than paper; registered below as beat B-cand-0, not executed here.

## 2. The committed wall (what any candidate Q_n has already had to pass)

Each entry is a committed no-go with the exact hypothesis it kills:

1. `Plain window` - `not_nonempty_cutoffLimitContracts_of_test_ne_zero`
   (`C1PositiveTraceCutoffVerdict.lean:64-90`): for EVERY nonzero g the
   remainder-corrected contract is UNINHABITED for the canonical
   window family - exact trace identity
   `Re Tr = (cutoffUpper - cutoffLower) * integral normSq g` (:43-58,
   file header :14-18) makes the traces monotone and linearly unbounded
   while the contract forces convergence. The header records WHY the
   family cannot carry arithmetic: the window bulk "carries no arithmetic
   content" (:16-18), and the constructive pointer:
   "A productive positive-trace limit needs a different detector family
   (Hilbert-transform/Mellin-conjugated windows), not further estimates on
   this one." (:18-20)
2. `Fixed response` - `not_projectionCutoffLimitContracts_of_fixedResponse
   _and_traceDefect_vanishing` (record 1211,
   `C1Stage3ProjectionContractObstruction.lean:38-60`): fixed response +
   vanishing insertion-sandwich trace + g nonzero => False.
3. `ANY bounded moving response` - the cofinal theorem
   `cutoffWindowToMovingResponseDefect_trace_re_cofinal_unbounded_of_-
   sourceTest_ne_zero` (`C1Stage3ProjectionDefectBounds.lean:616-627`):
   hypothesis is ONLY `IsTraceClassAlong` per n and an upper bound on
   `Re Tr(response n)` - the conclusion (detector - response is cofinally
   unbounded) holds for every such response family, with the file's own
   reading at :583-585: "Any surviving response owner must therefore
   carry an equally divergent trace". So the wall is NOT "the static
   family fails"; it is: **a surviving positive family's trace must
   DIVERGE at the detector's exact rate while the contract's readback
   converges - the cancellation must therefore live INSIDE the operator,
   not in the remainder or in a scalar subtraction** (1223 sec. 3 step 1
   words it as "counterterm INSIDE the kernel"; map 007 sec. 2).
4. `Estimation-based positivity` - dead by the 1226 C1 criterion (any
   socket bundled with healthiness and unconditionally giving S =>
   0 <= qw contradicts L1; only construction survives).
5. `Naive finite-part renormalization` - the 1212/1213 model twin showed
   the renormalized projection family reads FP = -3.321 * qw, NOT qw
   (38x outside band): subtracting the divergence is not arriving at the
   finite part; the FP value must be IDENTIFIED from the committed ledger
   (1223 sec. 3 step 1: "identify the linear bulk coefficient from the
   existing cutoff-trace ledger, rather than postulating its cancellation").

## 3. The feasible set after the wall (recon reading, honest about width)

Intersecting 1-5, a Fork B candidate is pinned to have ALL of:

```text
(a)  Q_n = traceProduct of an HS pair data (the only committed positivity
     by construction template: pairData.traceProduct, e.g.
     cutoffProjectionPairData) - so positivity is C^* K C form, and the
     counterterm must enter through the PAIR, not through a subtraction;
(b)  Re Tr(Q_n) converges to qw(g) despite (2)-(3): the divergent window
     bulk must be structurally absent from Q_n's kernel - i.e. the pair's
     window is NOT the plain cutoff window of the detector that its
     trace is compared against;
(c)  the limit value is the SAME-OWNER qw: identification route = the
     existing selectedArithmetic/residual/sandwich/defect ledger
     (realTrace_cutoffProjectionOperator_eq_selectedArithmetic_add_defects,
     C1Stage3ProjectionOperatorFamily.lean:138-178), whose
     selectedArithmeticCarrierSum + residual terms are the arithmetic
     finite parts and whose sandwich + windowDefect carry the bulk;
(d)  the vanishing hypothesis must be USED (it is the only input
     distinguishing g in the class): in the G8 campaign the same-owner
     readback's arithmetic side (records 1251, 1318-1330) consumed the
     triple vanishing exactly there;
(e)  the committed design pointer for (b): HT-/Mellin-conjugated windows
     (C1PositiveTraceCutoffVerdict.lean header :18-20) - windows whose
     exact trace identity is NOT window-length x mass (no bare bulk),
     because they carry the arithmetic weight inside the window.
```

Reading R2 (the sharp one): conditions (a)+(b)+(e) TOGETHER say Fork B is
not a repair of the Stage-3 family at all - it is the G8 machinery
re-expressed as a MOVING pair whose window is HT-conjugated. The G8
campaign already built the arithmetic-side identifications for a STATIC
response (c1Stage3 / stage3ProjectionKernel are n-frozen, the 1211
obstruction's trigger); what 1339 killed was the STATIC-window summability
route (`hcolumn`), NOT the ledger identities that feed (c). The difference
between the dead route and the open one is narrow and honest: the dead one
needed the bulk-free family's COLUMN energies summable; the open one needs
the HT-conjugated-window pair's TRACE LIMIT, a priori weaker (a limit
statement, not a summability statement). No theorem in-repo relates them;
do not claim one.

Reading R3 (the worry, registered): the wall items 1-3 are value-level
identities (trace = window x mass; cofinality of traces). They constrain
Tr(Q_n), not Q_n's kernel. A family satisfying (a)-(e) could still be
ruled out by a NEW committed-style no-go once specified - the map-006/U1
"Stage-0 satisfiability audit" for a concrete candidate remains a
prerequisite of any construction attempt. The recon found no committed
theorem that eliminates the HT-conjugated-window class (grep: the class is
named in the header pointer and produced nowhere in Source;
`CCM24HardyTitchmarsh`/`GlobalLogCrossing` supply the HT machinery).
So the class is OPEN and pre-named by the architecture itself. Precision
on "unfarmed": the Mellin/HT MACHINERY is committed at source level
(`CCM24GaussianMellin.lean`, `CCM24HardyTitchmarsh.lean`,
`CC20YoshidaMellin`, dev-side `MellinBandGamma`) - what does NOT exist
anywhere in-repo is a POSITIVE-TRACE PAIR-DATA family whose window is
HT-/Mellin-conjugated (grep: no `*PairData`/`cutoff*` construction consumes
the conjugation as its window); the machinery is waiting for the
construction, not the reverse.

## 4. A4 twin and the NM registry (parallel surfaces, untouched)

A4 (aggregate side, 1226 sec. 4 / map 007 sec. 2) is the SAME-shape marker
on the Bombieri P2 socket object, not the operator family: obligation =
per-vanishing-g aggregate socket witness with the two committed fields
(`C1BombieriP2Bridge.lean:198-206` consumes it to 0 <= qw). It shares the
capstone but not the wall of sec. 2 (no trace family involved); its audit
has not been run at Fork-B depth. The NM registry (map 006, 10 rows from
sweep round 1; the Suzuki R4.1 Weil-distribution Hilbert space and Bickel
R1.1 truncated-Hankel rows are the nearest published relatives of an
inside-kernel positivity template) is the companion lane's beat-3 SCREEN
obligation, not this lane's.

## 5. What this record does NOT establish

No candidate family, no brick, no numerics, no sign statement, no witness
of L4 or A4, no claim that the HT-conjugated class survives its own
Stage-0 audit (it has not had one), no relation claimed between the dead
summability route and the open limit obligation beyond "difference is
registered, not bridged". RH is not claimed.

## 6. Registered next beats (none executed; cost notes for the owner)

```text
B0  PAPER (this lane's own next step, ~half day): commit the exact
    HT-/Mellin-conjugated window definition sketch (operator, pair data,
    and the trace identity one WOULD need) and run the map-006/U1
    Stage-0 satisfiability audit against the whole sec. 2 wall ON PAPER;
    a committed no-go here closes Fork B cheaply, the way 1225 closed
    Cand-B.
B1  LEAN brick (~1 batch, low risk):
    sourceRH_of_all_vanishing_positiveTraceFamilies - make re-point R1
    committed (10 lines over existing parts) so any future construction
    attaches to the canonical contract.
B2  MODEL dry-fire (map-006 beat 4, fresh prereg, law 42; NOT the 1225
    ladder - that re-run stays closed): B0's family, positive control
    FIRST per U4, finite-part-vs-qw identity test at the known
    ground-truth qw = +1.895768e-02 control.
B3  If B0-B2 green: the 1223 sec. 3 counterterm specification record and
    the construction campaign proper (multi-record, research risk).
```

RH is not claimed.
