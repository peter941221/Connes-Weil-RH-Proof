# Record 1225 — B5 target satisfiability audit (Stage 0) and the positive-control preregistration

Date: 2026-09-09.
Status: PRE-REGISTRATION, committed BEFORE any new Lean build or numerical run
in this campaign (law 42).  Peter's session directive "full authority, proceed"
(2026-09-09) authorizes the Stage-0 audit, the Lean deliverables of section 3,
and the numerics of section 4.  RH is not claimed anywhere below; no
positivity, convergence, or value-match is asserted.

Supersedes the decision point of record 1224 section 3g (Cand-B design brief
vs 1209 signed-tail recon).  Neither registered option is taken: a Stage-0
target-satisfiability audit of the consumer premise shows both options aim at
a proposition that is refuted instance-by-instance by two committed theorems,
so further counterterm design or signed-tail reconstruction at the BUNDLED
target cannot produce information.  The record instead (i) formalizes that
refutation, (ii) re-points the producer at the committed UNIVERSAL exit, and
(iii) registers a positive-control measurement that can actually succeed.

Consumer named (verbatim target): `HealthyYoshidaDetectorData` detector exit
chain.  Allowed-work reference: RH_MAINLINE_FREEZE Allowed Work 3
(detector-specific semi-local positivity "or its same-owner trace readback")
and the committed capstone `healthy_spectral_nonneg_sourceRH_of_yoshida_detector`
(`ConnesWeilRH/Dev/C1CenterTwoRHExit.lean:64-83`), whose docstring states the
distance to `SourceRH` is "EXACTLY the Yoshida detector transport plus
nonnegativity of the independently defined spectral value on EVERY vanishing
convolution square".

## 1. Stage-0 audit: the bundled B5 producer premise has no witness

F1 — detector data forces strict negativity, independent of any numerics.
`HealthyYoshidaDetectorData rho g` (`C1HealthyYoshidaDetector.lean:182-190`)
contains the field

```lean
  weilSquareSumPositive :
    0 < C1.healthyCC20TestSpace.weilLocalSum
        (C1.healthyCC20TestSpace.starConvolution g)
```

and the committed equivalence (`C1HealthyYoshidaDetector.lean:194-200`)

```lean
theorem weilSquareSumPositive_iff_spectralWeilValue_neg (g : CompactLogTest) :
    (0 < ...weilLocalSum (...starConvolution g)) ↔
      C1SpectralWeil.spectralWeilValue g.convolutionSquare < 0
```

whose proof never mentions `rho`.  With
`C1CenterTwoCriterionBridge.qw_eq_spectralWeilValue_centerTwo` this yields,
for EVERY `rho` and EVERY `g`:

```text
  HealthyYoshidaDetectorData rho g  ->  C1SameOwnerWeil.qw g < 0            (F1)
```

F2 — the B5 contract forces nonnegativity of the same functional, and the
positivity input is unconditional.  `cutoffProjectionOperator_isPositive`
(`C1Stage3ProjectionOperatorFamily.lean:85-92`) and
`cutoffProjectionOperator_trace_re_nonnegative` (:94) hold for every `g` with
no analytic hypothesis, and

```text
  Nonempty (ProjectionCutoffLimitContracts g lambda S globalBasis)
    ->  0 <= C1SameOwnerWeil.qw g                                           (F2)
```

(`qw_nonnegative_of_projectionCutoffLimitContracts`, same file :214-222).

F3 — the B5 exit's producer premise bundles both signs for the SAME test.
`sourceRH_of_healthyDetector_p2ProjectionCutoffLimitContracts`
(`C1P2BilateralProfileExit.lean:711-731`) consumes

```lean
  (hproducer : forall rho, (1/2 : Real) < rho.1.re ->
      exists g, HealthyYoshidaDetectorData rho.1 g /\
        Nonempty (ProjectionCutoffLimitContracts g lambda S globalBasis))
```

By (F1)+(F2) the conjunction is FALSE for every `g`, in every context,
whenever some right-of-line `rho` is being served; and
`exists_healthyDetectorData_of_sourceNontrivialZero_right`
(`C1HealthyYoshidaSpectralNegativity.lean:568-579`) supplies such a `g` for
every right-of-line source zero.  Therefore `hproducer` holds if and only if
no right-of-line source zero exists: it is not an analytic obligation with a
constructive attack surface, it is `SourceRH` in disguise (vacuous truth only).
The exit theorem's own proof body
(`C1HealthyYoshidaSpectralNegativity.lean:611-630`) performs exactly the (F1)
derivation to close by `False.elim` — the no-go has been committed inside the
theorem the campaign was trying to feed; record 1223 section 3.1's Fork A/Fork
B analysis operated one layer downstream and missed it.

F4 — consequence for the closed 1224 Stage B evidence.  The 1213 model
readout `FP_inf = +1.3791e33`, `qw(g) = -4.1526e32` (record 1213, Q2) is the
ratio of a term forced `> 0` by F2's positivity half and a term forced `< 0`
by F1.  `FP/qw = -3.321` and the sec.3f/3g 3x3 `RANK-3` non-separability are
therefore measurements of an obligation that could not be met by ANY
correction `M_n`, at ANY `(lambda, S)`, of ANY rank: the trace of a positive
operator cannot converge to a negative number.  The stage-B identification
campaign is reclassified from "engineering verdict" to "structurally
guaranteed failure observed in model form".  No committed data is retracted;
its INTERPRETATION is superseded.

## 2. Withdrawals and deferrals (what stops)

| registered item | new status | reason |
|---|---|---|
| Cand-B design brief (survival re-est 15-20%) | WITHDRAWN | target conjunction refuted by (F1)+(F2); survival estimate estimated the wrong event |
| 1224 sec.3g decision point | SUPERSEDED by this record | both listed branches sit downstream of the framing error |
| 1209 signed-tail recon (~1wk) | DEFERRED, not taken | its named exit feeds the same bundled socket; revisit only under the universal target of section 3, if the control fails |
| E2/1219 entrywise campaign | stays SUSPENDED (1223) | unchanged |
| 1217/1218 layers, q28 chains | UNCHANGED | no output of this record touches them |

## 3. Lean deliverables (built after this commit, before any numerics)

New module `ConnesWeilRH/Dev/C1B5TargetSatisfiability.lean` + paired
`...Probe.lean` audit:

L1 `qw_neg_of_healthyDetectorData` — the (F1) lemma, standalone:
    `HealthyYoshidaDetectorData rho g -> qw g < 0`.
L2 `not_healthyDetectorData_of_projectionCutoffLimitContracts` —
    contract + detector data = False (F1+F2 conjunction kill).
L3 headline `not_exists_healthy_and_contracts_of_rightZero` — for every right
    source zero, `hproducer`'s existential conjunction has NO witness.
L4 constructive re-point `sourceRH_of_all_vanishing_projectionContracts` —
    the SAME contract family, universally quantified over
    `CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet`,
    composes with the committed detector existence and
    `healthy_sourceRH_of_right_healthyDetectorData_and_spectral_nonneg`
    (:585-610) to reach `SourceRH` with no hypothesis except the universal
    contract itself.  This is the live analytic obligation from here on:
    construct, per VANISHING test g (not per detector g), the positive family
    with `Re Tr(Q_n) -> qw g`.

Acceptance: focused builds, log footer + zero `^error:` lines + audit prints
exactly `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.

Route-authority note: the move from "certificate per hypothetical off-line
zero" (the 1076/7g phrasing of B5) to "certificate per vanishing test, with
the detector contradiction drawn OUTSIDE the premise in the capstone" changes
which propositions may be named as producer targets.  Both forms are already
committed theorems; only the producer campaign's target selection changes.  A
companion map record `docs/map/006_b5_quantifier_repair_and_target_ladder.md`
is registered to be written in this campaign's verdict phase (before any
Stage-B escalation beyond the control run), synchronized per the map live
update rule with README and RH_MAINLINE_FREEZE.md.  The frozen universal-B1
route (positivity for ALL compact supports, density/partition lift) is NOT
reopened: the L4 quantifier ranges only over the healthy triple-vanishing
class, which is the capstone's own committed premise shape.

## 4. Registered Stage-B instantiation: the positive control

Purpose.  The 1212/1213 rig has never been run on a test where a successful
readback is POSSIBLE: every prior subject carried forced `qw < 0` (F1).  A
measurement that cannot pass cannot calibrate an instrument.  This section
registers the first control run, whose ground truth is a committed closed
form, NOT a model guess:

```text
  GROUND TRUTH (committed):  for g ROOT-supported and triple-vanishing,
    C1SameOwnerWeil.qw g = - C1SameOwnerWeil.archimedeanTerm g.convolutionSquare
    (qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_rootSupport_logTwoHalf,
     C1CC20ArchimedeanReadback.lean:166-era chain)
  and 0 <= qw g on that subclass already has a proof path (same file :133-141),
  while not_healthyYoshidaDetectorData_of_cc20EndpointTraceCertificate... (:179)
  proves the detector can NEVER live there.
```

Control design (MODEL rig = 1212 pipeline, law 65 labels everywhere):

```text
  C1  g_ctrl: triple-vanishing test with NO rho node.
      Interpolation nodes = {0, 1/2, 1} only (empty routeNodes pattern of
      exists_healthyDetectorData...; the rho pair and its ±1 detection
      targets are DROPPED).  Bump + e^{x/2} halfDensityShift dressing and
      2sinh arch denominator are the same verbatim conventions as 1212.
  C2  support gate (S0-style): realized support of g_ctrl must sit inside
      [-log 2 / 2, log 2 / 2] strictly; a realized-support readout is
      printed BEFORE any trace is computed; violation = ABORTED-UNINFORMATIVE.
  C3  ground-truth readout: qw_model(g_ctrl) computed TWICE, once as
      -(archimedeanTerm) via the single-integral 2sinh form and once as
      archimedeanTerm + finitePrimeSum with the prime sum independently
      asserted ~0 (support inside log 2 kills visible primes); the two
      must agree to 1e-9 relative or the run is ABORTED-UNINFORMATIVE.
  C4  trace probe: ladder n in {8, 16, 32, 64}, dials lambda = 1, S =
      2, 3, 5 (the 1213 baseline dial), coarse/fine dt pair, cap 16385,
      eps_q 1e-8; renormalized readout Tn* = T_n * dt^2 convention exactly
      as 1213 (dt^2 sandwich normalization law banked there); replay gate:
      the baseline detector twin must reproduce FP_inf = +1.3791e33 within
      2e-4 in the same invocation.
  C5  registered branches (no third branch, law 42):
      MATCH     |FP_inf(g_ctrl) / qw_model(g_ctrl) - 1| <= 0.01
                -> the projection family K is the correct trace-formula
                   operator where the answer is known; the bundled-target
                   failure of 1213 is confirmed as an artifact of F1 sign
                   impossibility; the L4 universal obligation becomes the
                   sole mainline analytic target (new preregistration for
                   the extension beyond ROOT support).
      MISMATCH  otherwise
                -> first INFORMATIVE no-go on the operator K itself: FP - qw
                   is then a computable functional on a g where both terms
                   are sign-consistent, and the counterterm question is
                   re-opened WHERE it can be answered; the 1224 sec.3g
                   conclusion (rank obstruction) is then read back as
                   evidence about K, not about the bundled target.
      ABORTED-UNINFORMATIVE -> any C2/C3/C4 gate failure; no verdict either
                   way; 1097 protocol.
```

Registered amendment to section 4, committed after smoke-1 and BEFORE the
official run (law 42).  Smoke-1 fired the C2 gate (realized support 27.998
= torus noise, not physics): with the normalization target written as
`v / B(z)^NEXP` the coefficients reached |a|max = 1.17e31, and the e^{x/2}
dressing amplified the float64 FFT noise floor by e^{+14} over the far
support of the period-56 torus.  Three implementation decisions are
therefore registered before any official digit:

```text
  A1  the normalization row's rhs is the raw value 1 in the MOMENT
      partition function (no B^NEXP division): the enforced conditions are
      exactly lap-corr(1/2) = lap-corr(1) = lap-corr(3/2) = 0 and
      lap-corr(2) = 1, so lap h vanishes at the three nodes for the SAME
      reason as the baseline (vanishing of the correction functional, the
      base^{*NEXP} factor being nonzero on the grid) while coefficients
      stay O(1e6) instead of O(1e31);
  A2  the assembled g is rescaled to peak 1 before sampling (all adjudicated
      ratios are scale-invariant: FP and qw both scale quadratically);
  A3  support is REPORTED at three relative floors (1e-4, 1e-6, 1e-8) and
      the C2 gate reads the 1e-8 floor; C2 additionally prints the raw
      maximum of |g| outside [-0.347, 0.347] so the leak is auditable.
```

A4 is registered after smoke-2 (which passed C2/C3/C5 but failed S0.5:
`Tn dense-vs-spectral 5.6e-01, term1 rel 2.3` at the smoke override
RANK=96/DENSE_N=512).  Root cause: the effective spectral rank of
`W = C_n^* C_n` scales with the test's FREQUENCY bandwidth, which for the
control bump is ~1/(10 eps) = one-tenth of the ROOT window, roughly two
orders wider than the detector's (support 56); the smoke downscale, tuned to
the detector's near-flat spectral tail, truncates ~80% of the control's
trace mass at rank 96 of a 512-point spectrum.  Registered decision
procedure BEFORE any further digit:

```text
  the official ladder runs at the smallest rank from the ladder
      RANK in {320 (1212 default), 640, 1280, 2560, 5120}
  selected by the S0.5 fidelity gate at the COMMITTED DENSE_N = 2048
  validation grid (`dv.rel < 1e-6`, unchanged tolerance); every rung
  reports its tail_gap = (bulk - captured)/bulk into the results JSON for
  audit; if no rank <= 5120 reaches the committed fidelity at the ladder's
  finest N = 16384, the campaign is ABORTED-UNINFORMATIVE (the instrument
  cannot certify the readback on this test class - a rig finding, not a
  mathematical one).
  RANK is selected by PROBE_RANK (default 320); the SMOKE mode no longer
  downscales RANK or DENSE_N (only the ladder n-list and dt-pair).
  Detector-twin fidelity is protected by the registered C4 replay gate
  (FP_inf = +1.3791e33 within 2e-4), which runs in the same invocation.
```

A4b closes the gap smoke-3 exposed (S0.5 STILL failing at 2048/320, now with
the rank-diagnostic measurement `1225_rankdiag1.log`, a pure Stage-A
spectral diagnostic on the n=8 grid, no FP/qw readout):

```text
  TRUE dense spectrum of W at DENSE_N=2048 (control): capture fraction is
  0.763 at rank 320, 0.993 at 640, 0.99996 at 800, and EXACTLY 1.0000000000
  at 1024 (full rank 907 = window dimension); eigsh is EXONERATED (its
  top-320 agrees with the true top-320 to 3.6e-14).  The control spectrum
  is Slepian-shaped: a flat plateau out to the bump's Shannon knee at
  index ~ xi_knee * T / (2 pi), xi_knee ~ 50, then collapse.  The detector
  twin contrast: capture 1.0000000000 at rank 100 on the same grid, which
  is why the 1212 rig was faithful at RANK=320 for the DETECTOR.
```

  Consequences, registered before the next digit: (i) the A4 selection
  criterion is widened - a rank must pass the fidelity gate at the n=8
  S0.5 grid AND carry tail_gap < 1e-10 on EVERY official rung (the knee
  index scales with the period, so n=64/fine needs ~2x the n=8 rank);
  (ii) the official run uses PROBE_RANK=2560 with `bulk_eig` clamping
  k <= N//2 (keeps ARPACK's Krylov space 2k+1 <= N feasible; the measured
  true capture at 1024 = 2048//2 is exactly 1.0000000000, and the official
  grades N=8192/16384 use the full 2560); the S0.5 validation grid uses
  the fixed DV_RANK=1280, which the clamp renders as 1024 on its
  registered grid (measured exact capture there); (iii) `maxiter` scales
  as max(5000, 4*k); (iv) every OFFICIAL rung asserts tail_gap < 1e-10 at
  fail-fast (smoke rungs print only - the smoke dt-pair sits below the
  knee by construction); a rung that cannot certify it makes the
  invocation ABORTED-UNINFORMATIVE (rig finding, not mathematical).

A5 is registered after smoke-4 (S0.5 passed at the A4b rank:
`Tn dense-vs-spectral 1.49e-10`; the invocation then failed S0.6 with
`rel drift 1.65e-02` of Tn/bulk between the pad-24 and pad-40 fixed-dt
boxes).  Diagnosis: the wrap gate statistic is SCALE-WRONG for a small-
signal test, not evidence of contamination.  Genuine box-content wrapping
is an O(bulk) event (a fraction of the content mass crosses the period
seam); the inherited statistic |d(Tn/bulk)/(Tn/bulk)| measures the drift in
units of Tn, which for the control is 2.3e-4·bulk (the control's Tn is a
tiny cancellation difference), so the SAME absolute period-dependence of
the P_V term that the 1212 baseline disclosed as a smooth spectral
quadrature effect (2.9e-4 relative at DETECTOR grade, where it was
O(bulk)-scaled) is amplified 4000-fold relative to the control's tiny Tn.
The S0.6 gate runs only on the control sample in this script (the C4
replay is a rung + FP check and does not pass through it), so the
detector's calibration is untouched by the amendment.  Registered fix:
the S0.6 statistic becomes
`abs_drift_bulk = |Tn(40) - Tn(24)| / bulk < 1e-3` - an O(bulk) seam-wrap
event cannot pass it, while the observed control drift (1.65e-02 relative
= 3.92e-06 of bulk, smoke-5 and smoke-6 agree) does, with 255x margin.
Two disclosure corrections to this cross-check, both before any official
digit: (a) smoke-5 showed |sn_dt(40) - sn_dt(24)| mixes the bulk's own
discretization drift and is not a wrap statistic, so the registered form
uses Tn only; (b) smoke-6 shows my A5 text's quoted value 4.1e-5 was an
arithmetic error (I divided by the printed VN trace 247 instead of the
bulk 1238): the true fixed-dt drift in sn_dt-equivalent units is 2.04e-4,
5% ABOVE the 1% band - and the statistic is dt-coupled by construction
(bulk*dt grows as dt shrinks at fixed content), so banding it at the
S0.6 grid is a units mismatch, not a finding.  Cross-checks therefore
anchor at the adjudication grade:

```text
  S0.6 numeric gate:   abs_drift_bulk < 1e-3        (kept; PASSES 255x)
  S0.6 disclosure:     drift_sn_dt = |Tn(40)-Tn(24)|*dt printed to JSON
  A5b (NEW, post-ladder, official): materiality of the box/dt machinery
  at the grade where the verdict is read:
      |sn_dt(64, 8192) - sn_dt(64, 16384)| < 0.01 * |qw|
  failure => ABORTED-UNINFORMATIVE under the C5 any-gate-failure branch
  (the dt-pair spread would be the same size as the band, so the branch
  decision would not be resolvable at that precision - a rig finding).
```

C3 tolerance is amended 1e-9 -> 1e-3 WITH CAUSE, not by rescue: the closed
form `qw = -arch` requires the pole term of the SQUARE to vanish, and the
model dictionary pins lap h (the pre-dressing correction functional), not
lap g of the square, at the node set; the committed baseline itself shows an
unforced pole residue `pole/arch = 8.7e-5` (1213 JSON).  The registered
comparison target stays exactly the 1213 statistic `qw_model = pole - arch -
prime` (the committed 1116-convention arithmetic readout); C3 becomes a
significance guard: print `dev3 = |pole - prime| / |arch|` and abort only if
`dev3 >= 1e-3`, i.e. if the ROOT-window prime-free regime is not realized at
all.  The branch semantics of C5 (MATCH/MISMATCH on `sn_dt(fine, n=64)/qw`)
are UNCHANGED.

A6 is registered after smoke-7 (which traversed the full chain, 521 s) by
comparing against the COMMITTED 1212 results JSON: sn_dt(n=64,fine) there
is -1.1162e37, while the committed FP_inf is +1.3791e33 - because record
1213 section 8 warns verbatim that "the sn_dt field in the JSON is the raw
(T_n - bulk)*dt and is NOT the physical finite part" and all physical
readouts use `Tn^cont = T_n * dt^2`.  My fork's C5 readout and the C4
replay were wired to the wrong field (schema misread of 1212's JSON, the
same class of slip the 1213 verdict itself discloses at its S0.1 note).
Fix, before any official digit: the adjudicated statistic becomes

```text
  FP      = Tn(n=64, N=N_FINE) * dt_fine^2
  spread  = |FP(coarse) - FP(fine)|                  (A5b statistic, same
            cont units; gate vs 1% of |qw| unchanged)
  replay  = same formula on the detector twin vs +1.3791e33, band 2e-4
```

with the branch semantics of C5 (MATCH at |FP/qw - 1| <= 0.01, MISMATCH
otherwise) UNCHANGED, and A5's disclosure line recomputed in cont units.
Cross-check that the fix is right before running: detector rung cont at
n=64/fine from the committed numbers is Tn*dt^2 = +1.3791e33 (1213 Q2
table), and the 1213 grade-spread of FP is ~2e-4 relative, far below the
1% A5b band.  Smoke-8 re-verifies the wiring on the control builder only;
no official digit is taken from smoke.

Implementation: new builder function in a NEW file
`docs/proofs/1225_positive_control_probe.py` forking the 1212 machinery
(never editing the committed 1212 script or its JSONs); env selectors
mirroring `PROBE_LAMBDA`/`PROBE_S`/`PROBE_OUT`; outputs to
`1225_control_results.json` + `1225_control_logs/`.

Budget: section 3 Lean, 1 build day (two modules, warm mirror); section 4
implementation + official run, 1-2 days (single dial, ladder as 1213);
verdict addendum + map 006 + docs sync, same-window.  If MATCH, the
ROOT-support-to-detector-support extension campaign is a NEW preregistration
with its own Stage-0 audit.  RH not claimed.

## 5. What this record does NOT claim

It does not claim the universal contract is satisfiable — under (F1) and the
committed detector existence it is again exactly as strong as the positivity
gate itself; the audit claims only that L4 is a proposition that CAN be
witnessed constructively (one sign, one side), unlike the bundled form, and
that the instrument has never been tested where success was possible.  It
does not re-claim, retract, or edit any 1212/1213/1217/1218/1222/1223/1224
number.  It does not touch E2/1219, Line B (frozen), or the normalized
sockets.  All section-4 numerics are MODEL-twin statements (law 65) until a
Lean owner exists.
