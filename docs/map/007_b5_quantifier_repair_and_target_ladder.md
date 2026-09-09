# 007 - Records 1225/1226: B5 producer quantifier repair and the surviving target ladder

Date: 2026-09-09.

Authority: Binding companion to [`003`](003_b1_b5_minimal_exit_route_selection.md)
- binding on WHICH propositions may be named as B5-side producer targets and
on the ladder of surviving obligations; subordinate to `003` on route choice
itself. This record adds no new theorem: every statement below is a pointer
into committed records and committed Lean files. RH is not claimed.

Evidence base: record
[1225](../proofs/1225_b5_target_satisfiability_audit_and_positive_control_preregistration.md)
(sections 1-3, amendments A8/A9, sections 7-8) and record
[1226](../proofs/1226_signed_tail_recon_stageA_kill_and_repoint_preregistration.md)
(sections 1-4, landed FULL-LANDING).

## 1. The quantifier repair (what changed and what did not)

The pre-1225 producer premise for the B5 exit

```text
  hproducer :  forall rho, (1/2 < rho.1.re) ->
               exists g,  HealthyYoshidaDetectorData rho.1 g
                      /\ Nonempty (ProjectionCutoffLimitContracts g ...)
```

(`C1P2BilateralProfileExit.lean:711-731`) is NOT an analytic obligation.
Record 1225 sections 1 (F1-F3) proves, from committed equivalences alone:

- (F1) detector data forces `qw g < 0` (`C1HealthyYoshidaDetector.lean:182-200`
  + `qw_eq_spectralWeilValue_centerTwo`);
- (F2) the contract family forces `0 <= qw g` unconditionally
  (`C1Stage3ProjectionOperatorFamily.lean:85-94, 214-222`);
- (F3) so the conjunction has NO witness for any `g`, and `hproducer` is
  `SourceRH` in disguise (true only vacuously).

The repair moves the contradiction OUT of the premise and into the capstone,
where it already exists as a committed theorem
(`healthy_sourceRH_of_right_healthyDetectorData_and_spectral_nonneg`,
`C1HealthyYoshidaSpectralNegativity.lean:585-610`). The producer target
becomes the UNIVERSAL contract:

```text
  L4  (projection-cutoff side, record 1225 sec. 3):
      forall g in the healthy triple-vanishing class,
        Nonempty (ProjectionCutoffLimitContracts g lambda S globalBasis)
      ->  SourceRH                      [committed re-point theorem]

  A4  (aggregate side, record 1226 sec. 4):
      forall g in the same vanishing class,
        exists an aggregate P2 socket with the two committed fields
        (qw = form + Re tail;  -form <= Re tail)
      ->  0 <= qw g                     [C1BombieriP2Bridge.lean:198-206]
      ->  SourceRH via the same capstone.
```

What did NOT change: route ruling `003` (healthy `CompactLog`, B5-shaped);
the frozen universal-B1 campaign (the L4/A4 quantifier ranges only over the
healthy triple-vanishing class, the capstone's own committed premise shape -
it is NOT a lift to all compact supports); every freeze card; the
`normalized*` socket prohibition.

## 2. The target ladder (survivors, with current status)

```text
+--------+-------------------------------------+--------------------------+
| Target | Obligation                          | Status 2026-09-09      |
+--------+-------------------------------------+--------------------------+
| L4     | per-VANISHING-g positive trace       | OPEN - analytic         |
|        | family Q_n with Re Tr(Q_n) -> qw(g), | construction ONLY       |
|        | counterterm INSIDE the kernel         | (Fork B); numerics      |
|        |                                     | scout CLOSED (sec. 3)   |
+--------+-------------------------------------+--------------------------+
| A4     | per-vanishing-g aggregate socket     | OPEN - same shape,      |
|        | witness (two committed fields        | landed green-first-try  |
|        | compose to 0 <= qw g)                | as an exit theorem      |
+--------+-------------------------------------+--------------------------+
| dead   | bundled hproducer conjunction        | REFUTED 1225 F1-F3     |
| dead   | 1209 signed-tail exit (a)            | FORMALLY DEAD 1226    |
| wtd    | Cand-B moving-response brief         | WITHDRAWN 1225 sec. 2 |
| super  | 1224 Stage-B "engineering verdict"   | reclassified by 1225   |
|        | (RANK-3 non-separability)            | F4: structurally        |
|        |                                     | guaranteed failure      |
+--------+-------------------------------------+--------------------------+
```

L4 and A4 are MARKERS, not campaigns: they name the propositions a future
campaign must attack. Neither is authorized to spawn numerical work by this
record; new-math campaigns entering through the NM loop follow map
[`006`](006_new_math_creation_workflow.md).

## 3. The instrument verdict of record 1225 (capture law) and the closure

The preregistered positive control (known-answer calibration of the trace
ladder on the control family) terminated ABORTED-UNINFORMATIVE at ladder
rung 4: reproduced digit-exact across two independent invocations, then
`A4b FAILED: tail_gap 5.40e-08 at n=16, N=16384` against the pre-registered
1e-8 gate - the failure mode reserved in advance in amendment A8 as a REAL
capture finding, predicted at ~2.5e-8 in A9 before the rerun.

Yield (MODEL numbers, law 65):

- CAPTURE LAW: fixed rank 2560 cannot certify exact W-trace capture from
  `n = 16` upward in this family (observed scaling ~ x2.7 per dt-doubling,
  ~ x30 per n-doubling).
- DETERMINISM: the rig reproduces to the digit across invocations; any
  future discrepancy is attributable to protocol change, not noise.
- MAGNITUDE PRE-INDICATION: the bulk control term sat at ~1.4% of
  `qw = +1.895768e-02`, so even a passing rung 4 was headed for a
  MISMATCH verdict on this family - confirming record 1213's
  FP != qw lesson from the positive side.

Closure: on Peter's 2026-09-09 decision the numerical scout for L4 is
CLOSED on this yield; no re-run of the fixed-rank ladder is authorized, and
a rank-scaled recapture would require a fresh preregistration (law 42) that
this ladder's evidence does not currently recommend. The L4 obligation is
therefore PURELY ANALYTIC from here: a constructive Fork-B family whose
positivity and trace-readback are proved, not measured.

## 4. What this record does NOT claim

No witness of L4 or A4. No sign result for `qw(g)`. No reopening of any
frozen route. No numeric datum here is anything but a MODEL twin. The
capstone composition (universal contract -> SourceRH -> RH) is committed
machinery awaiting its premise; the premise is open.
