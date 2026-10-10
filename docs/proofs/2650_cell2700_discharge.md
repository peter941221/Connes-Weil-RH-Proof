Record 2650: cell2700 coefficient-ball discharge — first unconditional cell certificate GREEN
Date: 2026-10-10

Result

Positive: `ConnesWeilRH/Dev/C1RouteACell2700Discharge2650.lean` built
green (0 error, 0 `uses sorry`, 0 module warning,
`ℹ [3925/3925] Built ... (1.2s)` + `Build completed successfully
(3925 jobs)`), and both new theorems depend only on the standard axiom
trio `[propext, Classical.choice, Quot.sound]`.

The lane-A audit priced "coefficient-ball discharge" as the only
genuine mathematical unknown (unknown #1, cheapest experiment:
cell2700, upper 57/500000000000 = 1.14e-10). This record converts
that unknown into a theorem, in two forms:

1. Region form — `cell2700_boxDischarge2650`: the 2551 certificate
   extends from the ad-hoc ball to the WHOLE record-2338 base
   coefficient region:

       forall i, (baseCoefficientBox2540 i).Mem (coefficients i) ->
       (∫ x in edgeLeftPosition2548..edgeRightPosition2548,
          ||weightedPhysical2539 (1/2) coefficients
            nodeModulation2541 x||) <= boundaryCellIntegralUpper2551

2. Unconditional form — `cell2700_center_discharge2650`: instantiating
   at the exact-rational box-center tuple leaves ZERO premises. The
   cell2700 integral upper 57/500000000000 holds outright at the
   center owner. This is the first cell of the 20480-obligation grid
   with no coefficient premise left in the statement.

Mechanism (why the discharge was two lines)

The bridge lemma already existed inside
`C1RouteACenterNode2540.lean`: `baseCoefficient_error_of_box2540`
proves box membership forces the ball, because the box half-widths
sum to at most `baseCoefficientError2540 = 1/10^30`
(`baseBox_widths2540`), and `baseCoefficientCenter_mem2540` proves
the center tuple sits in its own boxes. The 2551 hypothesis was never
a mathematical risk — it was a bookkeeping gap between the
record-2338 region (the certified state of knowledge about the
interpolation coefficients) and the ball parametrization the 2542-2551
pipeline chose. Record 2650 closes the gap; the margin 1.14e-10
survives discharge untouched.

What this does and does not claim

- Discharged: the conditional -> unconditional step for cell2700,
  sigma = +1/2, modulations fixed at `nodeModulation2541`.
- Still open (lane-A unknown #3): exact-owner transfer — asserting
  that a LIVE external computation's coefficient tuple lies in the
  boxes. The center-owner theorem needs no such assertion; the region
  form covers every tuple in the boxes but does not name the live one.
- Still open (lane-A unknown #2): the sigma = -1/2 boundary chain.
- No grid claim beyond cell2700; Producer GO, SourceRH, RH remain open.

Build evidence

One green build of the brick after repairing the WSL build mirror:
the mirror had drifted to an old-era branch
(`proof/s2-percommon-source-data`, HEAD d2ea7bc5) with 8354 Dev
sources missing and 25304 sources differing from main — the first
build failed on `bad import`/missing 2551, the second on a stale
olean of `CompactLogConvolution` (pre-`f12b4fe3`, lacking
`convolutionSquare_support_subset_two_mul_Ioo`). Root-cause fix:
`git checkout -f -B main origin/main` in the WSL tree (the Windows
side and origin/main are the source of truth), then the full
3925-job chain rebuilt clean at main. Laws: AGENTS 2cl.

Next obligations

1. Scale the discharge: the same two-line composition turns every
   conditional cell certificate into a region/unconditional pair;
   the next certified-cell candidates are cell5440 (midpoint
   envelope, 2543-2546) and the sigma = -1/2 chain (unknown #2).
2. Exact-owner transfer composition (unknown #3): the 2452 point
   import / 2453-54 node norm / 2455-59 quadrature import per-seam
   machinery, assembled to assert live-tuple membership in the boxes.
3. The 2649 next steps continue in parallel: 190-panel partition over
   column 3, then the (0,3) entry containment against the 2597
   rectangle.
