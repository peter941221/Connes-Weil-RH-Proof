# Proof 549: direct non-polar Douglas obstruction

Result: useful, but not a Gate 3U proof.

Proof 548 made uniform component rows a direct entrance to Proof 547's
non-polar Douglas gate.  Proof 549 records the matching obstruction side.

The exact no-go test is:

    suffixEulerFrameAmbientBoundaryAnalysis lambda p S x = 0
    and rawFourTerm^dagger x != 0

or equivalently, using the existing packed-analysis/co-defect kernel
identification:

    leftCoDefect x = 0
    and rawFourTerm^dagger x != 0.

Under either form, Lean now rules out:

    exists uniform direct non-polar Douglas bound
    exists uniform component-row package.

The proof path is:

    raw zero-mode on ker(leftCoDefect)
      -> non-polar gap adjoint nonzero there
      -> no uniform non-polar gap factor
      -> no uniform non-polar Douglas data
      -> no uniform component-row entrance.

Main declarations:

    noUniformNonpolarGapDouglas_of_gapAdjoint_ne_zero
    noExistsUniformNonpolarGapDouglas_of_gapAdjoint_ne_zero
    noUniformNonpolarGapDouglas_of_rawAdjoint_ne_zero
    noExistsUniformNonpolarGapDouglas_of_rawAdjoint_ne_zero
    noExistsUniformNonpolarGapDouglas_of_rawAdjoint_ne_zero_on_analysis
    noExistsUniformComponentReadout_of_rawAdjoint_ne_zero_on_analysis

Boundary:

Proof 549 does not construct such a zero-mode vector and does not prove the
uniform component rows.  It only fixes the exact kernel condition that every
future source producer must pass.  Gate 3U, the finite-S sign, Burnol's
identity, and _root_.RiemannHypothesis remain open.

Verification target:

    lake build \
      ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaNonpolarDouglasObstruction

Focused audit target:

    lake env lean \
      ConnesWeilRH/Dev/CCM24FiniteSCompletedJuliaNonpolarDouglasObstructionAudit.lean


Verification result:

    Proof 549 source module      PASS
    focused axiom audit          PASS
    CCM25Concrete aggregate      3819 jobs, PASS
    full repository              3900 jobs, PASS

All six audited declarations use exactly:

    [propext, Classical.choice, Quot.sound]

The WSL localhost-proxy warning is external to the Lean proof.
