# Proof 545: non-polar gap kernel sanity

Result: useful, but not a Gate 3U producer.

## What It Is

This proof identifies the exact zero-mode test for the active non-polar gap.
Lean proves that the adjoint of the non-polar localization gap has the same
kernel test as the local polar/raw mismatch, and on the adjacent
left-co-defect kernel this is equivalent to the raw four-term adjoint test.

The key theorem is:

    leftCoDefect x = 0
      ->
        gap^dagger x = 0
          <-> rawFourTerm^dagger x = 0.

## Why It Matters

This removes ambiguity from the Proof 543 obstruction.  A future proof cannot
claim a non-polar gap factor while hiding a nonzero raw-row zero mode in the
left-co-defect kernel.

Equivalently:

    rawFourTerm^dagger x != 0 on ker(leftCoDefect)
      -> no uniform non-polar gap factor
      -> no uniform physical domination producer.

## Boundary

This proof does not construct a nonzero obstruction vector and does not prove
the kernel annihilation theorem unconditionally.  It proves the exact test
that any Gate 3U producer must pass.

The source module is:

    ConnesWeilRH/Source/CCM25Concrete/
      CCM24FiniteSCompletedJuliaNonpolarGapKernel.lean

The focused audit is:

    ConnesWeilRH/Dev/
      CCM24FiniteSCompletedJuliaNonpolarGapKernelAudit.lean
