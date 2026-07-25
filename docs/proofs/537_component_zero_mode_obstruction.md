# Proof 537: component zero-mode obstruction

## Result

Proof 537 turns Proof 536 into a reusable no-go criterion.

If there is a source-Sonin vector in the adjacent left-co-defect kernel on
which either the raw four-term adjoint or the complete polar/raw mismatch
adjoint is nonzero, then no component-row producer can exist for that suffix.

In symbols:

    leftCoDefect x = 0
    rawFourTermAdjoint x != 0
      -> no component-row factorization

and similarly:

    leftCoDefect x = 0
    mismatchAdjoint x != 0
      -> no component-row factorization

The same obstruction is lifted to the family-uniform level.  Since Proof 535
proves:

    exists uniform component readout
      <-> exists uniform physical Douglas domination,

the same zero-mode obstruction also rules out the current uniform physical
Douglas domination contract.

## What this changes

This is not a negative result about the actual route unless such a zero-mode
vector is supplied.  It is a formal guard:

    proposed producer
      -> must annihilate the left-co-defect kernel
      -> otherwise the producer is impossible

That guard is useful because it prevents a false Gate 3U producer from hiding
an unhandled kernel mode behind the abstract component-row interface.

## Verification

The Ubuntu 24.04 WSL2 ext4 verification batch passed:

    Proof 537 source module      3329 jobs, PASS
    Proof 537 focused audit      3330 jobs, PASS
    CCM25Concrete aggregate      3807 jobs, PASS
    full repository              3888 jobs, PASS

The focused audit reports exactly:

    [propext, Classical.choice, Quot.sound]

for all eight audited principal declarations.  The new source and audit
contain no sorry, admit, or user axiom declaration, and the new files have no
line over 100 characters.  Existing repository linter warnings are unchanged.
The WSL localhost-proxy notice is external.

## Boundary

Proof 537 does not construct a zero-mode obstruction vector.  It does not
prove or disprove the family-uniform component-row producer, Gate 3U, the
finite-S sign, negative-owner integration, Burnol's identity, or
_root_.RiemannHypothesis.

The focused audit is:

    ConnesWeilRH/Dev/CCM24FiniteSCompletedJuliaComponentObstructionAudit.lean
