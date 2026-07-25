# Proof 539: raw Douglas kernel obstruction

## Result

Proof 539 applies the Proof 537 kernel guard directly to the Proof 538 raw
Douglas interface.

If the raw Douglas inequality holds for one suffix, then the raw four-term
adjoint vanishes on the actual adjacent left-co-defect kernel:

    raw Douglas domination
    leftCoDefect x = 0
      -> rawFourTermAdjoint x = 0

After converting the produced raw readout to component rows, Lean also proves:

    raw Douglas domination
    leftCoDefect x = 0
      -> mismatchAdjoint x = 0

Consequently any nonzero raw or mismatch adjoint on that kernel rules out the
direct raw Douglas producer, including every uniform raw Douglas package.

## What this changes

Proof 538 made the target inequality explicit.  Proof 539 makes its first
necessary kernel test explicit:

    proposed raw Douglas estimate
      -> must annihilate left-co-defect kernel
      -> otherwise impossible

This prevents a future all-vector estimate from silently ignoring a kernel
mode where the physical energy is zero.

## Verification

The Ubuntu 24.04 WSL2 ext4 verification batch passed:

    Proof 539 source module      3330 jobs, PASS
    Proof 539 focused audit      3331 jobs, PASS
    CCM25Concrete aggregate      3809 jobs, PASS
    full repository              3890 jobs, PASS

The focused audit reports exactly:

    [propext, Classical.choice, Quot.sound]

for all nine audited principal declarations.  The new source and audit
contain no sorry, admit, or user axiom declaration, and the new files have no
line over 100 characters.  Existing repository linter warnings are unchanged.
The WSL localhost-proxy notice is external.

## Boundary

Proof 539 does not construct a nonzero obstruction vector and does not prove
the raw Douglas inequality.  It does not close Gate 3U, prove the finite-S
sign, prove Burnol's identity, or prove _root_.RiemannHypothesis.

The focused audit is:

    ConnesWeilRH/Dev/CCM24FiniteSCompletedJuliaRawDouglasObstructionAudit.lean
