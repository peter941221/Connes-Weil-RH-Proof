# Proof 536: component-kernel consequences

## Result

Proof 532--535 made the remaining Gate 3U producer equivalent to two
component rows on the actual physical carrier:

    physical analysis
      = ambient antiresonant-loss column
        + moving-boundary adjoint column

Proof 536 proves the immediate kernel consequence of that interface.  If the
component rows factor the named raw four-term row, then:

    physical analysis x = 0
      -> raw four-term adjoint x = 0
      -> complete polar/raw mismatch adjoint x = 0

The same statement is also available on the adjacent left-co-defect kernel,
because the packed physical-analysis norm is exactly the adjacent
left-co-defect norm.

## What this changes

This does not create the source-specific component rows.  It makes the
consumer side sharper:

    component-row factorization
      -> pointwise left-co-defect norm bound
      -> raw zero-mode annihilation
      -> complete mismatch zero-mode annihilation

The signed row remains whole.  The proof does not split the two component rows
into independent estimates, and it does not introduce any new source axiom.

## Verification

The Ubuntu 24.04 WSL2 ext4 verification batch passed:

    Proof 536 source module      3116 jobs, PASS
    Proof 536 focused audit      3329 jobs, PASS
    CCM25Concrete aggregate      3806 jobs, PASS
    full repository              3887 jobs, PASS

The focused audit reports exactly:

    [propext, Classical.choice, Quot.sound]

for all nine audited principal declarations.  The new source and audit
contain no sorry, admit, or user axiom declaration, and the new files have no
line over 100 characters.  Existing repository linter warnings are unchanged.
The WSL localhost-proxy notice is external.

## Boundary

Proof 536 does not prove the family-uniform component-row producer, Gate 3U,
the finite-S sign, negative-owner integration, Burnol's identity, or
_root_.RiemannHypothesis.

The focused audit is:

    ConnesWeilRH/Dev/CCM24FiniteSCompletedJuliaComponentKernelAudit.lean
