# Proof 538: raw Douglas readout

## Result

Proof 538 states the missing raw producer as a direct Douglas inequality.
For every source vector:

    ||rawFourTermAdjoint x||^2
      <= C^2 *
         (||ambientLossColumn x||^2 + ||boundary^dagger x||^2)

is equivalent to a bounded readout of the named raw four-term row from the
actual packed physical-analysis carrier.

At the uniform existence level, Lean now proves:

    uniform raw Douglas domination
      <-> uniform raw readout
      <-> uniform component readout
      <-> uniform physical Douglas domination.

## What this changes

The current Gate 3U bottom is no longer only an existential readout interface.
It can be pursued as one concrete all-vector inequality for the recombined raw
four-term adjoint against the actual summed physical energy.

This matters because the inequality is checked before quotienting, before
basis reduction, and before any separate ambient/boundary estimate:

    one signed raw row
      -> one packed physical energy
      -> Douglas readout

No source-specific bound is constructed here.

## Verification

The Ubuntu 24.04 WSL2 ext4 verification batch passed:

    Proof 538 source module      3328 jobs, PASS
    Proof 538 focused audit      3329 jobs, PASS
    CCM25Concrete aggregate      3808 jobs, PASS
    full repository              3889 jobs, PASS

The focused audit reports exactly:

    [propext, Classical.choice, Quot.sound]

for all nine audited principal declarations.  The new source and audit
contain no sorry, admit, or user axiom declaration, and the new files have no
line over 100 characters.  Existing repository linter warnings are unchanged.
The WSL localhost-proxy notice is external.

## Boundary

Proof 538 does not prove the raw Douglas inequality, construct a
family-uniform producer, close Gate 3U, prove the finite-S sign, prove
Burnol's identity, or prove _root_.RiemannHypothesis.

The focused audit is:

    ConnesWeilRH/Dev/CCM24FiniteSCompletedJuliaRawDouglasReadoutAudit.lean
