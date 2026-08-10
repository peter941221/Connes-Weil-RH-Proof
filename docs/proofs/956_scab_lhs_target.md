# 956 - Wall-A 1.4 reduces to a single arch/prime scalar (ScabLhsZero)

Date: 2026-08-10.  Status: axiom-clean structural reduction (WSL-verified).
RH NOT claimed.

## What

New file ConnesWeilRH/Dev/ScabLhsZero.lean proves (WSL green, 2960 jobs,
#print axioms = [propext, Classical.choice, Quot.sound], 0 sorry, 0 new axiom):

- polePairing_eq_polarSquare : polePairing(f) = poleFunctional(convolution f)
  on the healthy carrier (definitional).
- lhs_zero : poleFunctional(convolution f) - polePairing(f) = 0.
- scab_target_iff_arch_prime :
    ScabPoleArchTarget iff 2*totalArchimedean(convolution) + (a-b) = 0.

## Why it closes half of Wall-A 1.4

The SCAL scalar identity had a pole/pole left side.  It is now proved to be
identically ZERO (structural: polePairing = poleFunctional of the convolution
square).  The entire open content of Wall-A 1.4 reduces to the single scalar
relation

    2*totalArchimedean(convolution f) + (global - restricted) = 0

the arch/prime-difference relation - the genuine Weil-explicit-formula content.

## Honest bottom

That arch/prime relation remains OPEN (real analysis: computing totalArchimedean
on the test's compact-log representation and the {2} prime sums, then verifying
the equality).  RH NOT claimed.  See docs/952, 953, 955.