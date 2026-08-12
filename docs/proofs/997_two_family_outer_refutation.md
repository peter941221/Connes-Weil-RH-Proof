# 997 - Concrete {2}-family refutation of the infinite Gate: Outer channel, numeric-solid / formal-open

Date: 2026-08-11. Status: precise target + numeric-conclusive negative; formal Lean lower bound OPEN.
Scope: refute the canonical infinite-carrier Gate for a NON-EMPTY family via the OUTER channel.
It does NOT claim the finite-band Route-A gate is broken, and is NOT a RH claim. RH NOT claimed.

## 1. Disambiguation that unlocks the refutable channel (repo-verified defs)

From CCM24FiniteSProjectionTrace.lean + docs/815:
- R    = radialSupportProjection lambda   (log-radial support closure, COMPUTABLE star-proj)
- R0   = sourceSoninProjection lambda     (archimedean Sonin closure, the "unreachable exact Sonin")
- sourceBandProjection = R - R0 ;  D = finiteEulerMetricCoframe = E_gram o J o G^-1
- Channel split (docs/815, orthogonal): Gate(Proof-717)
      <=> OuterChannel + BandChannel = 0
      <=> OuterChannel = 0  AND  BandChannel = 0        (they are ORTHOGONAL subspaces)
   OuterChannel = (I - R) o D
   BandChannel  = sourceBandProjection o normalizedInverse o J  +  (R - R0) o D

The important fact: the OUTER channel (I - R) o D uses only R (computable) and D = E o J o G^-1,
NOT the unreachable R0.  So the refutation target is away from the numeric dead-end.

## 1. Refute the Gate for a non-empty family by proving (I - R) o D != 0

Because the channels are orthogonal, it suffices for a REFUTATION to show, for ONE
non-empty family family0 (concrete: visiblePrimes = [2]) at some lambda:

    || (I - R) o D ||  >  0            (even one nonzero image vector)

i.e. D has part outside the radial band R. Then OuterChannel != 0, so Gate fails for
that family.  Docs 815/884 already measure this:

- docs/884 (transport-Sonin frame): |(I-R) o D| ~ 0.61-0.62, FLAT across logla in [-2,+2],
  floor ~0.369, resolution n:200..6000 stable; never approaches 0.
  Regression anchor n=600 L=8: 0.6242 (matches 824).

So the OUTER-channel refutation of non-empty families is NUMERICALLY CONFIRMED and
scale-robust. This is exactly the "case-bound negative" from 884.

## 3. The remaining FORMAL open step (honest)

884 is finite-grid onwards, NOT a proof, and NOT a Lean theorem that
"forall lambda, ||(I-R) o D|| > c > 0".   A formal counterexample needs a RIGOROUS
positive lower bound on ||(I-R)D|| on a concrete {2}-family carrier, computed or bounded
for at least one cited vector u. The operator D = E_gram o J o G^-1 is concrete, so this
is a feasible-but-substantial analytic item (needs the exact radial-outside-band action of
D on the {2} carrier, beyond a finite grid).

## 5. Formal obligation (naming the family, exact object)

Ideal Lean statement (a future `Dev` leaf, NOT committed here - mirror dirty/no build):

    theorem gate_outer_nonzero_for_two
        {lambda}  : "|| (I - (radialSupportProjection lambda)) oL
                        (finiteEulerMetricCoframe lambda family2) ||" != (0 : Real) := ...

where family2 : is the one-prime family (visiblePrimes = [2]); numeric puts it ~ 0.61.

Closing this converts the 884 case-bound negative into a formal route-refutation for
non-empty families.  It does NOT need R0, does NOT need the Sonon intersection.

## 6. Why this is the right single counterexample step

- Orthogonality (docs/815) collapses Gate to each channel =0, so the outer channel's
  non-vanishing is SUFFICIENT (and independent).
- Outer uses only computable R, avoiding the numeric dead-end that killed inner/Band
  analyses (818/819).
- Numeric (884) already says ~0.61, so this is "lift a numeric to a formal bound", not
  a discovery-looking hazard.

RH not claimed.

Note: canonical deliverable = Route-A finite-band (closed); this is about the infinite-carrier
Gate it replaced, kept here as the route's archival verdict.
