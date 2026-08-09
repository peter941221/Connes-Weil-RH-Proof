# 932 - J-dual of the forward band-coframe vanishes: lemma PROVEN (byte-verified)

Date: 2026-08-10. Type: Lean result (self-created lever). No sorry, no new axiom.
RH NOT claimed.

## 0. The previously-open necessary condition, now proved

docs/931 derived that `L = 0` implies (by applying J^dag) the NECESSARY condition

    J^dagger o M = 0,   M := B o N^-1 o J

and flagged it "open". This round closed it inside Lean with two Leibniz-algebra facts
already in the library:

    J^dagger = J^dagger o P                      (sourceInclusionAdjoint_comp_sourceProjection)
    P o B = 0                                    (sourceSoninProjection_comp_sourceBandProjection_eq_zero)

=>  J^dagger o B = (J^dagger o P) o B = J^dagger o (P o B) = 0
=>  J^dagger o (B o N^-1 o J) = (J^dagger o B) o (N^-1 o J) = 0

## 1. The module (source of truth: Windows repo)

    ConnesWeilRH/Dev/CCM24JdaggerOrthogonality.lean

Theorems (byte-verified 2026-08-10, WSL build on a warm cwr-main mirror):

    inclusionAdjoint_comp_band_eq_zero :
        (sourceInclusion lambda)^dag oL sourceBandProjection lambda = 0
    dagger_comp_forwardBandCoframe_eq_zero :
        (sourceInclusion lambda)^dag o sourceActualBandForwardCoframe lambda family = 0

`lake env lean` EXIT=0;  `lake build` green (3275 jobs);
`#print axioms` = [propext, Classical.choice, Quot.sound], 0 sorry. Probe copy deleted
from the mirror afterward (AGENTS 8).

## 2. What this does and does not do

DOES: proves the necessary (J-dual) condition, and explains why every finite-grid probe
of the outer channel is FLAT (its linear content vanishes by algebra; the info is all in
the operator norm of the off-J part).

DOES NOT: close the infinite Gate. The Gate is the operator equality L = 0, strictly
stronger than its J-dual. No theorem gives L = 0; the remaining content is the
band-transport operator `B o N^-1` on the Sonin carrier, which is still open and
needs new analysis (not Lean assembly).

## 3. Status

Gate-3U infinite carrier: OPEN. Necessary condition: CLOSED (this module).
RH NOT claimed.


## 3b. Sonin side also cleared (same session)

The Sonin projection annihilates the forward band coframe too (new lemma, verified):

    sonin_comp_forwardBandCoframe_eq_zero :
        sourceSoninProjection lambda oL sourceActualBandForwardCoframe lambda family = 0

Axioms [pe,CC,Qs], 0 sorry. Proof: P o (B o N^-1 o J) = (P o B) o (N^-1 o J) = 0 (sourceSoninProjection_comp_sourceBandProjection_eq_zero).
Together with section 1 this clears BOTH projection-adjoint directions (J^dagger and P):
the residual Gate information lives only in the (E-P) projection norm of M. RH not claimed.
