# 858 - Mellin conjugation and critical-line reality for the route sign (axiom-clean)

Date: 2026-08-08 . Status: Dev lemma family; build + axiom verified; no RH claim.

Follows 857/857b.  857 pinned the half-density sign slot to
`Re[(M g i/2)^4] + Re[(M g -i/2)^4]` and noted the missing ingredient was a
"bidirectional Mellin conjugation / reality" that the repo's star did not supply.
This round supplies it: the real-base power conjugation, the Mellin-lift
conjugation, and the critical-line reality corollary for real-valued tests.
All of it is Lean-proven and axiom-clean; none of it decides the final sign.

## Results (build + axiom clean)

New `Dev/MellinConjugation.lean` (extends 858):

    conj_cpow_of_real (c : R) (s : C) (hc : arg (c:C) != pi) :
        conj (c^s) = c^(conj s)
    conj_cpow_exp (t : R) (s : C) :
        conj ((Real.exp t : C)^s) = (Real.exp t : C)^(conj s)
    conj_smul_cpow_exp (u : R) (s z : C) :
        conj ((Real.exp u : C)^s * z) = (Real.exp u : C)^(conj s) * conj z
    mellinLift_conj (f : R -> C) (s : C) :
        conj (MellinLift f s) = MellinLift (conj o f) (conj s)
    MellinLift (- (i/2)) = conj (MellinLift (i/2))     -- for real-valued f

The route-relevant Mellin-lift conjugation:
`conj (MellinLift f s) = MellinLift (conj o f) (conj s)`.

- lake build ConnesWeilRH.Dev.MellinConjugation: 2955 jobs success (leaf ~30s).
- #print axioms of every lemma here = [propext, Classical.choice, Quot.sound] (no sorryAx).

## Proof sketch

`mellinLift` unfolds through `mellin_comp_log_eq_exp_integral` (`MellinConvolutionIdentity`) to
`integral u, (e^u)^s . f u`.  Push the conjugate under the integral with
`MeasureTheory.integral_conj`, conjugate the weight factor with `conj_cpow_exp`
(it is conjugation of a positive-real base power; nonneg so `arg = 0 != pi`),
and use `map_mul`/`smul_eq_mul` for the complex scalar mul; done.

At `s = i/2`: `conj (i/2) = -i/2` (conj_I_half), so for a real-valued `f`
(`conj o f = f`) we get the critical-line reality lemma
`MellinLift f (-i/2) = conj (MellinLift f (i/2))`.

## What this does and does not decide (the sign slot)

Let `w = (M g (i/2))`.  With `g` real-valued, the conjugate-symmetry gives
`M g (-i/2) = conj (M g (i/2))`, hence `(M g (-i/2))^4 = conj(w^4)`.  The route
pole sum becomes:

    Re[M(g)(+i/2)^4] + Re[M(g)(-i/2)^4] = Re[w^4] + Re[conj(w^4)] = 2 Re[w^4].

So the sign slot `weilLocalSum(starConvol g) <= 0` (which is `polePairing >= 0`)
collapses to the single real statement:

    Re[(M g (1/2 i))^4] >= 0        (for real-valued g)

This is the sharpest honest frontier for this lane.  Conjugation/reality does
NOT imply `Re(w^4) >= 0`: a complex fourth power carries an arbitrary phase, so
`Re(w^4) >= 0` is an independent analytic condition on the test's Mellin at the
critical point (e.g. a reflection/positivity property of the test's spectrum, or
a phase bound on `M g (i/2)`), not something any star/conjugation plumbing
supplies.  If the concrete test is NOT real-valued, even the reduction to
`conj(MellinLift ...)` needs re-checking.

## Honest table after 858

| item | state |
| faithful square = square (857) | CLOSED (axiom-clean) |
| double square = fourth power (857b) | CLOSED (axiom-clean) |
| real-base power conjugation (858) | CLOSED (axiom-clean) |
| Mellin-lift conjugation + critical-line reality (this round) | CLOSED (axiom-clean) |
| route sign slot weil(s) <= 0 | OPEN; reduced to Re(w^4) >= 0 (analytic input) |
| generic-lambda prolate HS (only 3U premise) | OPEN (856: no rescale bridge) |
| per-F rows (finiteSetDisjoint / riemannZeta(1/2)!=0) | CLOSED (849, Dirichlet eta) |
| RH | NOT proven |

No RH is claimed.  These lemmas are the conjugation/reality half of the
critical-line direction; the numerical-pusitivity half (Re(w^4) >= 0) is the
remaining genuine input.

