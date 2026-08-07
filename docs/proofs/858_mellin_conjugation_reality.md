# 858 - Mellin conjugation and critical-line reality for the route sign (axiom-clean)

Date: 2026-08-08 . Status: Dev lemma family; build + axiom verified; no RH claim.

Follows 857/857b.  857 pinned the half-density sign slot to
`Re[(M g i/2)^4] + Re[(M g -i/2)^4]` and noted the missing ingredient was a
"bidirectional Mellin conjugation / reality" that the repo's star did not supply.
This round supplies it: the real-base power conjugation, the Mellin-lift
conjugation, the critical-line reality corollary, and the final single-real
pole-sum reduction. All of it is Lean-proven and axiom-clean; none of it
decides the final sign.

## Results (build + axiom clean)

New `Dev/MellinConjugation.lean` (858) and `Dev/MellinSignAssembly.lean (858c):

    conj_cpow_of_real (c : R) (s : C) (hc : arg (c:C) != pi) :
        conj (c^s) = c^(conj s)
    conj_cpow_exp (t : R) (s : C) :
        conj ((Real.exp t : C)^s) = (Real.exp t : C)^(conj s)
    conj_smul_cpow_exp (u : R) (s z : C) :
        conj ((Real.exp u : C)^s * z) = (Real.exp u : C)^(conj s) * conj z
    mellinLift_conj (f : R -> C) (s : C) :
        conj (MellinLift f s) = MellinLift (conj o f) (conj s)
    conj_I_half : conj (i/2) = -i/2
    mellinLift_real_involution (g) (hg : conj o g = g) :
        MellinLift g (-i/2) = conj (MellinLift g (i/2))
    pow4_conj (z) : conj (z^4) = (conj z)^4
    halfDensity_poleSum_top  : pole-sum top term = Re[w^4]
    halfDensity_poleSum_pow4_real (g) (hg) : pole sum = 2 * Re[w^4]

The core over the log Mellin integral:
`conj (MellinLift f s) = MellinLift (conj o f) (conj s)` by pushing
`integral_conj` under the integral and conjugating the real-base power with
`conj_cpow_exp`.

- lake build ConnesWeilRH.Dev.MellinSignAssembly: 2957 jobs success (leaf ~30s).
- #print axioms of every lemma here = [propext, Classical.choice, Quot.sound] (no sorryAx).

## What this does and does not decide (the sign slot)

Let `w = M g (i/2)`.  With `g` real-valued, the conjugate symmetry gives
`M(g -i/2) = conj (M(g i/2))`, hence `M(g -i/2)^4 = conj(w^4)` (pow4_conj).  The
route half-density pole sum (the thing the sign target needs to be >=0) becomes:

    Re[M(g)(+i/2)^4] + Re[M(g)(-i/2)^4] = Re[w^4] + Re[conj(w^4)] = 2 Re[w^4].

`halfDensity_poleSum_pow4_real` is the Lean statement of exactly that.  So the
whole open sign slot reduces to the single real statement:

    Re[(M g i/2)^4] >= 0        (for real-valued g)

Conjugation/reality does NOT imply `Re(w^4) >= 0`: a complex fourth power carries
an arbitrary phase, so this is an independent analytic condition on the test's
Mellin at the critical point.  If the concrete test is NOT real-valued, even the
reduction to `conj(M(g i/2))` needs re-checking.

## Honest table after 858c

| item | state |
| faithful square = square (857) | CLOSED (axiom-clean) |
| double square = fourth power (857b) | CLOSED (axiom-clean) |
| real-base power conjugation (858) | CLOSED (axiom-clean) |
| Mellin-lift conjugation + critical-line reality (858) | CLOSED (axiom-clean) |
| pole sum = 2*Re[w^4] reduction (858c) | CLOSED (axiom-clean) |
| route sign slot weil(s) <= 0 | OPEN; = this reduction + Re[w^4] >= 0 (analytic) |
| generic-lambda prolate HS (only 3U premise) | OPEN (856: no rescale bridge) |
| per-F rows (finiteSetDisjoint / riemannZeta(1/2)!=0) | CLOSED (849, Dirichlet eta) |
| RH | NOT proven |

No RH is claimed.  These lemmas are the conjugation/reality half of the
critical-line direction; the remaining genuine-positivity half is exactly
`Re[(M g i/2)^4] >= 0`.
