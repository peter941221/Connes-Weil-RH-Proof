# 857 - Faithful half-density square: Mellin of the genuine convolution square is a SQUARE (axiom-clean)

Date: 2026-08-08 . Status: Dev lemma; build + axiom verified, no RH claim.

Follows 852-856.  The additive CC20 model forces M(conv^2 g)(s) = 2 * Mellin g s (the
2 = 1 pathology, CC20YoshidaConstruction:2727) which manufactures a fake negative Weil
pairing - 850 called it a model artifact.  This round proves the faithful replacement on
the log-coordinate Mellin-product carrier: the genuine convolution really multiplies under
Mellin, so the half-density square is a pure SQUARE, not a double.

## Result (build + axiom clean)

New Dev/MellinHalfDensitySquare.lean:

    halfDensitySquareMellin_eq_mellin_sq (g : R -> C) (s : C)
        (hF : Integrable (logWeight s g)) :
        Mellin(conv g g)(s) = (Mellin g)(s)^2

Proof is rw [MellinProductCarrier.mellinConvolutionProductLaw (f:=g)(g:=g) s hF hF] then ring.
The half-density square Mellin is the SQUARE of the test Mellin, using the already
axiom-clean product law (852/853).

- lake build ConnesWeilRH.Dev.MellinHalfDensitySquare: 2955 jobs success (leaf ~30 s).
- #print axioms of the theorem = [propext, Classical.choice, Quot.sound], no sorryAx.

## Why this is the correct block, and what it does NOT decide

The route endpoint / half-density sign slot needs weilLocalSum(starConvolution g) <= 0, where
the pairing reads M(convolutionSquare g)(+/-i/2).  On the faithful carrier the square is
conv g g, so:

    M(conv g g)(+i/2) = (M g (+i/2))^2 ; M(conv g g)(-i/2) = (M g (-i/2))^2

So the sign question reduces to the sum of two complex SQUARES at +/-i/2.  A complex square
carries any phase at a general g; it does NOT by itself force <= 0 or >= 0.  What 857
certifies and records:

- the additive double M = 2Mg is NOT the correct model law; the square Mg^2 is correct and
  now Lean-proven;
- any head sign decision must analyze Re[(M g (i/2))^2] + Re[(M g (-i/2))^2] (plus the
  star / conjugation reflection) - genuine analysis, not a reasserted-2e1 pathology; that model law is false (2 = 1).

## Honest table after 857

| item | state |
| generic-lambda prolate HS (only 3U premise) | OPEN; wall confirmed 856 (no rescaling bridge) |
| faithful half-density square Mellin = square | CLOSED (this module, axiom-clean) |
| route sign slot weil <= 0 | OPEN; reduced to Re squares at +/-i/2 (real analysis) |
| per-F rows (tripleVanishingMatchesMellin / finiteSetDisjoint) | OPEN arithmetic (848) |
| RH | NOT proven |

No RH is claimed.  This module removes the additive-multiplicative-model bug at the level it
enters the sign, without pretending the sign is decided.

## 857b - the double square is the FOURTH power (route pole-sum shape, axiom-clean)

Follow-up to the square lemma.  The route sign slot reads the DOUBLE convolution
square convolutionSquare (convolutionSquare g).  On the faithful carrier that is
conv (conv g g) (conv g g), and the product law applied twice gives:

    M(conv (conv g g) (conv g g))(s) = (M g)(s)^4

New lemma Dev/MellinHalfDensitySquare.lean::halfDensityDoubleSquareMellin_eq_mellin_pow4,
proved by two rw of the product law (on conv g g with hFF, and the inner square with hF)
then ring.  lake build 2955 jobs pass; #print axioms = [propext, Classical.choice, Quot.sound]
for both 857 lemmas.

So the endpoint / half-density sign the route needs reduces to:

    Re[M(g)(i/2)^4] + Re[M(g)(-i/2)^4]

a fourth-power complex sum.  A complex 4th power still carries a phase, so this does NOT
by itself force the sign; it certifies the correct multiplicative shape (the additive
2*M g, and its 4-fold square 16*Mg^2, are NOT the model).  The remaining sign step is a
genuine analytic condition on g (a bidirectional Mellin conjugation / reality that the
repo's star does not currently provide) - no Lean plumbing supplies it.
