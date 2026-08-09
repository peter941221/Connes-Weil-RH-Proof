# 02 - Roadmap to RH: the three walls, what is proven, what is open (2026-08-10)

RH is NOT proved. No item here claims RH. This file records the frontier after the NEW
verified result of this round (the J-dual orthogonality is proven), which narrows Wall 1.

## Wall 1 - infinite-carrier Gate 3U (the active analytic bottom)

Real objects:  J = sourceInclusion,  B = sourceBandProjection,
N = normalizedFiniteEulerInverse,  H = finiteEulerAmbientGram,
G = finiteEulerGram = J^dag H J,  D = finiteEulerMetricCoframe,
C = sourceActualBandForwardCoframe = B o N^-1 o J,
L = sourceActualBandCombinedCoframeLeakage = C + (D - J).

The Gate is ONE operator identity (docs/931):

    B o N^-1 o J  +  H o J o G^-1  =  J            (equality in S ->L F)

Progress this round (NEW, PROVEN, byte-verified):

    (sourceInclusion lambda)^dag oL sourceBandProjection lambda = 0
    (sourceInclusion lambda)^dag o sourceActualBandForwardCoframe lambda family = 0
    sonin_comp_forwardBandCoframe_eq_zero :
        sourceSoninProjection lambda oL sourceActualBandForwardCoframe lambda family = 0
    axioms (all three) = [propext, Classical.choice, Quot.sound]; 0 sorry
    file = ConnesWeilRH/Dev/CCM24JdaggerOrthogonality.lean

Interpretation: the linear (J- and P-dual) content of the forward coframe vanishes by pure
Leibniz algebra, so the Gate information lives only in the operator norm of the off-J
component. This is why no finite-grid probe can ever decide it (AGENT 818/819).

Still OPEN: the (sufficient) full operator equality, not just the J-dual. No theorem
gives L = 0; the deciding factor is the band-transport operator `B o N^-1` coupled to
the Sonin generator, which needs genuine analysis rather than Lean assembly.

## Wall 2 - finite-S sign / source-model carrier

The current concrete skeleton model is inconsistent: `convolutionStar = f + g` is not a
Mellin convolution (the square law fails, giving 2=1 in CC20YoshidaConstruction:2727),
and `exactSupport` forces product zero. The healthy carrier is CompactLogTest / CompactRootHalfLinePair (HS).
Re-typing the source core to that carrier is a bounded engineering seam, but it does NOT
close Walls 1 or 3. No self-created lever changes this judgment.

## Wall 3 - arch phase / Gamma bounds (analytic refinements)

Many leaf gates are CLOSED and axiom-clean: |arg Gamma(1+i/2)| <= pi/8 via
PhaseGateSandwich, arctan certificates (ArctanCert), the S-series sandwich (SSeries), all
with axioms [pe, CC, Qs]. Remaining open: the Gamma magnitude identity / Stirling
residual bound, which is a real-analysis leaf independent of Walls 1-2.

## Recommended order

1. Wall 1: the operator part `(E - P) o (C + D - J)` for one explicit test or its
   refutation. This is genuinely open and needs new analysis.
2. Wall 2 carrier re-type: bounded engineering; it does not close Wall 1.
3. Wall 3 Gamma residual: a leaf.

Honest statement: this round removed a necessary-condition step by proof, but the
sufficient equality is not closed. No zero-sorry path to RH is currently known.
RH is not claimed.

## 0a. Build-verification record (2026-08-10)

All committed Dev leaves were re-built green at current HEAD in a fresh ext4
mirror (seed `.lake` from the warm cwr-main cache, build dir recreated):
- `CCM24JdaggerOrthogonality` (3275 jobs; `#print axioms` = [propext, Classical.choice, Quot.sound], 0 sorry)
- `EBandFactorSharpProbe` (3220 jobs)
- `Gate3UDichotomyProbe` (3418 jobs)
- `L657DiagProbe` (2950 jobs)
- `L657DiagnosticProbe` (2948 jobs, after `(empty : Finset Nat)` -> `(∅ : Finset Nat)`)

Wall 1 re-grounding: the endpoint contraction `norm_le_one_iff` and the operator
Gram form `End†∘End = id + L†∘L` (EndpointContractionGuard:298), together with
the pointwise Pythagoras `‖End u‖² = ‖u‖² + ‖L u‖²`, do NOT force the sufficient
identity `L = 0`. Closure still requires the signed cancellation
`(E−P)∘(Forward + PhysicalLeakage) = 0` — the open analytic Piece-1.
