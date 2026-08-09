# 931 — Piece-1 exact algebra: the whole infinite Gate is one operator identity in (B,N,J)

Date: 2026-08-10. Type: analytic reformulation (self-created lever). No `sorry`, no new
`axiom`. RH NOT claimed. This memo does NOT prove Piece 1; it removes the opacity of the
projector and leaves exactly one open operator identity whose objects are all directly
defined (no unreachable intersection inside the statement).

## 0. Objects (names source-verified)

    S  = sourceSoninCarrier lambda
    F  = finiteSCarrier
    J  = sourceInclusion lambda : S → F        isometric: J†J = 1_S        (GramResponse:46)
    H  = finiteEulerAmbientGram = T†T  (F → F, T = finiteEulerTransportOperator)
    G  = finiteEulerGram = J†H J   (S → S, self-adjoint, positive, invertible)
    B  = sourceBandProjection lambda (F → F, star projection)
    N  = normalizedFiniteEulerInverse (S → S)
    D  = finiteEulerMetricCeopd = H ∘ J ∘ G⁻¹          (metric oeop)
    C  = sourceActualBandForwardCoframe = B ∘ N⁻¹ ∘ J   (forward oeop)
    L  = sourceActualBandCombinedCoframeLeakage = C + (D − J)    (off-Sonin)

Gate-3U infinite target: L = 0 on every (non-empty) family, i.e.

    (∗)   B ∘ N⁻¹ ∘ J  +  (H ∘ J ∘ G⁻¹)  =  J        (equality in S →_L F)

## 1. What is already forced (in-repo, axiom-clean)

The objects D, P and the biorthonormality satisfy:

    J†J = 1_S            (GramResponse:46)
    J∘J† = P             (Sonin projector, GramResponse:57)
    J†∘D = 1_S           (biorthon., CoframeResponse:52)
    P∘D = J              (Sonin compression, CoframeResponse:85)
    P∘L = 0,  J†∘L = 0   (CombinedCoframeGuard, fully off-Sonin)

Hence D is entirely determined by J, H, G. Every term but the forward morphism is pinned.

## 2. Necessary condition (clean, derived from (∗))

Apply J† to (∗).  J†(H∘J∘G⁻¹) = (J†HJ)∘G⁻¹ = G∘G⁻¹ = 1_S,  and J†J = 1_S, so:

    J†∘(B∘N⁻¹∘J) = 0          (the forward forward coframe is orthogonal to the Sonin J)

is a NECESSARY condition for the Gate (it is L=0 projected on the J dual).  It is not
sufficient (L = C + D − J is an operator equality, stronger than its J†-projection).

## 3. The exact open lemma (no projector in the statement)

    Gate31_bottom :
      ∀ (lambda family), B(lambda)∘(N⁻¹ family)∘J lambda =
        J lambda − H family∘J lambda∘(G lambda)⁻¹

Equivalently (multiplying on the right by G, using J†J=1):

    B∘N⁻¹∘J∘G  +  H∘J  =  J∘G          (fornote: no P appears)

No in-repo theorem gives either. The metric part is `H∘J∘G⁻¹` — fully solved; the only free
object is the band-transport composition `B∘N⁻¹∘J`.

## 4. Why no finite-grid numeric can decide (guard)

L and the objects act on S, the exact infinite Sonin space. The band projector B[λ] and the
transport on S are infinite-dimensional; any finite-dim band model of S is near-parallel to
the Sonin directions (AGENTS 818/819), so a numeric zero would resolve the grid, not the
operator. This is why the clean operator identity must hold as an exact theorem, no
numeric substitute.

## 5. Takeaway

Piece 1 = one operator identity B∘N⁻¹∘J + H∘J∘G⁻¹ = J.  Everything else (J†ortho, P-ortho,
Gram-inv, metric coframes) is already in Library. Honest short statement: the Gate is
exactly "the band-then-transport inverse applied to the Sonin inclusion reproduces the
inclusion minus the metric correction"; this is genuinely new analysis, not a Lean seam.
RH not claimed.


## 6. STATUS UPDATE (2026-08-10) - necessary condition PROVEN

The necessary condition of section 2 (Jdagger o M = 0) is now a byte-verified Lean lemma:

    ConnesWeilRH/Dev/CCM24JdaggerOrthogonality.lean
    inclusionAdjoint_comp_band_eq_zero   |  dagger_comp_forwardBandCoframe_eq_zero
    axioms [propext, Classical.choice, Quot.sound], 0 sorry (docs/932)

The sufficient operator equality (the full Gate) remains OPEN. RH not claimed.