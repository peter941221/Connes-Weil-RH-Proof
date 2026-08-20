import ConnesWeilRH.Source.CC20Concrete.PositiveTrace

/-!
# C1CrossingCommonCarrierTransport - unitary transport of ordinary traces

Stage 1b core lemma (1038).  Conjugating an operator by a basis-matching
inner-preserving continuous linear map transports the ordinary trace along
the matching Hilbert bases exactly.  This is the shared core of the four
producer-obligation fields of `CrossingCommonCarrierData`: once the carrier
is modeled by one of the owner's interval spaces and the crossing pair
operators are conjugated through the basis-matching unitary, both trace
equalities reduce to this lemma termwise.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CrossingCommonCarrierTransport

open CC20Concrete.PositiveTrace
open scoped InnerProductSpace

noncomputable section

/-- An inner-preserving continuous linear map that matches two Hilbert bases
transports the ordinary trace of any conjugated operator exactly. -/
theorem ordinaryTraceAlong_conj_of_basisMatching
    {ι H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Countable ι]
    (e : HilbertBasis ι ℂ H) (f : HilbertBasis ι ℂ K)
    (U : H →L[ℂ] K)
    (hU_basis : ∀ i, U (e i) = f i)
    (T : K →L[ℂ] K) :
    ordinaryTraceAlong e ((U.adjoint.comp T).comp U) =
      ordinaryTraceAlong f T := by
  have hterm : ∀ i, ⟪e i, ((U.adjoint.comp T).comp U) (e i)⟫_ℂ =
      ⟪f i, T (f i)⟫_ℂ := by
    intro i
    have hshift : ⟪e i, ((U.adjoint.comp T).comp U) (e i)⟫_ℂ =
        ⟪U (e i), T (U (e i))⟫_ℂ := by
      simp only [ContinuousLinearMap.comp_apply]
      exact ContinuousLinearMap.adjoint_inner_right U (e i) (T (U (e i)))
    rw [hshift, hU_basis i]
  unfold ordinaryTraceAlong
  exact tsum_congr hterm

/-- The basis-matching conjugator between two Hilbert bases: compose the
representing `ℓ²` isometries.  This is the unitary that instantiates the
transport lemma above for the common-carrier producer. -/
noncomputable def basisMatchingCLM
    {ι H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : HilbertBasis ι ℂ H) (f : HilbertBasis ι ℂ K) : H →L[ℂ] K :=
  (e.repr.trans f.repr.symm).toContinuousLinearEquiv.toContinuousLinearMap

theorem basisMatchingCLM_apply
    {ι H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : HilbertBasis ι ℂ H) (f : HilbertBasis ι ℂ K) (x : H) :
    basisMatchingCLM e f x = f.repr.symm (e.repr x) := rfl

theorem basisMatchingCLM_inner
    {ι H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : HilbertBasis ι ℂ H) (f : HilbertBasis ι ℂ K) (x y : H) :
    ⟪basisMatchingCLM e f x, basisMatchingCLM e f y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [basisMatchingCLM_apply, basisMatchingCLM_apply]
  exact (LinearIsometry.inner_map_map (f.repr.symm.toLinearIsometry) _ _).trans
    (LinearIsometry.inner_map_map (e.repr.toLinearIsometry) _ _)

theorem basisMatchingCLM_basis
    {ι H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [DecidableEq ι]
    (e : HilbertBasis ι ℂ H) (f : HilbertBasis ι ℂ K) (i : ι) :
    basisMatchingCLM e f (e i) = f i := by
  rw [basisMatchingCLM_apply, HilbertBasis.repr_self e i,
    HilbertBasis.repr_symm_single f i]

/-- The linear-isometry-equiv underlying `basisMatchingCLM`. -/
def basisMatchingLIE
    {ι H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : HilbertBasis ι ℂ H) (f : HilbertBasis ι ℂ K) : H ≃ₗᵢ[ℂ] K :=
  e.repr.trans f.repr.symm

theorem coe_basisMatchingCLM
    {ι H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : HilbertBasis ι ℂ H) (f : HilbertBasis ι ℂ K) :
    basisMatchingCLM e f = (basisMatchingLIE e f : H →L[ℂ] K) := rfl

theorem basisMatchingLIE_basis
    {ι H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [DecidableEq ι]
    (e : HilbertBasis ι ℂ H) (f : HilbertBasis ι ℂ K) (i : ι) :
    (basisMatchingLIE e f : H →L[ℂ] K) (e i) = f i :=
  basisMatchingCLM_basis e f i

/-- Symm of the basis-matching equiv is the matching in the other direction. -/
theorem basisMatchingLIE_symm
    {ι H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : HilbertBasis ι ℂ H) (f : HilbertBasis ι ℂ K) :
    (basisMatchingLIE e f).symm = basisMatchingLIE f e := by
  simp [basisMatchingLIE, LinearIsometryEquiv.symm_trans]

/-- The basis-matching unitary's adjoint is the matching in the other
direction. -/
theorem basisMatchingCLM_adjoint
    {ι H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : HilbertBasis ι ℂ H) (f : HilbertBasis ι ℂ K) :
    (basisMatchingCLM e f).adjoint = basisMatchingCLM f e := by
  rw [coe_basisMatchingCLM, LinearIsometryEquiv.adjoint_eq_symm,
    coe_basisMatchingCLM, ← basisMatchingLIE_symm]
  simp

/-- The basis-matching unitary is an isometry. -/
theorem basisMatchingCLM_norm
    {ι H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : HilbertBasis ι ℂ H) (f : HilbertBasis ι ℂ K) (x : H) :
    ‖basisMatchingCLM e f x‖ = ‖x‖ :=
  LinearIsometry.norm_map (basisMatchingLIE e f).toLinearIsometry x

/-- Matching one way and then back is the identity. -/
theorem basisMatchingCLM_cancel
    {ι H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : HilbertBasis ι ℂ H) (f : HilbertBasis ι ℂ K) (x : H) :
    basisMatchingCLM f e (basisMatchingCLM e f x) = x := by
  simp only [basisMatchingCLM_apply, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.symm_apply_apply]


/-- Conjugated pair trace-product algebra, abstract form: transporting both
pair legs through `u` and back through `w'` leaves the trace product in the
exact form consumed by the trace-transport lemma.  `w'` is the right inverse
carrier of `w` with `w'† = w` (instantiated by a linear isometry equiv at the
consumer). -/
theorem conjPair_traceProduct
    {H K G S : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
    (u : H →L[ℂ] K) (w : G →L[ℂ] S) (w' : S →L[ℂ] G) (L R : K →L[ℂ] S)
    (hw' : w'.adjoint = w) (hw : ∀ z : S, w (w' z) = z) :
    ((w'.comp L).comp u).adjoint.comp ((w'.comp R).comp u) =
      (u.adjoint.comp (L.adjoint.comp R)).comp u := by
  ext x
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    hw']
  simp [hw]

end
end C1CrossingCommonCarrierTransport
end Source
end ConnesWeilRH
