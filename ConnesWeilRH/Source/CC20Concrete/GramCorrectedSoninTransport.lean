import ConnesWeilRH.Source.CC20Concrete.InvertibleTransportSonin
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Gram-corrected transport of a closed Sonin space

For a bounded injective frame `A`, the orthogonal projection onto its range is
not an oblique similarity.  It is the Gram-corrected operator

`A (A† A)⁻¹ A†`.

For a continuous linear equivalence, restriction to a closed subspace gives an
explicit equivalence onto the transported closed subspace. Its Gram inverse is
therefore constructed as `E⁻¹ (E⁻¹)†`, without a stored inverse premise.
-/

namespace ConnesWeilRH
namespace CC20Concrete

open scoped InnerProduct

noncomputable local instance closedSubmoduleCarrierCompleteSpace
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (S : ClosedSubmodule 𝕜 E) : CompleteSpace S.toSubmodule :=
  S.isClosed.completeSpace_coe

section AbstractFrame

variable {𝕜 H K : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- The Gram-corrected range projection associated to a frame `A`. -/
noncomputable def gramCorrectedProjection
    (A : H →L[𝕜] K) (gramInv : H →L[𝕜] H) : K →L[𝕜] K :=
  A ∘L gramInv ∘L ContinuousLinearMap.adjoint A

theorem gramCorrectedProjection_isIdempotentElem
    (A : H →L[𝕜] K) (gramInv : H →L[𝕜] H)
    (hgram : gramInv ∘L ContinuousLinearMap.adjoint A ∘L A =
      ContinuousLinearMap.id 𝕜 H) :
    IsIdempotentElem (gramCorrectedProjection A gramInv) := by
  change gramCorrectedProjection A gramInv *
      gramCorrectedProjection A gramInv = gramCorrectedProjection A gramInv
  simp only [ContinuousLinearMap.mul_def]
  ext x
  let z : H := gramInv (ContinuousLinearMap.adjoint A x)
  change A (gramInv (ContinuousLinearMap.adjoint A (A z))) = A z
  have hz := congrArg (fun F : H →L[𝕜] H => F z) hgram
  apply congrArg A
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using hz

theorem gramCorrectedProjection_isSelfAdjoint
    (A : H →L[𝕜] K) (gramInv : H →L[𝕜] H)
    (hself : IsSelfAdjoint gramInv) :
    IsSelfAdjoint (gramCorrectedProjection A gramInv) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp only [gramCorrectedProjection, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hself.adjoint_eq]
  exact ContinuousLinearMap.comp_assoc _ _ _

theorem gramCorrectedProjection_isStarProjection
    (A : H →L[𝕜] K) (gramInv : H →L[𝕜] H)
    (hgram : gramInv ∘L ContinuousLinearMap.adjoint A ∘L A =
      ContinuousLinearMap.id 𝕜 H)
    (hself : IsSelfAdjoint gramInv) :
    IsStarProjection (gramCorrectedProjection A gramInv) :=
  ⟨gramCorrectedProjection_isIdempotentElem A gramInv hgram,
    gramCorrectedProjection_isSelfAdjoint A gramInv hself⟩

theorem gramCorrectedProjection_range
    (A : H →L[𝕜] K) (gramInv : H →L[𝕜] H)
    (hgram : gramInv ∘L ContinuousLinearMap.adjoint A ∘L A =
      ContinuousLinearMap.id 𝕜 H) :
    (gramCorrectedProjection A gramInv).range = A.range := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨gramInv (ContinuousLinearMap.adjoint A x), rfl⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨A x, ?_⟩
    change A (gramInv (ContinuousLinearMap.adjoint A (A x))) = A x
    have hx := congrArg (fun F : H →L[𝕜] H => F x) hgram
    apply congrArg A
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hx

end AbstractFrame

section RestrictedTransport

variable {𝕜 H K : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- The algebraic restriction of `T` to a closed source subspace, with
codomain equal to its exact transported closed subspace. -/
noncomputable def restrictedClosedTransportLinearEquiv
    (T : H ≃L[𝕜] K) (S : ClosedSubmodule 𝕜 H) :
    S.toSubmodule ≃ₗ[𝕜] (transportedClosedSubmodule T S).toSubmodule where
  toFun x :=
    ⟨T x, (ClosedSubmodule.mem_mapEquiv_iff' T S x).2 x.property⟩
  invFun y :=
    ⟨T.symm y, (ClosedSubmodule.mem_mapEquiv_iff T S y).1 y.property⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_add' x y := by
    ext
    simp
  map_smul' c x := by
    ext
    simp

/-- The restriction is a bounded invertible map onto the transported closed
subspace. Continuity is inherited from `T` and `T.symm`. -/
noncomputable def restrictedClosedTransportEquiv
    (T : H ≃L[𝕜] K) (S : ClosedSubmodule 𝕜 H) :
    S.toSubmodule ≃L[𝕜] (transportedClosedSubmodule T S).toSubmodule where
  __ := restrictedClosedTransportLinearEquiv T S
  continuous_toFun :=
    (T.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (T.symm.continuous.comp continuous_subtype_val).subtype_mk _

omit [CompleteSpace H] [CompleteSpace K] in
@[simp]
theorem restrictedClosedTransportEquiv_apply_coe
    (T : H ≃L[𝕜] K) (S : ClosedSubmodule 𝕜 H) (x : S.toSubmodule) :
    ((restrictedClosedTransportEquiv T S x :
      (transportedClosedSubmodule T S).toSubmodule) : K) = T x := by
  simp [restrictedClosedTransportEquiv,
    restrictedClosedTransportLinearEquiv]

omit [CompleteSpace H] [CompleteSpace K] in
@[simp]
theorem restrictedClosedTransportEquiv_symm_apply_coe
    (T : H ≃L[𝕜] K) (S : ClosedSubmodule 𝕜 H)
    (y : (transportedClosedSubmodule T S).toSubmodule) :
    ((restrictedClosedTransportEquiv T S).symm y : H) = T.symm y := by
  change ((restrictedClosedTransportLinearEquiv T S).symm y : H) = T.symm y
  rfl

/-- Restrict a bounded invertible transport to a closed source subspace. -/
noncomputable def restrictedClosedTransport
    (T : H ≃L[𝕜] K) (S : ClosedSubmodule 𝕜 H) :
    S.toSubmodule →L[𝕜] K :=
  T.toContinuousLinearMap ∘L S.toSubmodule.subtypeL

omit [CompleteSpace H] [CompleteSpace K] in
/-- The direct restriction agrees with inclusion after the exact restricted
continuous linear equivalence. -/
theorem restrictedClosedTransport_eq_subtype_comp_equiv
    (T : H ≃L[𝕜] K) (S : ClosedSubmodule 𝕜 H) :
    restrictedClosedTransport T S =
      (transportedClosedSubmodule T S).toSubmodule.subtypeL ∘L
        (restrictedClosedTransportEquiv T S).toContinuousLinearMap := by
  ext x
  change T x = ((restrictedClosedTransportEquiv T S x :
    (transportedClosedSubmodule T S).toSubmodule) : K)
  exact (restrictedClosedTransportEquiv_apply_coe T S x).symm

/-- The inverse of the exact restricted continuous linear equivalence. -/
noncomputable def restrictedClosedTransportInverse
    (T : H ≃L[𝕜] K) (S : ClosedSubmodule 𝕜 H) :
    (transportedClosedSubmodule T S).toSubmodule →L[𝕜] S.toSubmodule :=
  (restrictedClosedTransportEquiv T S).symm.toContinuousLinearMap

/-- The explicit inverse of the restricted Gram operator. If `E` is the
restricted transport equivalence, this is `E⁻¹ (E⁻¹)†`. -/
noncomputable def restrictedTransportGramInv
    (T : H ≃L[𝕜] K) (S : ClosedSubmodule 𝕜 H) :
    S.toSubmodule →L[𝕜] S.toSubmodule :=
  restrictedClosedTransportInverse T S ∘L
    ContinuousLinearMap.adjoint (𝕜 := 𝕜)
      (restrictedClosedTransportInverse T S)

theorem restrictedTransportGramInv_isSelfAdjoint
    (T : H ≃L[𝕜] K) (S : ClosedSubmodule 𝕜 H) :
    IsSelfAdjoint (restrictedTransportGramInv T S) := by
  exact (ContinuousLinearMap.isPositive_self_comp_adjoint
    (restrictedClosedTransportInverse T S)).isSelfAdjoint

theorem restrictedTransportGramInv_leftInverse
    (T : H ≃L[𝕜] K) (S : ClosedSubmodule 𝕜 H) :
    restrictedTransportGramInv T S ∘L
        ContinuousLinearMap.adjoint (𝕜 := 𝕜)
          (restrictedClosedTransport T S) ∘L
        restrictedClosedTransport T S =
      ContinuousLinearMap.id 𝕜 S.toSubmodule := by
  let E := (restrictedClosedTransportEquiv T S).toContinuousLinearMap
  let B := restrictedClosedTransportInverse T S
  let J := (transportedClosedSubmodule T S).toSubmodule.subtypeL
  have hEB : E ∘L B = ContinuousLinearMap.id 𝕜 _ := by
    ext x
    simp [E, B, restrictedClosedTransportInverse]
  have hBE : B ∘L E = ContinuousLinearMap.id 𝕜 _ := by
    ext x
    simp [E, B, restrictedClosedTransportInverse]
  have hBadjEadj : ContinuousLinearMap.adjoint (𝕜 := 𝕜) B ∘L
      ContinuousLinearMap.adjoint (𝕜 := 𝕜) E =
        ContinuousLinearMap.id 𝕜 _ := by
    have h := congrArg
      (fun A => ContinuousLinearMap.adjoint (𝕜 := 𝕜) A) hEB
    simpa only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_id] using h
  have hJ : ContinuousLinearMap.adjoint (𝕜 := 𝕜) J ∘L J =
      ContinuousLinearMap.id 𝕜 _ := by
    rw [Submodule.adjoint_subtypeL]
    ext x
    exact (transportedClosedSubmodule T S).toSubmodule
      |>.starProjection_mem_subspace_eq_self x
  rw [restrictedClosedTransport_eq_subtype_comp_equiv T S]
  change (B ∘L ContinuousLinearMap.adjoint (𝕜 := 𝕜) B) ∘L
      ContinuousLinearMap.adjoint (𝕜 := 𝕜) (J ∘L E) ∘L
        (J ∘L E) = ContinuousLinearMap.id 𝕜 _
  rw [ContinuousLinearMap.adjoint_comp]
  calc
    (B ∘L ContinuousLinearMap.adjoint (𝕜 := 𝕜) B) ∘L
          (ContinuousLinearMap.adjoint (𝕜 := 𝕜) E ∘L
            ContinuousLinearMap.adjoint (𝕜 := 𝕜) J) ∘L
          (J ∘L E) =
        B ∘L (ContinuousLinearMap.adjoint (𝕜 := 𝕜) B ∘L
          ContinuousLinearMap.adjoint (𝕜 := 𝕜) E) ∘L
          (ContinuousLinearMap.adjoint (𝕜 := 𝕜) J ∘L J) ∘L E := by
      ext x
      rfl
    _ = ContinuousLinearMap.id 𝕜 _ := by
      rw [hBadjEadj, hJ]
      simpa using hBE

omit [CompleteSpace H] [CompleteSpace K] in
theorem restrictedClosedTransport_range
    (T : H ≃L[𝕜] K) (S : ClosedSubmodule 𝕜 H) :
    (restrictedClosedTransport T S).range =
      (transportedClosedSubmodule T S).toSubmodule := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (ClosedSubmodule.mem_mapEquiv_iff' T S x).2 x.property
  · intro hy
    have hy' := (ClosedSubmodule.mem_mapEquiv_iff T S y).1 hy
    let x : S := ⟨T.symm y, hy'⟩
    refine ⟨x, ?_⟩
    change T (T.symm y) = y
    exact T.apply_symm_apply y

/-- The canonical orthogonal projection onto the image of a closed subspace
under a bounded invertible transport. -/
noncomputable def transportedSoninStarProjection
    (T : H ≃L[𝕜] K) (S : ClosedSubmodule 𝕜 H) : K →L[𝕜] K :=
  gramCorrectedProjection (restrictedClosedTransport T S)
    (restrictedTransportGramInv T S)

theorem transportedSoninStarProjection_isStarProjection
    (T : H ≃L[𝕜] K) (S : ClosedSubmodule 𝕜 H) :
    IsStarProjection (transportedSoninStarProjection T S) := by
  exact gramCorrectedProjection_isStarProjection
    (restrictedClosedTransport T S) (restrictedTransportGramInv T S)
    (restrictedTransportGramInv_leftInverse T S)
    (restrictedTransportGramInv_isSelfAdjoint T S)

theorem transportedSoninStarProjection_range
    (T : H ≃L[𝕜] K) (S : ClosedSubmodule 𝕜 H) :
    (transportedSoninStarProjection T S).range =
      (transportedClosedSubmodule T S).toSubmodule := by
  calc
    (transportedSoninStarProjection T S).range =
        (restrictedClosedTransport T S).range :=
      gramCorrectedProjection_range _ _
        (restrictedTransportGramInv_leftInverse T S)
    _ = (transportedClosedSubmodule T S).toSubmodule :=
      restrictedClosedTransport_range T S

end RestrictedTransport

end CC20Concrete
end ConnesWeilRH
