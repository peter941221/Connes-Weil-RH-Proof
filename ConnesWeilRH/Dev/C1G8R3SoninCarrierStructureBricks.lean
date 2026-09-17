/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3GateResidualMomentBricks
import ConnesWeilRH.Source.CC20Concrete.CCM24HardyTitchmarsh

/-!
# Sonin-carrier structure bricks (wave V, record 1589)

Bricks that pin the *shape* of the source Sonin carrier and close the algebraic
content of records 1581, 1586 and 1587.  Every statement is on committed
objects; no spectral, density or sign input appears as a conclusion.

* `starProjection_comp_apply_eq_self_iff` -- for two orthogonal projections `E`,
  `Q` the fixed points of the sandwich `E o Q o E` are exactly the vectors in
  both ranges.  This is record 1586 section 1 ("the carrier is `ker (1 - EQE)`")
  in its general, hypothesis-free form: no commutativity is used, and the
  equality case is the 1588 brick
  `starProjection_eq_self_of_re_inner_eq_normSq`.
* `radialSupport_comp_fourierSupport_apply_eq_self_iff` -- the same at the
  project's own pair `(radialSupportProjection, sourceFourierSupportProjection)`.
* `sourceSoninProjection_eq_self_iff_mem_radial_and_fourier` -- the same with the
  infimum projection, in membership form.
* `sub_sourceSoninProjection_eq_add_defect` -- record 1587 section 2.1's exact
  vector identity: the residual column is the radial escape plus the carrier
  defect of the RADIALLY PROJECTED vector.  The only input is `P o E = P`.
* `norm_sq_sub_sourceSoninProjection_eq_radial_add_defect` -- the squared form;
  the two summands are orthogonal, so the squares add exactly.
* `sum_norm_sq_sub_starProjection_le_of_quadraticFormGap` -- the (star)-level
  form of the 1588 moment conversion: summed over a finite family it reads
  `sum_i ||(1 - P) e_i||^2 <= gap^-1 * sum_i <e_i, (1 - K) e_i>`, which is the
  trace level the gate consumes, not an operator-norm bound.
* `radialSupportProjection_eq_self_of_mem_sonin` and
  `sourceFourierSupportProjection_eq_self_of_mem_sonin` -- record 1581 section
  1's "carrier vacuity, with scope", as its two exact halves, plus the
  sandwiched consequence.
* `ccm24ArchimedeanHardyTitchmarsh_mem_sonin_iff` (in the CC20 namespace) -- the
  Hardy--Titchmarsh involution maps the source Sonin carrier onto itself.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSSoninCarrierStructure

open ConnesWeilRH.Source.CC20Concrete
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGateResidualMomentBricks
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## 1. The fixed space of the sandwich `E o Q o E` -/

/-- For two orthogonal projections on a complex inner product space, the fixed
points of the sandwich `E o Q o E` are exactly the vectors lying in both
ranges.

Neither commutativity nor any relation between `E` and `Q` is assumed.  The two
directions are (i) `x = Q (E x)` gives `x in range Q`, while
`‖E x‖ <= ‖x‖ = ‖Q (E x)‖ <= ‖E x‖` forces `‖E x‖ = ‖x‖` and hence `E x = x`,
so also `x in range E`; and (ii) the projection identity. -/
theorem starProjection_comp_apply_eq_self_iff
    {E Q : Submodule ℂ H} [E.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {x : H} :
    Q.starProjection (E.starProjection x) = x ↔ x ∈ E ∧ x ∈ Q := by
  constructor
  · intro h
    have hnorm : ‖E.starProjection x‖ = ‖x‖ := by
      have h1 : ‖E.starProjection x‖ ≤ ‖x‖ :=
        Submodule.norm_starProjection_apply_le (K := E) x
      have h2 : ‖x‖ ≤ ‖E.starProjection x‖ := by
        have h3 : ‖x‖ = ‖Q.starProjection (E.starProjection x)‖ := by rw [h]
        exact h3.trans_le (Submodule.norm_starProjection_apply_le (K := Q)
          (E.starProjection x))
      exact le_antisymm h1 h2
    have hxE : x ∈ E := (Submodule.mem_iff_norm_starProjection E x).mpr hnorm
    have hEx : E.starProjection x = x :=
      (Submodule.starProjection_eq_self_iff (K := E)).mpr hxE
    have hQ : Q.starProjection x = x :=
      (congrArg (fun y => Q.starProjection y) hEx).symm.trans h
    exact ⟨hxE, (Submodule.starProjection_eq_self_iff (K := Q)).mp hQ⟩
  · rintro ⟨hxE, hxQ⟩
    rw [(Submodule.starProjection_eq_self_iff (K := E)).mpr hxE,
      (Submodule.starProjection_eq_self_iff (K := Q)).mpr hxQ]

/-- The sandwich identity at the project's own projection pair: the vectors that
the composite `Q o E` fixes are exactly the source Sonin carrier vectors. -/
theorem radialSupport_comp_fourierSupport_apply_eq_self_iff
    (lambda : CCM24SoninScale) (x : finiteSCarrier) :
    sourceFourierSupportProjection lambda (radialSupportProjection lambda x) = x ↔
      x ∈ (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule ∧
        x ∈ (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule := by
  have h := starProjection_comp_apply_eq_self_iff
    (E := (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule)
    (Q := (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule) (x := x)
  simpa only [radialSupportProjection, sourceFourierSupportProjection] using h

/-- The same statement with the Sonin projection itself, in membership form. -/
theorem sourceSoninProjection_eq_self_iff_mem_radial_and_fourier
    (lambda : CCM24SoninScale) (x : finiteSCarrier) :
    sourceSoninProjection lambda x = x ↔
      x ∈ (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule ∧
        x ∈ (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule :=
  Submodule.starProjection_eq_self_iff.trans Submodule.mem_inf

/-! ## 2. The exact split of the residual column (record 1587 section 2.1) -/

/-- The residual column splits as the radial escape plus the carrier defect of
the RADIALLY PROJECTED vector.  The only input is `P o E = P`, committed in
record 1588. -/
theorem sub_sourceSoninProjection_eq_add_defect
    (lambda : CCM24SoninScale) (g : finiteSCarrier) :
    g - sourceSoninProjection lambda g =
      (g - radialSupportProjection lambda g) +
        (radialSupportProjection lambda g -
          sourceSoninProjection lambda (radialSupportProjection lambda g)) := by
  have hPE : sourceSoninProjection lambda (radialSupportProjection lambda g) =
      sourceSoninProjection lambda g := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T g)
        (sourceSoninProjection_comp_radialSupportProjection lambda)
  rw [hPE]
  abel

/-- The squared form of the same split: the two summands are orthogonal, so the
squares add exactly.  This is the shape record 1587 section 2.1 writes as
`residual^2 = strip mass + carrier distance`, the carrier distance being taken
at the radially projected vector. -/
theorem norm_sq_sub_sourceSoninProjection_eq_radial_add_defect
    (lambda : CCM24SoninScale) (g : finiteSCarrier) :
    ‖g - sourceSoninProjection lambda g‖ ^ 2 =
      ‖g - radialSupportProjection lambda g‖ ^ 2 +
        ‖radialSupportProjection lambda g -
          sourceSoninProjection lambda (radialSupportProjection lambda g)‖ ^ 2 := by
  have hPE : sourceSoninProjection lambda (radialSupportProjection lambda g) =
      sourceSoninProjection lambda g := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T g)
        (sourceSoninProjection_comp_radialSupportProjection lambda)
  rw [hPE]
  exact norm_sq_sub_sourceSoninProjection_eq_add lambda g

/-! ## 3. The (star)-level summation of the moment conversion -/

/-- The 1588 per-vector moment conversion summed over a finite family: the
squared distances to the fixed space are bounded by `gap^-1` times the summed
quadratic form of `1 - K`.  This is the trace-level form the gate consumes; the
whole-space operator-norm adapter cannot be summed this way.

No orthonormality of the family is needed: the per-vector bound is uniform. -/
theorem sum_norm_sq_sub_starProjection_le_of_quadraticFormGap
    {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (K : H →L[ℂ] H) {gap : ℝ} (hgap : 0 < gap)
    (hsym : ∀ u v : H, inner ℂ (K u) v = inner ℂ u (K v))
    (hfix : ∀ u : H, u ∈ W ↔ K u = u)
    (hform : ∀ y : H, (∀ w ∈ W, inner ℂ y w = 0) →
      gap * ‖y‖ ^ 2 ≤ (inner ℂ y (y - K y)).re)
    {ι : Type*} (s : Finset ι) (e : ι → H) :
    ∑ i ∈ s, ‖e i - W.starProjection (e i)‖ ^ 2 ≤
      gap⁻¹ * ∑ i ∈ s, (inner ℂ (e i) (e i - K (e i))).re := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    norm_sq_sub_starProjection_le_of_quadraticFormGap K hgap hsym hfix hform (e i)

/-! ## 4. Carrier vacuity, with scope (record 1581 section 1) -/

/-- On the Sonin carrier the radial window projection acts as the identity. -/
theorem radialSupportProjection_eq_self_of_mem_sonin
    (lambda : CCM24SoninScale) {u : finiteSCarrier}
    (hu : u ∈ (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule) :
    radialSupportProjection lambda u = u := by
  have hu' : u ∈ (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule ∧
      u ∈ (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule := by
    simpa only [ccm24ArchimedeanSoninClosedSubspace, ClosedSubmodule.toSubmodule_inf,
      Submodule.mem_inf] using hu
  exact (Submodule.starProjection_eq_self_iff (K :=
    (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule)).mpr hu'.1

/-- On the Sonin carrier the Fourier window projection acts as the identity. -/
theorem sourceFourierSupportProjection_eq_self_of_mem_sonin
    (lambda : CCM24SoninScale) {u : finiteSCarrier}
    (hu : u ∈ (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule) :
    sourceFourierSupportProjection lambda u = u := by
  have hu' : u ∈ (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule ∧
      u ∈ (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule := by
    simpa only [ccm24ArchimedeanSoninClosedSubspace, ClosedSubmodule.toSubmodule_inf,
      Submodule.mem_inf] using hu
  exact (Submodule.starProjection_eq_self_iff (K :=
    (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule)).mpr hu'.2

/-- The algebraic consequence of the two halves: an operator sandwiched between
radial window projections cannot see the window on the carrier.  This is the
identity `J^dagger X E J = J^dagger X J` of record 1581 section 1, stated
without inclusion maps. -/
theorem radialSupportProjection_comp_apply_eq_of_mem_sonin
    (lambda : CCM24SoninScale) (X : finiteSCarrier →L[ℂ] finiteSCarrier)
    {u : finiteSCarrier}
    (hu : u ∈ (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule) :
    radialSupportProjection lambda (X (radialSupportProjection lambda u)) =
      radialSupportProjection lambda (X u) := by
  rw [radialSupportProjection_eq_self_of_mem_sonin lambda hu]

end CCM24FiniteSSoninCarrierStructure
end CCM25Concrete
end Source

namespace Source
namespace CC20Concrete
namespace CCM24SoninCarrierInvariance

open ConnesWeilRH.Source.CC20Concrete

/-- The Hardy--Titchmarsh involution maps the source Sonin carrier onto itself:
`H u` satisfies the radial and the Fourier support conditions exactly when `u`
does.  The two conditions exchange places, because the Fourier support space is
the preimage of the radial one (committed `mem_..._iff`) and `H` is an
involution (committed `ccm24ArchimedeanHardyTitchmarsh_involutive`). -/
theorem ccm24ArchimedeanHardyTitchmarsh_mem_sonin_iff
    (lambda : CCM24SoninScale) (u : cc20GlobalLogCrossingL2) :
    ccm24ArchimedeanHardyTitchmarsh u ∈
        (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule ↔
      u ∈ (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule := by
  have hcomap : ∀ v : cc20GlobalLogCrossingL2,
      (v ∈ ccm24ArchimedeanFourierSupportClosedSubspace lambda) ↔
        ccm24ArchimedeanHardyTitchmarsh v ∈
          ccm24LogRadialSupportClosedSubspace lambda :=
    fun v => mem_ccm24ArchimedeanFourierSupportClosedSubspace_iff lambda v
  have hinv : ∀ v : cc20GlobalLogCrossingL2,
      ccm24ArchimedeanHardyTitchmarsh (ccm24ArchimedeanHardyTitchmarsh v) = v :=
    fun v => ccm24ArchimedeanHardyTitchmarsh_involutive v
  have hmem : ∀ v : cc20GlobalLogCrossingL2,
      (v ∈ (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule) ↔
        (v ∈ ccm24LogRadialSupportClosedSubspace lambda ∧
          v ∈ ccm24ArchimedeanFourierSupportClosedSubspace lambda) :=
    fun v => Submodule.mem_inf
  rw [hmem]
  constructor
  · rintro ⟨hE, hF⟩
    exact ⟨hinv u ▸ (hcomap (ccm24ArchimedeanHardyTitchmarsh u)).mp hF,
      (hcomap u).mpr hE⟩
  · rintro ⟨hE, hF⟩
    exact ⟨(hcomap u).mp hF,
      (hcomap (ccm24ArchimedeanHardyTitchmarsh u)).mpr ((hinv u).symm ▸ hE)⟩

end CCM24SoninCarrierInvariance
end CC20Concrete
end Source
end ConnesWeilRH
