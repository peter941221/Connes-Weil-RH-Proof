import ConnesWeilRH.Dev.C1BombieriP2Bridge

namespace ConnesWeilRH.Source.C1BombieriP2Bridge

open C1BombieriFiniteQuadraticBridge
open C1BombieriSection7Gamma
open C1SameOwnerWeil
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution

noncomputable section

structure ProbeData (g : CompactLogTest) where
  n : Nat
  t : Real
  ht : 0 < t
  gamma : Fin n → Real
  z : Fin n → Complex
  residual : Real
  tailBound : Real
  qw_eq_quadratic_sub_residual : qw g =
    (star (bombieriWOfZ gamma z) ⬝ᵥ
      (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)).re - residual
  residual_abs_le : |residual| ≤ tailBound
  tailBound_le_quadratic : tailBound ≤
    (star (bombieriWOfZ gamma z) ⬝ᵥ
      (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)).re

theorem probe_qw_nonneg {g : CompactLogTest} (p : ProbeData g) : 0 ≤ qw g := by
  obtain ⟨S, hS, hform⟩ :=
    bombieriHMatrix_quadraticForm_eq_ofReal_nonneg p.t p.ht p.gamma p.z
  have hformReal :
      (star (bombieriWOfZ p.gamma p.z) ⬝ᵥ
          (bombieriHMatrix p.gamma p.t).mulVec (bombieriWOfZ p.gamma p.z)).re = S := by
    rw [hform]
    simp
  have htail : 0 ≤ p.tailBound := by
    exact le_trans (abs_nonneg p.residual) p.residual_abs_le
  rw [p.qw_eq_quadratic_sub_residual, hformReal]
  have hres : p.residual ≤ p.tailBound :=
    (abs_le.mp p.residual_abs_le).2
  have htailform : p.tailBound ≤ S := by
    simpa [hformReal] using p.tailBound_le_quadratic
  linarith

end
end ConnesWeilRH.Source.C1BombieriP2Bridge
