import ConnesWeilRH.Dev.C1BombieriSection8EndpointWirtinger

namespace ConnesWeilRH
namespace Source
namespace ProbeQuadraticBridge

open C1BombieriSection7Gamma
open C1BombieriSection7H
open C1BombieriSection7Readback
open C1BombieriSection8EigenGram
open C1BombieriSection8TotalAssembly
open scoped ComplexConjugate

variable {n : Nat}

example (t : Real) (gamma : Fin n -> Real) (z : Fin n -> Complex) :
    star (bombieriWOfZ gamma z) ⬝ᵥ
        (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)
      = bombieriKstarGram t gamma z := by
  unfold dotProduct bombieriKstarGram
  simp only [Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hconj : star (bombieriWOfZ gamma z i) =
      ((1 / 4 + gamma i ^ 2 : Real) : Complex) * star (z i) := by
    simpa only [starRingEnd_apply] using conj_bombieriWOfZ gamma z i
  change star (bombieriWOfZ gamma z i) *
      (fun j => bombieriHMatrix gamma t i j) ⬝ᵥ bombieriWOfZ gamma z = _
  rw [hconj]
  simp only [dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [bombieriHMatrix, Matrix.of_apply, bombieriWOfZ]
  calc
    ((1 / 4 + gamma i ^ 2 : Real) : Complex) * star (z i) *
          (bombieriH (gamma i) (gamma j) t
            * (((1 / 4 + gamma j ^ 2 : Real) : Complex) * z j))
        = (((1 / 4 + gamma i ^ 2 : Real) : Complex) * star (z i)) *
            (bombieriH (gamma i) (gamma j) t
              * ((1 / 4 + gamma j ^ 2 : Real) : Complex)) * z j := by ring
    _ = (((1 / 4 + gamma i ^ 2 : Real) : Complex) * star (z i)) *
          (((2 * t : Real) : Complex) * bombieriKstar (gamma i) (gamma j) t) * z j := by
      rw [mul_comm (bombieriH (gamma i) (gamma j) t)
        ((1 / 4 + gamma j ^ 2 : Real) : Complex),
        bombieriH_mul_weight_eq]
    _ = _ := by
      simp only [starRingEnd_apply]
      ring

end ProbeQuadraticBridge
end Source
end ConnesWeilRH
