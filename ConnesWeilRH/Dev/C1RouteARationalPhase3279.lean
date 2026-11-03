import ConnesWeilRH.Dev.C1RouteARationalWeightTaylor3278
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerStagedPhasePower3251

namespace ConnesWeilRH.Dev

namespace RatRect3276

def powSq (a : RatRect3276) : ℕ → RatRect3276
  | 0 => a
  | n + 1 => mul (powSq a n) (powSq a n)

theorem mem_powSq {z : ℂ} {a : RatRect3276}
    (ha : a.Mem z) : ∀ n, (powSq a n).Mem (z ^ (2 ^ n))
  | 0 => by simpa [powSq] using ha
  | n + 1 => by
      have h := mem_mul (mem_powSq ha n) (mem_powSq ha n)
      have hp : z ^ (2 ^ (n + 1)) =
          (z ^ (2 ^ n)) * (z ^ (2 ^ n)) := by
        rw [show 2 ^ (n + 1) = (2 ^ n) * 2 by ring, pow_mul]
        simp [pow_two]
      simpa [powSq, hp] using h

end RatRect3276

theorem ratPhaseRect_mem3279
    {angle : ℚ} {base : RatRect3276}
    (hangle : |((angle : ℝ) / 512)| ≤ 1)
    (hsubset : base.toReal.reLo ≤ (phaseRect3218 (angle : ℝ)).reLo ∧
      (phaseRect3218 (angle : ℝ)).reHi ≤ base.toReal.reHi ∧
      base.toReal.imLo ≤ (phaseRect3218 (angle : ℝ)).imLo ∧
      (phaseRect3218 (angle : ℝ)).imHi ≤ base.toReal.imHi) :
    base.Mem
      (Complex.exp (((angle : ℝ) / 512 : ℝ) * Complex.I)) := by
  have hphase := phaseRect_mem3218 hangle
  change base.toReal.Mem
    (Complex.exp (((angle : ℝ) / 512 : ℝ) * Complex.I))
  exact rectSubset2676 hsubset.1 hsubset.2.1 hsubset.2.2.1 hsubset.2.2.2 hphase

 theorem ratPhasePowSq_mem3279
    {angle : ℚ} {base : RatRect3276}
    (hbase : base.Mem
      (Complex.exp (((angle : ℝ) / 512 : ℝ) * Complex.I))) :
    (RatRect3276.powSq base 9).Mem
      (Complex.exp (((angle : ℝ) : ℂ) * Complex.I)) := by
  have hpow := RatRect3276.mem_powSq hbase 9
  have hphase := complex_phase_eq_pow512_3218 (angle : ℝ)
  have hpow512 :
      (Complex.exp (((angle : ℝ) / 512 : ℝ) * Complex.I)) ^ 512 =
        Complex.exp (((angle : ℝ) : ℂ) * Complex.I) := by
    exact hphase.symm
  have hbase' : (RatRect3276.powSq base 9).Mem
      ((Complex.exp (((angle : ℝ) / 512 : ℝ) * Complex.I)) ^ 512) := by
    simpa using hpow
  rw [hpow512] at hbase'
  exact hbase'


def ratPhaseRe3279 (angle : ℚ) : ℚ :=
  ∑ k ∈ Finset.range 13,
    (-1 : ℚ) ^ k * (angle / 512) ^ (2 * k) / ((2 * k).factorial : ℚ)

def ratPhaseIm3279 (angle : ℚ) : ℚ :=
  ∑ k ∈ Finset.range 13,
    (-1 : ℚ) ^ k * (angle / 512) ^ (2 * k + 1) /
      ((2 * k + 1).factorial : ℚ)

def ratPhaseError3279 (angle : ℚ) : ℚ :=
  |angle / 512| ^ 26 *
    ((27 : ℚ) / ((26 : ℕ).factorial * 26))

def ratPhaseRect3279 (angle : ℚ) : RatRect3276 :=
  { reLo := ratPhaseRe3279 angle - ratPhaseError3279 angle
    reHi := ratPhaseRe3279 angle + ratPhaseError3279 angle
    imLo := ratPhaseIm3279 angle - ratPhaseError3279 angle
    imHi := ratPhaseIm3279 angle + ratPhaseError3279 angle }

theorem ratPhaseRect_toReal3279 (angle : ℚ) :
    (ratPhaseRect3279 angle).toReal = phaseRect3218 (angle : ℝ) := by
  apply ComplexRect2427.ext <;>
    simp [ratPhaseRect3279, ratPhaseRe3279, ratPhaseIm3279,
      ratPhaseError3279, phaseRect3218, phaseTaylorError3218,
      reExpIPartial2676, imExpIPartial2676, RatRect3276.toReal,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow, Rat.cast_abs]
  <;> norm_num
  <;> push_cast
  <;> ring
theorem ratPhaseRect_mem_canonical3279
    {angle : ℚ} (hangle : |((angle : ℝ) / 512)| ≤ 1) :
    (ratPhaseRect3279 angle).Mem
      (Complex.exp (((angle : ℝ) / 512 : ℝ) * Complex.I)) := by
  apply ratPhaseRect_mem3279 hangle
  rw [ratPhaseRect_toReal3279]
  exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

def record2680CenterRat3279 (index : ℕ) : ℚ :=
  -(65536001 / 10000000 : ℚ) +
    ((2 * index + 1 : ℕ) : ℚ) *
      (65536001 / 10000000 : ℚ) / 40960

theorem record2680CenterRat_cast3279 (index : ℕ) :
    (record2680CenterRat3279 index : ℝ) = record2680Center3212 index := by
  norm_num [record2680CenterRat3279, record2680Center3212,
    record2680Grid3212, diagnosticRadius3201]
  push_cast
  ring

def capturedModulationsRat3279 : Fin 30 → ℚ :=
  ![((-5524291025718029 : ℚ) / 140737488355328),
    ((-5524291025718029 : ℚ) / 140737488355328),
    ((5524291025718029 : ℚ) / 140737488355328),
    ((5524291025718029 : ℚ) / 140737488355328),
    ((-5524291025718029 : ℚ) / 140737488355328),
    (0 : ℚ), (0 : ℚ), (0 : ℚ),
    ((-3978571430081297 : ℚ) / 281474976710656),
    ((-5917178117733711 : ℚ) / 281474976710656),
    ((-3519965277442521 : ℚ) / 140737488355328),
    ((-3894251610461801 : ℚ) / 140737488355328),
    ((-2140960324737725 : ℚ) / 70368744177664),
    ((-4635197846686455 : ℚ) / 140737488355328),
    ((-5289784310949011 : ℚ) / 140737488355328),
    ((-5758797740487047 : ℚ) / 140737488355328),
    ((-3048871735671609 : ℚ) / 70368744177664),
    ((-6756124363134027 : ℚ) / 140737488355328),
    ((-1751261042181613 : ℚ) / 35184372088832),
    ((-1863727500536955 : ℚ) / 35184372088832),
    ((-7944103127967419 : ℚ) / 140737488355328),
    ((-8352353914239387 : ℚ) / 140737488355328),
    ((-8561311721741165 : ℚ) / 140737488355328),
    ((-4581887954876333 : ℚ) / 70368744177664),
    ((-4720322026636147 : ℚ) / 70368744177664),
    ((-152934154702833 : ℚ) / 2199023255552),
    ((-316954711375437 : ℚ) / 4398046511104),
    ((-665905501606627 : ℚ) / 8796093022208),
    ((-2714292757716727 : ℚ) / 35184372088832),
    ((-2791435723263659 : ℚ) / 35184372088832)]

theorem capturedModulationsRat_cast3279 (family : Fin 30) :
    (capturedModulationsRat3279 family : ℝ) = capturedModulations2584 family := by
  fin_cases family <;>
    norm_num [capturedModulationsRat3279, capturedModulations2584,
      Matrix.cons_val_zero, Fin.ext_iff]

def record2680PhaseAngleRat3279 (index : ℕ) (family : Fin 30) : ℚ :=
  capturedModulationsRat3279 family * record2680CenterRat3279 index

theorem record2680PhaseAngleRat_cast3279 (index : ℕ) (family : Fin 30) :
    (record2680PhaseAngleRat3279 index family : ℝ) =
      capturedModulations2584 family * record2680Center3212 index := by
  simp [record2680PhaseAngleRat3279, record2680CenterRat_cast3279,
    capturedModulationsRat_cast3279]

theorem record2680PhaseAngleRat_small3279
    {index : ℕ} (hindex : index < 40960) (family : Fin 30)
    (hactive : |record2680Center3212 index| < C1RouteAOwnerScaleAudit.storedWidth family ^ 2) :
    |((record2680PhaseAngleRat3279 index family : ℝ) / 512)| ≤ 1 := by
  have hprod :
      |capturedModulations2584 family * record2680Center3212 index| ≤ 512 := by
    rw [abs_mul]
    fin_cases family <;>
      norm_num [capturedModulations2584, C1RouteAOwnerScaleAudit.storedWidth, Matrix.cons_val_zero,
        Matrix.cons_val_four, Fin.ext_iff] at hactive ⊢ <;>
      nlinarith [abs_nonneg (record2680Center3212 index)]
  rw [record2680PhaseAngleRat_cast3279]
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 512)]
  norm_num at hprod ⊢
  nlinarith [hprod]

theorem record2680CanonicalPhaseRect_mem3279
    {index : ℕ} (hindex : index < 40960) (family : Fin 30)
    (hactive : |record2680Center3212 index| < C1RouteAOwnerScaleAudit.storedWidth family ^ 2) :
    (ratPhaseRect3279 (record2680PhaseAngleRat3279 index family)).Mem
      (Complex.exp (((((capturedModulations2584 family * record2680Center3212 index : ℝ) / 512) : ℂ) *
        Complex.I))) := by
  have hsmall := record2680PhaseAngleRat_small3279 hindex family hactive
  have hbase := ratPhaseRect_mem_canonical3279 hsmall
  rw [record2680PhaseAngleRat_cast3279] at hbase
  convert hbase using 1 <;> norm_num <;> ring
theorem record2680CanonicalPhasePowRect_mem3279
    {index : ℕ} (hindex : index < 40960) (family : Fin 30)
    (hactive : |record2680Center3212 index| <
      C1RouteAOwnerScaleAudit.storedWidth family ^ 2) :
    (RatRect3276.powSq
      (ratPhaseRect3279 (record2680PhaseAngleRat3279 index family)) 9).Mem
      (Complex.exp (((capturedModulations2584 family *
        record2680Center3212 index : ℝ) : ℂ) * Complex.I)) := by
  have hbase0 := record2680CanonicalPhaseRect_mem3279 hindex family hactive
  have hbase :
      (ratPhaseRect3279 (record2680PhaseAngleRat3279 index family)).Mem
        (Complex.exp
          ((((record2680PhaseAngleRat3279 index family : ℚ) : ℝ) / 512 : ℝ) *
            Complex.I)) := by
    have ha := record2680PhaseAngleRat_cast3279 index family
    rw [ha]
    have hscalar :
        (((capturedModulations2584 family * record2680Center3212 index / 512 : ℝ) : ℂ)) =
          ((capturedModulations2584 family * record2680Center3212 index : ℂ) / 512) := by
      push_cast
      ring
    rw [hscalar]
    simpa only [Complex.ofReal_mul] using hbase0
  have hpow := ratPhasePowSq_mem3279
    (base := ratPhaseRect3279 (record2680PhaseAngleRat3279 index family))
    hbase
  have ha := record2680PhaseAngleRat_cast3279 index family
  rw [ha] at hpow
  exact hpow

end ConnesWeilRH.Dev