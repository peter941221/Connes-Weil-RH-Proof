import ConnesWeilRH.Dev.C1PoweredSeedEnvelope2725
import ConnesWeilRH.Dev.C1PoweredSeedD4D7Adapter3104
import ConnesWeilRH.Dev.C1SeedD4D7Certified3103
import ConnesWeilRH.Dev.C1ExplicitSeedSecondOrderMass
import ConnesWeilRH.Dev.C1ExplicitSeedThirdOrderIntervalCertificate

/-! Low-rung powered-seed envelope adapter (3112).

Record 2727 identified `{1,2,3,4}` as the first rung set that clears all
three stored row-B pin prices at model grade.  This module instantiates the
existing endpoint-envelope theorem with kernel-checked low-rung bounds:
`D1 = 2`, `D2 = 8`, `D3 <= 84`, and `D4 <= 1500`.

It proves an analytic envelope only.  The finite full-frequency numerical
replay and the three wired pin inequalities remain separate obligations.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteBLowRungPoweredSeedEnvelope3112

open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open C1ExplicitSmoothSeed
open C1ExplicitFiniteNodeCorrection
open C1StripTransport2722C
open ConnesWeilRH.Dev.C1SeedCertificate3101
open ConnesWeilRH.Dev.C1PoweredSeedD4D7Adapter3104
open scoped BigOperators

noncomputable section

def lowRungs3112 : Finset ℕ := {1, 2, 3, 4}

def lowRungD3112 (k : ℕ) : ℝ :=
  if k = 1 then 2 else
    if k = 2 then 8 else
      if k = 3 then 84 else
        1500

theorem lowRungs_nonempty3112 : lowRungs3112.Nonempty := by
  simp [lowRungs3112]

theorem lowRungD_nonneg3112 (k : ℕ) (hk : k ∈ lowRungs3112) :
    0 ≤ lowRungD3112 k := by
  by_cases h1 : k = 1 <;>
    by_cases h2 : k = 2 <;>
      by_cases h3 : k = 3 <;>
        simp [lowRungD3112, h1, h2, h3] <;> norm_num

theorem lowRungD_bound3112 (k : ℕ) (hk : k ∈ lowRungs3112) :
    derivOrderL1 k smoothSeed ≤ lowRungD3112 k := by
  have hk' : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    simpa [lowRungs3112] using hk
  rcases hk' with rfl | rfl | rfl | rfl
  · rw [derivOrderL1_one, derivativeL1_smoothSeed_eq_two]
    norm_num [lowRungD3112]
  · rw [derivOrderL1_smoothSeed_two]
    norm_num [lowRungD3112]
  · have h := derivOrderL1_smoothSeed_three_mem_Icc.2
    norm_num [lowRungD3112] at h ⊢
    linarith
  · have h := smoothSeed_derivOrderL1_four_lt3103
    norm_num [lowRungD3112] at h ⊢
    linarith

def lowRungPoweredSeedEnvelope3112 (nodes : Finset ℂ) (y : ℂ → ℂ)
    (σ t : ℝ) : ℝ :=
  ∑ z ∈ nodes,
    ‖y z‖ / (‖nodeProduct nodes z z‖ * ‖laplaceAt poweredSeed 0‖) *
    (∏ w ∈ nodes.erase z,
      Real.sqrt ((max |w.re| |1 - w.re|) ^ 2 + (t - w.im) ^ 2)) *
    (if t = z.im then Real.exp (max |z.re| |1 - z.re|) * 3
      else min (Real.exp (max |z.re| |1 - z.re|) * 3)
        (lowRungs3112.inf' lowRungs_nonempty3112 (fun k =>
          Real.exp (max |z.re| |1 - z.re|) *
            (lowRungD3112 k * (2 : ℝ) ^ k / |t - z.im| ^ k)))) ^ 10

theorem norm_cardinalSum_poweredSeed_le_lowRung_env3112
    (nodes : Finset ℂ) (y : ℂ → ℂ) {σ t : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    ‖cardinalSum nodes poweredSeed y
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      lowRungPoweredSeedEnvelope3112 nodes y σ t := by
  have hgeneric := norm_cardinalSum_poweredSeed_le_endpoint_env
    nodes y (l1u := 3) smoothSeed_l1Mass_le_three (by norm_num)
    (rungs := lowRungs3112) lowRungs_nonempty3112
    (D := lowRungD3112) lowRungD_bound3112
    (σ := σ) (t := t) lowRungD_nonneg3112 hσ
  simpa [lowRungPoweredSeedEnvelope3112] using hgeneric

end
end C1RouteBLowRungPoweredSeedEnvelope3112
end Source
end ConnesWeilRH
