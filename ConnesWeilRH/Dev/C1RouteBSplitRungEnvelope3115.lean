import ConnesWeilRH.Dev.C1RouteBLowRungPoweredSeedEnvelope3112

/-! Proved low rungs and a seventh-order exterior arm on the same seed.

The low-rung bound remains useful on compact frequency intervals, but
record 2729 rules out its quadratic full-line envelope on a 56-node owner.
This module uses the sharp proved D3 upper endpoint and adds the actual
D7 certificate. It proves an analytic envelope, not the three wired pins.
-/

namespace ConnesWeilRH.Source.C1RouteBSplitRungEnvelope3115

open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open C1ExplicitSmoothSeed C1ExplicitFiniteNodeCorrection C1StripTransport2722C
open ConnesWeilRH.Dev.C1SeedCertificate3101
open ConnesWeilRH.Dev.C1PoweredSeedD4D7Adapter3104
open scoped BigOperators

noncomputable section

def splitRungs3115 : Finset ℕ := {1, 2, 3, 4, 7}

def splitD3115 (k : ℕ) : ℝ :=
  if k = 1 then 2 else
    if k = 2 then 8 else
      if k = 3 then 787283385 / 10000000 else
        if k = 4 then 1500 else 2000000000

theorem splitRungs_nonempty3115 : splitRungs3115.Nonempty := by
  simp [splitRungs3115]

theorem splitD_nonneg3115 (k : ℕ) : 0 ≤ splitD3115 k := by
  unfold splitD3115
  split_ifs <;> norm_num

theorem splitD_bound3115 (k : ℕ) (hk : k ∈ splitRungs3115) :
    derivOrderL1 k smoothSeed ≤ splitD3115 k := by
  have hk' : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 7 := by
    simpa [splitRungs3115] using hk
  rcases hk' with rfl | rfl | rfl | rfl | rfl
  · rw [derivOrderL1_one, derivativeL1_smoothSeed_eq_two]
    norm_num [splitD3115]
  · rw [derivOrderL1_smoothSeed_two]
    norm_num [splitD3115]
  · have h := derivOrderL1_smoothSeed_three_mem_Icc.2
    norm_num [splitD3115] at h ⊢
    exact h
  · simpa [splitD3115] using smoothSeed_derivOrderL1_four_lt3103.le
  · simpa [splitD3115] using smoothSeed_derivOrderL1_seven_lt3103.le

def splitPoweredSeedEnvelope3115 (nodes : Finset ℂ) (y : ℂ → ℂ)
    (t : ℝ) : ℝ :=
  ∑ z ∈ nodes,
    ‖y z‖ / (‖nodeProduct nodes z z‖ * ‖laplaceAt poweredSeed 0‖) *
    (∏ w ∈ nodes.erase z,
      Real.sqrt ((max |w.re| |1 - w.re|) ^ 2 + (t - w.im) ^ 2)) *
    (if t = z.im then Real.exp (max |z.re| |1 - z.re|) * 3
      else min (Real.exp (max |z.re| |1 - z.re|) * 3)
        (splitRungs3115.inf' splitRungs_nonempty3115 (fun k =>
          Real.exp (max |z.re| |1 - z.re|) *
            (splitD3115 k * (2 : ℝ) ^ k / |t - z.im| ^ k)))) ^ 10

theorem norm_cardinalSum_poweredSeed_le_split_env3115
    (nodes : Finset ℂ) (y : ℂ → ℂ) {σ t : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    ‖cardinalSum nodes poweredSeed y ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      splitPoweredSeedEnvelope3115 nodes y t := by
  simpa [splitPoweredSeedEnvelope3115] using
    norm_cardinalSum_poweredSeed_le_endpoint_env nodes y
      (l1u := 3) smoothSeed_l1Mass_le_three (by norm_num)
      (rungs := splitRungs3115) splitRungs_nonempty3115
      (D := splitD3115) splitD_bound3115
      (σ := σ) (t := t) (fun k _ => splitD_nonneg3115 k) hσ

end
end ConnesWeilRH.Source.C1RouteBSplitRungEnvelope3115
