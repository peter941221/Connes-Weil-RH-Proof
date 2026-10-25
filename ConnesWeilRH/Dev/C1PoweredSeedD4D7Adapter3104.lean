import ConnesWeilRH.Dev.C1PoweredSeedEnvelope2725
import ConnesWeilRH.Dev.C1SeedD4D7Certified3103
import ConnesWeilRH.Dev.C1SmoothSeedMassThree2728

/-! The actual-owner adapter for the two newly certified seed rungs.

This file removes the generic mass and D4/D7 hypotheses from the 2725
powered-seed envelope. It deliberately leaves the node coefficients and
the resulting cardinal pin as an explicit envelope: a numerical pin still
needs the independent node/cancellation certificate. -/

namespace ConnesWeilRH.Dev.C1PoweredSeedD4D7Adapter3104

open MeasureTheory
open ConnesWeilRH.Source
open ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection
open ConnesWeilRH.Source.C1ExplicitSmoothSeed
open ConnesWeilRH.Source.C1StripTransport2722C
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Dev.C1SeedCertificate3101
open scoped BigOperators

noncomputable section

def d4d7Rungs3104 : Finset ℕ := {4, 7}

def d4d7D3104 (k : ℕ) : ℝ := if k = 4 then 1500 else 2000000000

theorem d4d7Rungs_nonempty3104 : d4d7Rungs3104.Nonempty := by
  simp [d4d7Rungs3104]

theorem d4d7D_nonneg3104 (k : ℕ) : 0 ≤ d4d7D3104 k := by
  by_cases hk : k = 4 <;> simp [d4d7D3104, hk] <;> norm_num

theorem d4d7D_bound3104 (k : ℕ) (hk : k ∈ d4d7Rungs3104) :
    derivOrderL1 k smoothSeed ≤ d4d7D3104 k := by
  have hk' : k = 4 ∨ k = 7 := by
    simpa [d4d7Rungs3104] using hk
  rcases hk' with rfl | rfl
  · simp [d4d7D3104]
    exact smoothSeed_derivOrderL1_four_lt3103.le
  · simp [d4d7D3104]
    exact smoothSeed_derivOrderL1_seven_lt3103.le

def d4d7PoweredSeedEnvelope3104 (nodes : Finset ℂ) (y : ℂ → ℂ)
    (σ t : ℝ) : ℝ :=
  ∑ z ∈ nodes,
    ‖y z‖ / (‖nodeProduct nodes z z‖ * ‖laplaceAt poweredSeed 0‖) *
    (∏ w ∈ nodes.erase z,
      Real.sqrt ((max |w.re| |1 - w.re|) ^ 2 + (t - w.im) ^ 2)) *
    (if t = z.im then Real.exp (max |z.re| |1 - z.re|) * 3
      else min (Real.exp (max |z.re| |1 - z.re|) * 3)
        (d4d7Rungs3104.inf' d4d7Rungs_nonempty3104 (fun k =>
          Real.exp (max |z.re| |1 - z.re|) *
            (d4d7D3104 k * (2 : ℝ) ^ k / |t - z.im| ^ k)))) ^ 10

theorem norm_cardinalSum_poweredSeed_le_d4d7_env3104
    (nodes : Finset ℂ) (y : ℂ → ℂ) {σ t : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    ‖cardinalSum nodes poweredSeed y
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      d4d7PoweredSeedEnvelope3104 nodes y σ t := by
  have hgeneric := norm_cardinalSum_poweredSeed_le_endpoint_env
    nodes y (l1u := 3) smoothSeed_l1Mass_le_three (by norm_num)
    (rungs := d4d7Rungs3104) d4d7Rungs_nonempty3104
    (D := d4d7D3104) d4d7D_bound3104
    (σ := σ) (t := t) (fun k hk => d4d7D_nonneg3104 k) hσ
  simpa [d4d7PoweredSeedEnvelope3104, d4d7D3104] using hgeneric

end
end ConnesWeilRH.Dev.C1PoweredSeedD4D7Adapter3104
