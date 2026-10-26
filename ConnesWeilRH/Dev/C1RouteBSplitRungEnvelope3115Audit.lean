import ConnesWeilRH.Dev.C1RouteBCardinalExterior3115
import ConnesWeilRH.Dev.C1RouteBExteriorRungArithmetic2818

open ConnesWeilRH.Source.C1RouteBSplitRungEnvelope3115
open ConnesWeilRH.Source.C1StripTransport2722C
open ConnesWeilRH.Source.C1ExplicitSmoothSeed

namespace ConnesWeilRH.Source.C1RouteBSplitRungEnvelope3115

theorem empty_exterior_bound3115 (y : ℂ → ℂ) (T : ℝ) (p : ℕ) :
    cardinalExteriorBound3115 ∅ y T p = 0 := by
  simp [cardinalExteriorBound3115]

theorem zero_values_exterior_bound3115 (nodes : Finset ℂ) (T : ℝ) (p : ℕ) :
    cardinalExteriorBound3115 nodes (fun _ => 0) T p = 0 := by
  simp [cardinalExteriorBound3115]

theorem reject_low_rung_degree3115 :
    (55 : ℤ) + 2 - 10 * 4 = 17 ∧ 0 < (55 : ℤ) + 2 - 10 * 4 ∧
      (55 : ℤ) + 2 - 10 * 7 = -13 := by
  norm_num

theorem reject_zero_frequency_exterior3115 {T : ℝ} (hT : 0 < T) :
    ¬T ≤ |(0 : ℝ)| := by simpa using not_le.mpr hT

theorem negative_frequency_exterior3115
    (nodes : Finset ℂ) (y : ℂ → ℂ) {σ t T : ℝ} (p : ℕ)
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (hT : 0 < T) (ht : T ≤ |t|)
    (hheight : ∀ z ∈ nodes, |z.im| < T) (hdegree : nodes.card + p ≤ 71) :
    |t| ^ p * ‖cardinalSum nodes poweredSeed y
      ((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ ≤
        cardinalExteriorBound3115 nodes y T p := by
  simpa only [abs_neg] using weighted_cardinalSum_le_exterior3115 nodes y p hσ hT
    (t := -t) (by simpa only [abs_neg] using ht) hheight hdegree

end ConnesWeilRH.Source.C1RouteBSplitRungEnvelope3115

#check norm_cardinalSum_poweredSeed_le_split_env3115
#check poweredSeed_exterior_arm3115
#check weighted_cardinalSum_le_exterior3115
#check normalized_cardinalSum_le_exterior3115

#print axioms splitRungs_nonempty3115
#print axioms splitD_nonneg3115
#print axioms splitD_bound3115
#print axioms norm_cardinalSum_poweredSeed_le_split_env3115
#print axioms poweredSeed_exterior_arm3115
#print axioms weighted_cardinalSum_le_exterior3115
#print axioms normalized_cardinalSum_le_exterior3115
#print axioms empty_exterior_bound3115
#print axioms zero_values_exterior_bound3115
#print axioms reject_low_rung_degree3115
#print axioms reject_zero_frequency_exterior3115
#print axioms negative_frequency_exterior3115
