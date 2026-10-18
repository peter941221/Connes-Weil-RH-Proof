namespace ConnesWeilRH.Dev

noncomputable section

/-! Arithmetic interface for the proposed D4 sign-partition route.

The three variation bounds are intentionally explicit inputs.  This file does
not yet prove that they bound the analytic fourth derivative; that bridge is
the next analytic obligation.
-/

def routeBD4VariationA2869 : ℝ := 111
def routeBD4VariationB2869 : ℝ := 167
def routeBD4VariationC2869 : ℝ := 40

def routeBD4SignPartitionCharge2869 : ℝ :=
  4 * (routeBD4VariationA2869 + routeBD4VariationB2869 +
    routeBD4VariationC2869)

theorem routeBD4SignPartitionCharge_lt_target2869 :
    routeBD4SignPartitionCharge2869 < 1500 := by
  norm_num [routeBD4SignPartitionCharge2869, routeBD4VariationA2869,
    routeBD4VariationB2869, routeBD4VariationC2869]

end
end ConnesWeilRH.Dev
