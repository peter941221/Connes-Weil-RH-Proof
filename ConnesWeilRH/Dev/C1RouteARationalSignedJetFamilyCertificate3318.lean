import ConnesWeilRH.Dev.C1RouteARationalSignedJetFamilyBridge3317

namespace ConnesWeilRH.Dev

open scoped BigOperators

/-
The certificate boundary for an externally generated family endpoint.

`cert` is a rational upper endpoint produced by an independently audited
interval evaluator. The theorem below records exactly what must be supplied
to make that endpoint consumable: a pointwise upper bound for every Lean
family rectangle endpoint. No external JSON is treated as a theorem here.
-/
theorem ratWeightedPhysicalBlockRect3310_reHi_le_of_family_endpoint_certificate
    {order block : ℕ} (hblock : block < 160)
    (cert : ℕ → Fin 30 → ℚ)
    (hcert : ∀ offset ∈ Finset.range 256, ∀ family : Fin 30,
      (ratWeightedPhysicalTermRect3310 order (block * 256 + offset) family).reHi ≤
        cert (block * 256 + offset) family) :
    (ratWeightedPhysicalBlockRect3310 order block).reHi ≤
      ∑ offset ∈ Finset.range 256,
        ∑ family : Fin 30, cert (block * 256 + offset) family := by
  rw [ratWeightedPhysicalBlockRect3310_reHi_eq_family_cell_sum]
  apply Finset.sum_le_sum
  intro offset hoff
  apply Finset.sum_le_sum
  intro family hfamily
  exact hcert offset hoff family

theorem ratWeightedPhysicalBlockRect3310_reHi_le_of_family_sum_certificate
    {order block : ℕ} (hblock : block < 160)
    (familyUpper : ℕ → Fin 30 → ℚ)
    (blockUpper : ℚ)
    (hcert : ∀ offset ∈ Finset.range 256, ∀ family : Fin 30,
      (ratWeightedPhysicalTermRect3310 order (block * 256 + offset) family).reHi ≤
        familyUpper (block * 256 + offset) family)
    (haggregate :
      (∑ offset ∈ Finset.range 256,
        ∑ family : Fin 30, familyUpper (block * 256 + offset) family : ℚ) ≤
        blockUpper) :
    (ratWeightedPhysicalBlockRect3310 order block).reHi ≤ blockUpper := by
  exact le_trans
    (ratWeightedPhysicalBlockRect3310_reHi_le_of_family_endpoint_certificate
      hblock familyUpper hcert)
    haggregate

end ConnesWeilRH.Dev
