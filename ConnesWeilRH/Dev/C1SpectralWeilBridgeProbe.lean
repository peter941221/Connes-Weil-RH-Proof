import ConnesWeilRH.Dev.C1SpectralWeil

/-!
# C1SpectralWeilBridgeProbe

Disposable probe verifying the finite-set-sum interleaving needed by
`spectralHeightMultiplicity_le_finiteHeightMultiplicity`.  The main module
stays clean; once these compile the reusable lemmas move back.

The core identity: for a finite `Set s : Set α` and a function `f : α → ℝ`,
with `s.toFinset` the corresponding finset,
  ∑' x : {x // x ∈ s}, f x  =  ∑ x ∈ s.toFinset, f x
-/
namespace ConnesWeilRH
namespace Source
namespace C1SpectralWeil

open scoped BigOperators

theorem tsum_finite_subtype_eq_sum_toFinset {α : Type*} {s : Set α}
    (hs : s.Finite) (f : α → ℝ) (h𝟎 : s.toFinset.Nonempty := by })
    : (∑' x : {x // x ∈ s}, f x) =
        ∑ x ∈ s.toFinset, f x := by
  letI := hs.fintype
  rw [tsum_fintype]
  congr 1
  funext x
  rfl

end C1SpectralWeil
end Source
end ConnesWeilRH