/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CompactApproximateKernel

/-!
# Compact-observable witness for the carrier base

The carrier base is a kernel/non-kernel question for a Hardy-Toeplitz
operator.  Finite sections only produce bounded approximate kernels, so the
missing compactness step must rule out weak escape.  The existing source
lemma says that an injective operator sends every compact observable of such a
sequence to zero.  This leaf exposes the contrapositive as the exact producer
interface consumed by the carrier base: a single compact observable that does
not vanish along a bounded approximate-kernel sequence forces a nontrivial
kernel.

No concrete Toeplitz sequence or compact observable is supplied here.  The
analytic producer remains open; this is the non-circular consumer interface.
-/

namespace ConnesWeilRH
namespace Dev

open Filter Function Set Topology
open Source
open Source.CC20Concrete
open Source.CC20Concrete.CompactApproximateKernel
open scoped InnerProductSpace

variable {H G J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- A compact observable that survives along a bounded approximate kernel
sequence is incompatible with injectivity of the kernel operator. -/
theorem not_injective_of_compact_observable_survives_approximate_kernel
    (D : H →L[ℂ] G) (K : H →L[ℂ] J)
    (hK : IsCompactOperator K)
    (x : ℕ → H)
    (hbounded : Bornology.IsBounded (Set.range x))
    (hzero : Tendsto (fun n ↦ D (x n)) atTop (nhds 0))
    (hsurvives : ¬ Tendsto (fun n ↦ K (x n)) atTop (nhds 0)) :
    ¬ Function.Injective D := by
  intro hD
  exact hsurvives
    (compact_output_tendsto_zero_of_injective_approximate_kernel
      D K hD hK x hbounded hzero)

/-- The non-injectivity conclusion is exactly a nonzero kernel vector. -/
theorem exists_ne_zero_mem_kernel_of_compact_observable_survives_approximate_kernel
    (D : H →L[ℂ] G) (K : H →L[ℂ] J)
    (hK : IsCompactOperator K)
    (x : ℕ → H)
    (hbounded : Bornology.IsBounded (Set.range x))
    (hzero : Tendsto (fun n ↦ D (x n)) atTop (nhds 0))
    (hsurvives : ¬ Tendsto (fun n ↦ K (x n)) atTop (nhds 0)) :
    ∃ y : H, y ≠ 0 ∧ D y = 0 := by
  have hnot : ¬ Function.Injective D :=
    not_injective_of_compact_observable_survives_approximate_kernel
      D K hK x hbounded hzero hsurvives
  by_contra h
  apply hnot
  intro a b hab
  by_contra hne
  apply h
  refine ⟨a - b, sub_ne_zero.mpr hne, ?_⟩
  rw [map_sub, hab, sub_self]

end Dev
end ConnesWeilRH
