/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# The canonical finite-S family of a selected Weil square

This module constructs the finite prime-power family used by the CCM24
semilocal carrier from the exact nonzero arithmetic support of the same
selected convolution square.  Prime-power witnesses use the canonical
`minFac`/`factorization` decomposition, so the family does not depend on an
unrelated choice of prime places.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSProjectionTrace
namespace FinitePrimePowerFamily

open SelectedWeilSquare
open ConnesWeilRH.Source.CC20Concrete

/-- The canonical prime/exponent coordinates of a natural number. -/
noncomputable def canonicalTerm (n : ℕ) : ℕ × ℕ :=
  (n.minFac, n.factorization n.minFac)

theorem canonicalTerm_prime {n : ℕ} (hn : IsPrimePow n) :
    (canonicalTerm n).1.Prime := by
  exact Nat.minFac_prime (ne_of_gt hn.one_lt)

theorem canonicalTerm_exponent_ne_zero {n : ℕ} (hn : IsPrimePow n) :
    (canonicalTerm n).2 ≠ 0 := by
  intro hexponent
  have hpow := hn.minFac_pow_factorization_eq
  rw [show n.factorization n.minFac = 0 by
    simpa [canonicalTerm] using hexponent, pow_zero] at hpow
  exact (ne_of_gt hn.one_lt) hpow.symm

theorem canonicalTerm_pow_eq {n : ℕ} (hn : IsPrimePow n) :
    (canonicalTerm n).1 ^ (canonicalTerm n).2 = n := by
  simpa [canonicalTerm] using hn.minFac_pow_factorization_eq

/-- Build the finite prime-power family from exact support belonging to the
same selected Weil square. -/
noncomputable def ofSelectedExactSupport
    (owner : SelectedWeilSquareOwner)
    (support : SelectedFinitePrimeSupportData owner) :
    FinitePrimePowerFamily where
  terms := support.globalPrimeIndexSet.attach.image fun n => canonicalTerm n.1
  prime := by
    intro pm hpm
    rw [Finset.mem_image] at hpm
    obtain ⟨n, -, rfl⟩ := hpm
    exact canonicalTerm_prime ((support.globalExact n.1).mp n.2).1
  exponent_ne_zero := by
    intro pm hpm
    rw [Finset.mem_image] at hpm
    obtain ⟨n, -, rfl⟩ := hpm
    exact canonicalTerm_exponent_ne_zero ((support.globalExact n.1).mp n.2).1

/-- A selected compact square canonically determines the prime-power family
used by its semilocal CCM24 carrier. -/
noncomputable def ofSelectedOwner (owner : SelectedWeilSquareOwner) :
    FinitePrimePowerFamily :=
  ofSelectedExactSupport owner (SelectedFinitePrimeSupportData.ofOwner owner)

theorem exists_mem_ofSelectedExactSupport_pow_eq_iff
    (owner : SelectedWeilSquareOwner)
    (support : SelectedFinitePrimeSupportData owner) (n : ℕ) :
    (∃ pm ∈ (ofSelectedExactSupport owner support).terms,
        pm.1 ^ pm.2 = n) ↔
      n ∈ support.globalPrimeIndexSet := by
  constructor
  · rintro ⟨pm, hpm, hpmpow⟩
    change pm ∈
      support.globalPrimeIndexSet.attach.image
        (fun k => canonicalTerm k.1) at hpm
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hpm
    have hkprime : IsPrimePow k.1 :=
      ((support.globalExact k.1).mp k.2).1
    have hkn : k.1 = n :=
      (canonicalTerm_pow_eq hkprime).symm.trans hpmpow
    exact hkn ▸ k.2
  · intro hn
    have hnprime : IsPrimePow n := ((support.globalExact n).mp hn).1
    refine ⟨canonicalTerm n, ?_, canonicalTerm_pow_eq hnprime⟩
    change canonicalTerm n ∈
      support.globalPrimeIndexSet.attach.image
        (fun k => canonicalTerm k.1)
    exact Finset.mem_image.mpr
      ⟨⟨n, hn⟩, Finset.mem_attach _ _, rfl⟩

/-- The powered indices of the canonical family are exactly the selected
square's nonzero prime-power atoms. -/
theorem exists_mem_ofSelectedOwner_pow_eq_iff
    (owner : SelectedWeilSquareOwner) (n : ℕ) :
    (∃ pm ∈ (ofSelectedOwner owner).terms, pm.1 ^ pm.2 = n) ↔
      IsPrimePow n ∧ owner.finitePrimeTerm n ≠ 0 := by
  exact
    (exists_mem_ofSelectedExactSupport_pow_eq_iff owner
      (SelectedFinitePrimeSupportData.ofOwner owner) n).trans
      ((SelectedFinitePrimeSupportData.ofOwner owner).globalExact n)

theorem finitePrimeTerm_pow_ne_zero_of_mem_ofSelectedOwner
    (owner : SelectedWeilSquareOwner) {pm : ℕ × ℕ}
    (hpm : pm ∈ (ofSelectedOwner owner).terms) :
    owner.finitePrimeTerm (pm.1 ^ pm.2) ≠ 0 := by
  exact
    (exists_mem_ofSelectedOwner_pow_eq_iff owner (pm.1 ^ pm.2)).mp
      ⟨pm, hpm, rfl⟩ |>.2

theorem exists_nonzero_primePower_of_mem_visiblePrimes_ofSelectedOwner
    (owner : SelectedWeilSquareOwner) {p : CCM24VisiblePrime}
    (hp : p ∈ (ofSelectedOwner owner).visiblePrimes) :
    ∃ m, owner.finitePrimeTerm (p.1 ^ m) ≠ 0 := by
  obtain ⟨m, hm⟩ :=
    (ofSelectedOwner owner).exists_term_of_mem_visiblePrimes hp
  exact ⟨m, finitePrimeTerm_pow_ne_zero_of_mem_ofSelectedOwner owner hm⟩

/-- Every canonical visible prime is bounded by the compact support cutoff of
the same selected square. -/
theorem visiblePrime_lt_globalIndexBound_ofSelectedOwner
    (owner : SelectedWeilSquareOwner) {p : CCM24VisiblePrime}
    (hp : p ∈ (ofSelectedOwner owner).visiblePrimes) :
    p.1 < owner.globalIndexBound := by
  let family := ofSelectedOwner owner
  obtain ⟨m, hm⟩ := family.exists_term_of_mem_visiblePrimes hp
  have hm0 : m ≠ 0 := family.exponent_ne_zero (p.1, m) hm
  have hpprime : p.1.Prime := family.prime (p.1, m) hm
  have hprimepow : IsPrimePow (p.1 ^ m) :=
    ⟨p.1, m, hpprime.prime, Nat.pos_of_ne_zero hm0, rfl⟩
  have hterm : owner.finitePrimeTerm (p.1 ^ m) ≠ 0 :=
    finitePrimeTerm_pow_ne_zero_of_mem_ofSelectedOwner owner hm
  exact (Nat.le_pow (Nat.pos_of_ne_zero hm0)).trans_lt
    (owner.index_lt_globalIndexBound hprimepow hterm)

theorem minFac_mem_visiblePrimes_of_finitePrimeTerm_ne_zero
    (owner : SelectedWeilSquareOwner) {n : ℕ}
    (hnprime : IsPrimePow n) (hnterm : owner.finitePrimeTerm n ≠ 0) :
    (⟨n.minFac, (Nat.minFac_prime (ne_of_gt hnprime.one_lt)).one_lt⟩ :
        CCM24VisiblePrime) ∈
      (ofSelectedOwner owner).visiblePrimes := by
  have hn :
      n ∈ (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet :=
    ((SelectedFinitePrimeSupportData.ofOwner owner).globalExact n).mpr
      ⟨hnprime, hnterm⟩
  have hterm : canonicalTerm n ∈ (ofSelectedOwner owner).terms := by
    change canonicalTerm n ∈
      (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet.attach.image
        (fun k => canonicalTerm k.1)
    exact Finset.mem_image.mpr
      ⟨⟨n, hn⟩, Finset.mem_attach _ _, rfl⟩
  simpa [canonicalTerm] using
    (ofSelectedOwner owner).mem_visiblePrimes_of_mem hterm

end FinitePrimePowerFamily
end CCM24FiniteSProjectionTrace
end CCM25Concrete
end Source
end ConnesWeilRH
