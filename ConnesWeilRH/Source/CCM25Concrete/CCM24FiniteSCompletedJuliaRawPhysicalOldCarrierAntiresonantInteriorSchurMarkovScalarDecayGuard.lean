/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurMarkovPairing

/-!
# Literal suffix Schur--Markov scalar decay guard

The existing normalized estimates carry the literal suffix scalar
`suffixEulerSchurMarkovScalar S` on the left.  This file records an exact
quantitative guard against removing that scalar by a uniform division.

The legal visible-prime carrier only requires `1 < p`, so the sequence
`p_n = (n + 2)^2` is available for literal suffix lists.  Its one-step scalar
is `(n + 1) / (n + 3)`, and the prefix product is

```text
2 / ((N + 1) * (N + 2)).
```

Thus the scalar has no positive lower bound on literal suffixes.  This is not
a counterexample to the complete signed physical estimate: it only proves
that the existing scalar-weighted absolute estimate cannot be upgraded by
dividing through `rho_S`.  A genuine Gate 3U producer still has to prove the
same-object signed cancellation before the first absolute value.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantSchurMarkovScalarDecayGuard

open Filter Topology
open CC20Concrete
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
open CCM24FiniteSSchurMarkovPairing

/-! ## A multiplicative law for the literal suffix scalar -/

theorem suffixEulerSchurMarkovScalar_append
    (A B : List CCM24VisiblePrime) :
    suffixEulerSchurMarkovScalar (A ++ B) =
      suffixEulerSchurMarkovScalar A * suffixEulerSchurMarkovScalar B := by
  induction A with
  | nil => simp [suffixEulerSchurMarkovScalar]
  | cons p A ih =>
      simp only [List.cons_append, suffixEulerSchurMarkovScalar]
      rw [ih]
      ring

/-! ## Exact square-sequence factor -/

theorem primeSchurMarkovScalar_canonicalVisiblePrimeSequence
    (n : Nat) :
    primeSchurMarkovScalar (canonicalVisiblePrimeSequence n) =
      ((n : Real) + 1) / ((n : Real) + 3) := by
  have hn : (0 : Real) <= (n : Real) + 2 := by positivity
  simp only [primeSchurMarkovScalar, canonicalVisiblePrimeSequence,
    ccm24PrimeEulerCoefficient, Nat.cast_pow, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hn, Nat.cast_add, Nat.cast_ofNat]
  field_simp
  ring

noncomputable def canonicalVisiblePrimePrefix (N : Nat) :
    List CCM24VisiblePrime :=
  (List.range N).map canonicalVisiblePrimeSequence

theorem suffixEulerSchurMarkovScalar_canonicalVisiblePrimePrefix
    (N : Nat) :
    suffixEulerSchurMarkovScalar (canonicalVisiblePrimePrefix N) =
      2 / (((N : Real) + 1) * ((N : Real) + 2)) := by
  induction N with
  | zero =>
      norm_num [canonicalVisiblePrimePrefix, suffixEulerSchurMarkovScalar]
  | succ N ih =>
      have hprefix :
          canonicalVisiblePrimePrefix (Nat.succ N) =
            canonicalVisiblePrimePrefix N ++
              [canonicalVisiblePrimeSequence N] := by
        simp [canonicalVisiblePrimePrefix, List.range_succ]
      rw [hprefix, suffixEulerSchurMarkovScalar_append, ih]
      simp only [suffixEulerSchurMarkovScalar,
        primeSchurMarkovScalar_canonicalVisiblePrimeSequence]
      push_cast
      field_simp
      ring

/-! ## No uniform positive lower bound -/

theorem exists_canonicalVisiblePrimePrefix_scalar_lt
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ N : Nat,
      suffixEulerSchurMarkovScalar (canonicalVisiblePrimePrefix N) < epsilon := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / epsilon)
  refine ⟨N, ?_⟩
  rw [suffixEulerSchurMarkovScalar_canonicalVisiblePrimePrefix]
  have hNreal : 2 / epsilon < (N : Real) := by
    simpa using hN
  have hNmul : 2 < (N : Real) * epsilon := by
    exact (div_lt_iff₀ hepsilon).mp hNreal
  have hA : 0 < (N : Real) + 1 := by positivity
  have hB : 0 < (N : Real) + 2 := by positivity
  have hAB : 0 < ((N : Real) + 1) * ((N : Real) + 2) :=
    mul_pos hA hB
  have hcompare :
      2 / (((N : Real) + 1) * ((N : Real) + 2)) <=
        2 / ((N : Real) + 1) := by
    apply (div_le_div_iff₀ hAB hA).2
    have hN0 : (0 : Real) ≤ (N : Real) := by positivity
    nlinarith [hN0]
  have hsmall : 2 / ((N : Real) + 1) < epsilon := by
    apply (div_lt_iff₀ hA).2
    nlinarith [hNmul]
  exact hcompare.trans_lt hsmall

end AntiresonantSchurMarkovScalarDecayGuard
end CCM25Concrete
end Source
end ConnesWeilRH
