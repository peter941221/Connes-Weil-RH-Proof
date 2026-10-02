import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.BigOperators
import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

set_option linter.style.longLine false

/-  2454: one-sided rectangle enlargement.  If a rectangle `a` contains
`z` and the rectangle `b` covers `a` corner-wise, then `b` contains `z`.
This is the generic consumer-side companion of the 2453 norm bridge: a
generator can emit literal outer hulls and transport containment from
computed product rectangles into them without any arithmetic in Lean.
Owner-independent, no numerical data. -/

namespace ConnesWeilRH.Dev

theorem mem_of_rect_subset_2454 {z : ℂ} {a b : ComplexRect2427}
    (h : a.Mem z) (h1 : b.reLo ≤ a.reLo) (h2 : a.reHi ≤ b.reHi)
    (h3 : b.imLo ≤ a.imLo) (h4 : a.imHi ≤ b.imHi) : b.Mem z :=
  ⟨h1.trans h.1, h.2.1.trans h2, h3.trans h.2.2.1, h.2.2.2.trans h4⟩

/-- The 30-term sum over `Fin 30` is the right-associated chain, with
numeral indices.  Generic over an opaque function: keeping `f` abstract
is what lets the simp closing this avoid any array peeling (concrete
summands over definition arrays stall the peeler mid-chain; see record
2454). -/
theorem fin30_sum_univ_chain_2454 {M : Type*} [AddCommMonoid M]
    (f : Fin 30 → M) :
    ∑ i : Fin 30, f i =
      (f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + f 29))))))))))))))))))))))))))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

end ConnesWeilRH.Dev
