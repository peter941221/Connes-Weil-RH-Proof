/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection7Lemma10

/-!
# The Bombieri (7.3) normalized kernel `H` and its symmetry

Section 7 of Bombieri's memoir (book p.203, design record
`docs/proofs/1043` section 6y) normalizes the corrected kernel by the
positive weight of its right index:

```
(7.3)  H(x,y;t) = 2 t K*(x,y;t) / (1/4 + y^2)
```

The normalization exists precisely to symmetrize: by the (7.1) symmetry
law `(1/4 + x^2) K*(x,y;t) = (1/4 + y^2) K*(y,x;t)`, the weighted forms
of `K*` agree, and multiplying that law by `2 t` turns the (7.3)
readbacks on both sides into

```
H(x,y;t) = H(y,x;t)
```

so `H` is a fully symmetric kernel — the matrix `H(Gamma;t)` of (7.4)
is symmetric, which is the entrance for the eigenvalue sign count
(Theorem 8 / Lemma 10).  This leaf records the definition, the (7.3)
readback `bombieriH_mul_weight_eq`, and the flagship symmetry
`bombieriH_symmetric`.

No numerical datum enters any leaf: only exact identities are proven.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection7H

open ConnesWeilRH.Source.C1BombieriSection7Readback
open ConnesWeilRH.Source.C1BombieriSection7Symmetry

/-- The normalized kernel of (7.3): `H(x,y;t) = 2 t K*(x,y;t) / (1/4 + y^2)`.
The weight `1/4 + y^2` is a strictly positive real, so the division is
always defined. -/
noncomputable def bombieriH (x y t : Real) : Complex :=
  ((2 * t : Real) : Complex) * bombieriKstar x y t
    / ((1 / 4 + y ^ 2 : Real) : Complex)

/-- The weights are strictly positive reals. -/
private theorem weight_pos (c : Real) : (0 : Real) < 1 / 4 + c ^ 2 := by
  have h1 : (0 : Real) < 1 / 4 := by norm_num
  have h2 : (1 : Real) / 4 <= 1 / 4 + c ^ 2 := by
    linarith [sq_nonneg c]
  exact lt_of_lt_of_le h1 h2

/-- The weight cast is nonzero. -/
private theorem weightCast_ne (c : Real) :
    ((1 / 4 + c ^ 2 : Real) : Complex) ≠ 0 := by
  intro h0
  have h1 : (1 / 4 + c ^ 2 : Real) = 0 := Complex.ofReal_eq_zero.mp h0
  have h2 : (0 : Real) < 1 / 4 + c ^ 2 := weight_pos c
  rw [h1] at h2
  exact lt_irrefl (0 : Real) h2

/-- The (7.3) readback: the weight times `H` is `2 t K*`. -/
theorem bombieriH_mul_weight_eq (x y t : Real) :
    ((1 / 4 + y ^ 2 : Real) : Complex) * bombieriH x y t
      = ((2 * t : Real) : Complex) * bombieriKstar x y t := by
  unfold bombieriH
  rw [← mul_div_assoc (((1 / 4 + y ^ 2 : Real) : Complex))
      ((((2 * t : Real) : Complex) * bombieriKstar x y t))
      (((1 / 4 + y ^ 2 : Real) : Complex)),
    mul_div_cancel_left₀ ((((2 * t : Real) : Complex) * bombieriKstar x y t))
      (weightCast_ne y)]

/-- The normalization of (7.3) makes the kernel fully symmetric. -/
theorem bombieriH_symmetric (x y t : Real) (ht : t ≠ 0) (hxy : x ≠ y) :
    bombieriH x y t = bombieriH y x t := by
  have hwx := weightCast_ne x
  have hwy := weightCast_ne y
  have e1 := bombieriH_mul_weight_eq x y t
  have e2 := bombieriH_mul_weight_eq y x t
  -- The (7.1) symmetry law, restated from its `binop%` complex-ambient
  -- weight form into single real-cast weights.
  have hsym := bombieriKstar_symmetric x y t ht hxy
  have hcx : (1 / 4 + x ^ 2 : Complex) = ((1 / 4 + x ^ 2 : Real) : Complex) := by
    rw [← Complex.ofReal_pow]
    push_cast
    ring
  have hcy : (1 / 4 + y ^ 2 : Complex) = ((1 / 4 + y ^ 2 : Real) : Complex) := by
    rw [← Complex.ofReal_pow]
    push_cast
    ring
  rw [hcx, hcy] at hsym
  -- The symmetry law multiplied by `2 t`, bracketed so the readbacks grab it.
  have hM : ((2 * t : Real) : Complex)
      * (((1 / 4 + x ^ 2 : Real) : Complex) * bombieriKstar x y t)
      = ((2 * t : Real) : Complex)
        * (((1 / 4 + y ^ 2 : Real) : Complex) * bombieriKstar y x t) :=
    congrArg (fun z : Complex => ((2 * t : Real) : Complex) * z) hsym
  -- Both weights times both values of `H` agree; cancel the nonzero product.
  have m1 : ((1 / 4 + x ^ 2 : Real) : Complex)
      * (((1 / 4 + y ^ 2 : Real) : Complex) * bombieriH x y t)
      = ((1 / 4 + y ^ 2 : Real) : Complex)
        * (((1 / 4 + x ^ 2 : Real) : Complex) * bombieriH y x t) := by
    rw [e1, e2,
      mul_left_comm (((1 / 4 + x ^ 2 : Real) : Complex))
        (((2 * t : Real) : Complex)) (bombieriKstar x y t),
      mul_left_comm (((1 / 4 + y ^ 2 : Real) : Complex))
        (((2 * t : Real) : Complex)) (bombieriKstar y x t)]
    exact hM
  rw [← mul_assoc (((1 / 4 + x ^ 2 : Real) : Complex))
      (((1 / 4 + y ^ 2 : Real) : Complex)) (bombieriH x y t),
    ← mul_assoc (((1 / 4 + y ^ 2 : Real) : Complex))
      (((1 / 4 + x ^ 2 : Real) : Complex)) (bombieriH y x t),
    mul_comm (((1 / 4 + y ^ 2 : Real) : Complex))
      (((1 / 4 + x ^ 2 : Real) : Complex))] at m1
  exact mul_right_injective₀ (mul_ne_zero hwx hwy) m1

end C1BombieriSection7H
end Source
end ConnesWeilRH
