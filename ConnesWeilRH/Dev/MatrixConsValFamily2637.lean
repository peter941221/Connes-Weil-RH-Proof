import Mathlib.Data.Fin.VecNotation

/-!
# Project-local `Matrix.cons_val` family for indices 5-29

Mathlib's `Matrix.cons_val_two` .. `Matrix.cons_val_four` family
(Mathlib/Data/Fin/VecNotation.lean) stops at four. Unfolding
`storedWidth d` (a 30-entry `![...]` literal) inside `norm_num` for
diagonal owners `d >= 5` needs the matching peel lemma. This module
extends the family with the same `vecHead (vecTail^...) := rfl` shape;
the tail reduction is carried by the ambient simp lemmas `head_cons`
and `tail_cons`, exactly as for indices two through four. Names use
digits for uniform generation.
-/

namespace Matrix

variable {α : Type*} {m : ℕ}

theorem cons_val_5 (x : α) (u : Fin m.succ.succ.succ.succ.succ → α) :
    vecCons x u 5 = vecHead (vecTail (vecTail (vecTail (vecTail u)))) :=
  rfl

theorem cons_val_6 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 6 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail u))))) :=
  rfl

theorem cons_val_7 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 7 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u)))))) :=
  rfl

theorem cons_val_8 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 8 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u))))))) :=
  rfl

theorem cons_val_9 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 9 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u)))))))) :=
  rfl

theorem cons_val_10 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 10 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u))))))))) :=
  rfl

theorem cons_val_11 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 11 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u)))))))))) :=
  rfl

theorem cons_val_12 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 12 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u))))))))))) :=
  rfl

theorem cons_val_13 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 13 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u)))))))))))) :=
  rfl

theorem cons_val_14 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 14 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u))))))))))))) :=
  rfl

theorem cons_val_15 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 15 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u)))))))))))))) :=
  rfl

theorem cons_val_16 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 16 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u))))))))))))))) :=
  rfl

theorem cons_val_17 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 17 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u)))))))))))))))) :=
  rfl

theorem cons_val_18 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 18 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u))))))))))))))))) :=
  rfl

theorem cons_val_19 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 19 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u)))))))))))))))))) :=
  rfl

theorem cons_val_20 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 20 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u))))))))))))))))))) :=
  rfl

theorem cons_val_21 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 21 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u)))))))))))))))))))) :=
  rfl

theorem cons_val_22 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 22 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u))))))))))))))))))))) :=
  rfl

theorem cons_val_23 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 23 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u)))))))))))))))))))))) :=
  rfl

theorem cons_val_24 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 24 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u))))))))))))))))))))))) :=
  rfl

theorem cons_val_25 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 25 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u)))))))))))))))))))))))) :=
  rfl

theorem cons_val_26 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 26 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u))))))))))))))))))))))))) :=
  rfl

theorem cons_val_27 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 27 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u)))))))))))))))))))))))))) :=
  rfl

theorem cons_val_28 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 28 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u))))))))))))))))))))))))))) :=
  rfl

theorem cons_val_29 (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    vecCons x u 29 = vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail u)))))))))))))))))))))))))))) :=
  rfl

end Matrix
