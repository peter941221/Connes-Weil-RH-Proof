import ConnesWeilRH.Dev.C1SeedCertificateIntervals3098

/-! A finite witness checker for the actual transition derivatives. Every
rounding enclosure is supplied as rational endpoints and checked by the
kernel. This file proves the checker's meaning before any data are accepted. -/

namespace ConnesWeilRH.Dev.C1SeedCertificate3098

open ConnesWeilRH.Source.C1ExplicitSmoothSeed

structure Certificate where
  k : Nat
  powers : List Box
  exps : List Box
  recips : List Box
  price4 : Nat
  price7 : Nat
  deriving Repr

def slot (xs : List Box) (n : Nat) : Box := xs[n]?.getD (Box.point 0)
def expStep (B : Box) (E : Nat → Box) (n : Nat) : Box :=
  Box.sum (fun j => ((Box.point (n.choose j)).mul (phaseBox B (j + 1))).mul
    (E (n - j))) (n + 1)
def recipStep (E R : Nat → Box) (n : Nat) : Box :=
  ((Box.point 0).sub (Box.sum (fun j =>
    ((Box.point ((n + 1).choose (j + 1))).mul (E (j + 1))).mul (R (n - j)))
      (n + 1))).mul ((Box.point 1).add (E 0)).inv
def productSlot (E R : Nat → Box) (n : Nat) : Box :=
  Box.sum (fun j => ((Box.point (n.choose j)).mul (E j)).mul (R (n - j))) (n + 1)

def Valid (i : Nat) (c : Certificate) : Prop :=
  i < 8192 ∧ 0 < (cell i).lo ∧ (cell i).hi < 1 ∧ (cell i).lo ≤ (cell i).hi ∧
  (phaseBox (cell i) 0).hi ≤ 0 ∧
  -(phaseBox (cell i) 0).lo ≤ (2 : Rat) ^ c.k ∧
  c.powers.length = c.k + 1 ∧ c.exps.length = 8 ∧ c.recips.length = 8 ∧
  (slot c.powers 0).Contains (initialExp (phaseBox (cell i) 0) c.k) ∧
  (∀ j : Fin c.k, (slot c.powers (j.1 + 1)).Contains
    ((slot c.powers j.1).mul (slot c.powers j.1))) ∧
  (slot c.exps 0).Contains (slot c.powers c.k) ∧
  0 < ((Box.point 1).add (slot c.exps 0)).lo ∧
  (slot c.recips 0).Contains ((Box.point 1).add (slot c.exps 0)).inv ∧
  (∀ j : Fin 7, (slot c.exps (j.1 + 1)).Contains
    (expStep (cell i) (slot c.exps) j.1)) ∧
  (∀ j : Fin 7, (slot c.recips (j.1 + 1)).Contains
    (recipStep (slot c.exps) (slot c.recips) j.1)) ∧
  4 * ((cell i).hi - (cell i).lo) *
    (productSlot (slot c.exps) (slot c.recips) 4).absUpper ≤ (c.price4 : Rat) / 4096 ∧
  4 * ((cell i).hi - (cell i).lo) *
    (productSlot (slot c.exps) (slot c.recips) 7).absUpper ≤ (c.price7 : Rat) / 4096

instance (i : Nat) (c : Certificate) : Decidable (Valid i c) := by
  unfold Valid
  infer_instance

def checkCell (i : Nat) (c : Certificate) : Bool := decide (Valid i c)

theorem power_chain_mem (P : Box) (k : Nat) (xs : List Box)
    (hP : P.hi ≤ 0) (hcap : -P.lo ≤ (2 : Rat) ^ k)
    (hfirst : (slot xs 0).Contains (initialExp P k))
    (hstep : ∀ j : Fin k, (slot xs (j.1 + 1)).Contains
      ((slot xs j.1).mul (slot xs j.1)))
    {z : Real} (hz : P.Mem z) : (slot xs k).Mem (Real.exp z) := by
  have h : ∀ n ≤ k, (slot xs n).Mem
      (Real.exp (z / (2 : Real) ^ k) ^ ((2 : Nat) ^ n)) := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa using Box.mem_of_contains hfirst (initialExp_mem P k hP hcap hz)
    | succ n ih =>
      intro hn
      have hm := Box.mem_mul (ih (by omega)) (ih (by omega))
      have hm' := Box.mem_of_contains (hstep ⟨n, by omega⟩) hm
      simpa only [Nat.pow_succ, pow_mul, pow_two] using hm'
  have heq : Real.exp (z / (2 : Real) ^ k) ^ ((2 : Nat) ^ k) = Real.exp z := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  simpa only [heq] using h k le_rfl

theorem valid_product_mem (i : Nat) (c : Certificate) (hv : Valid i c)
    {x : Real} (hx : (cell i).Mem x) :
    ∀ n ≤ 7, (productSlot (slot c.exps) (slot c.recips) n).Mem
      (iteratedDeriv n Real.smoothTransition x) := by
  rcases hv with ⟨hi, hlo, hhi, hord, hP, hcap, hplen, helen, hrlen,
    hp0, hpstep, he0, hden, hr0, hestep, hrstep, hprice4, hprice7⟩
  have hx0 : 0 < x := (show (0 : Real) < (cell i).lo by exact_mod_cast hlo).trans_le hx.1
  have hx1 : x < 1 := hx.2.trans_lt (by exact_mod_cast hhi)
  have hphase (n : Nat) := phaseBox_mem (cell i) n hlo hhi hx
  have hezero : (slot c.exps 0).Mem (transitionExp2731 x) := by
    apply Box.mem_of_contains he0
    apply power_chain_mem _ c.k c.powers hP hcap hp0 hpstep
    simpa only [iteratedDeriv_zero] using hphase 0
  have hE : ∀ n ≤ 7, (slot c.exps n).Mem (iteratedDeriv n transitionExp2731 x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      cases n with
      | zero => simpa only [iteratedDeriv_zero] using hezero
      | succ m =>
        rw [iteratedDeriv_transitionExp2731 m hx0 hx1]
        apply Box.mem_of_contains (hestep ⟨m, by omega⟩)
        apply Box.mem_sum
        intro j hj
        have hslot := Box.mem_mul
          (Box.mem_mul (Box.mem_point (m.choose j : Rat)) (hphase (j + 1)))
          (ih (m - j) (by omega) (by omega))
        simpa only [Rat.cast_natCast] using hslot
  have hdenmem : ((Box.point 1).add (slot c.exps 0)).Mem (1 + transitionExp2731 x) := by
    simpa using Box.mem_add (Box.mem_point 1) hezero
  have hinv := Box.mem_inv hden hdenmem
  have hR : ∀ n ≤ 7, (slot c.recips n).Mem
      (iteratedDeriv n transitionReciprocal2731 x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      cases n with
      | zero =>
        simpa only [iteratedDeriv_zero, transitionReciprocal2731] using
          Box.mem_of_contains hr0 hinv
      | succ m =>
        rw [iteratedDeriv_transitionReciprocal2731 m hx0 hx1]
        apply Box.mem_of_contains (hrstep ⟨m, by omega⟩)
        have hs := Box.mem_sum
          (fun j => ((Box.point ((m + 1).choose (j + 1))).mul
            (slot c.exps (j + 1))).mul (slot c.recips (m - j)))
          (fun j => ((m + 1).choose (j + 1) : Real) *
            iteratedDeriv (j + 1) transitionExp2731 x *
              iteratedDeriv (m - j) transitionReciprocal2731 x) (m + 1) (by
            intro j hj
            have ht := Box.mem_mul
              (Box.mem_mul (Box.mem_point ((m + 1).choose (j + 1) : Rat))
                (hE (j + 1) (by omega))) (ih (m - j) (by omega) (by omega))
            simpa only [Rat.cast_natCast] using ht)
        have hneg := Box.mem_sub (Box.mem_point 0) hs
        simpa only [Rat.cast_zero, zero_sub, div_eq_mul_inv] using Box.mem_mul hneg hinv
  intro n hn
  rw [iteratedDeriv_smoothTransition_product2731 n hx0 hx1]
  apply Box.mem_sum
  intro j hj
  have ht := Box.mem_mul (Box.mem_mul (Box.mem_point (n.choose j : Rat))
    (hE j (by omega))) (hR (n - j) (by omega))
  simpa only [Rat.cast_natCast] using ht

end ConnesWeilRH.Dev.C1SeedCertificate3098
