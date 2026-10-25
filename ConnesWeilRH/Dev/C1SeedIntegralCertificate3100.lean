import ConnesWeilRH.Dev.C1SeedCellCertificate3099
import ConnesWeilRH.Dev.C1D4D7EndpointCharges2756

namespace ConnesWeilRH.Dev.C1SeedCertificate3098

open MeasureTheory
open ConnesWeilRH.Source.C1ExplicitSmoothSeed

def endpoint (i : Nat) : Real := (cell i).lo

theorem cell_hi_eq_endpoint (i : Nat) : ((cell i).hi : Real) = endpoint (i + 1) := by
  simp [endpoint, cell]
def price (c : Certificate) (n : Nat) : Nat := if n = 4 then c.price4 else c.price7
def totalPrice (cs : List Certificate) (n : Nat) : Nat := (cs.map (fun c => price c n)).sum
def checkCells : Nat → List Certificate → Bool
  | _, [] => true
  | i, c :: cs => checkCell i c && checkCells (i + 1) cs

theorem checkCells_append (xs ys : List Certificate) (i : Nat) :
    checkCells i (xs ++ ys) = (checkCells i xs && checkCells (i + xs.length) ys) := by
  induction xs generalizing i with
  | nil => simp [checkCells]
  | cons c cs ih => simp [checkCells, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Bool.and_assoc]

theorem totalPrice_append (xs ys : List Certificate) (n : Nat) :
    totalPrice (xs ++ ys) n = totalPrice xs n + totalPrice ys n := by
  simp [totalPrice]

theorem valid_price (i : Nat) (c : Certificate) (hv : Valid i c)
    (n : Nat) (hn : n = 4 ∨ n = 7) :
    4 * ((cell i).hi - (cell i).lo) *
      (productSlot (slot c.exps) (slot c.recips) n).absUpper ≤ (price c n : Rat) / 4096 := by
  rcases hv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4, h7⟩
  rcases hn with rfl | rfl
  · simpa [price] using h4
  · simpa [price] using h7

theorem cell_integral_le_price (i : Nat) (c : Certificate) (hv : Valid i c)
    (n : Nat) (hn : n = 4 ∨ n = 7) :
    4 * (∫ x in (endpoint i)..(endpoint (i + 1)),
      ‖iteratedDeriv n Real.smoothTransition x‖) ≤ (price c n : Real) / 4096 := by
  let U : Real := (productSlot (slot c.exps) (slot c.recips) n).absUpper
  have hc : Continuous (fun x : Real => ‖iteratedDeriv n Real.smoothTransition x‖) :=
    continuous_norm.comp (contDiff_one_iteratedDeriv_smoothTransition n).continuous
  have hab : endpoint i ≤ endpoint (i + 1) := by
    rw [← cell_hi_eq_endpoint]
    change ((cell i).lo : Real) ≤ (cell i).hi
    exact_mod_cast hv.2.2.2.1
  have hbound (x : Real) (hx : x ∈ Set.Ioo (endpoint i) (endpoint (i + 1))) :
      ‖iteratedDeriv n Real.smoothTransition x‖ ≤ U := by
    apply Box.norm_le_absUpper (valid_product_mem i c hv ?_ n (by omega))
    exact ⟨hx.1.le, by simpa only [cell_hi_eq_endpoint] using hx.2.le⟩
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) hab
    (hc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _) hbound
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  calc
    4 * (∫ x in (endpoint i)..(endpoint (i + 1)),
        ‖iteratedDeriv n Real.smoothTransition x‖) ≤
        4 * ((endpoint (i + 1) - endpoint i) * U) :=
      mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ ≤ (price c n : Real) / 4096 := by
      have h := valid_price i c hv n hn
      have hR : 4 * (((cell i).hi : Real) - (cell i).lo) * U ≤
          (price c n : Real) / 4096 := by
        have hcast := (Rat.cast_le (K := Real)).mpr h
        push_cast at hcast
        exact hcast
      simpa only [cell_hi_eq_endpoint, endpoint, mul_assoc] using hR

theorem checked_cells_integral_le (i : Nat) (cs : List Certificate)
    (hcheck : checkCells i cs = true) (n : Nat) (hn : n = 4 ∨ n = 7) :
    4 * (∫ x in (endpoint i)..(endpoint (i + cs.length)),
      ‖iteratedDeriv n Real.smoothTransition x‖) ≤ (totalPrice cs n : Real) / 4096 := by
  induction cs generalizing i with
  | nil => simp [totalPrice]
  | cons c cs ih =>
    have hparts : checkCell i c = true ∧ checkCells (i + 1) cs = true := by
      simpa only [checkCells, Bool.and_eq_true] using hcheck
    have hv : Valid i c := of_decide_eq_true hparts.1
    have hfirst := cell_integral_le_price i c hv n hn
    have hrest := ih (i + 1) hparts.2
    have hc : Continuous (fun x : Real => ‖iteratedDeriv n Real.smoothTransition x‖) :=
      continuous_norm.comp (contDiff_one_iteratedDeriv_smoothTransition n).continuous
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable (endpoint i) (endpoint (i + 1)))
      (hc.intervalIntegrable (endpoint (i + 1)) (endpoint (i + 1 + cs.length)))
    have hend : i + (c :: cs).length = i + 1 + cs.length := by simp; omega
    rw [hend, ← hsplit, mul_add]
    simpa [totalPrice, Nat.cast_add, add_div] using add_le_add hfirst hrest

theorem endpoint_zero : endpoint 0 = (1 : Real) / 4096 := by norm_num [endpoint, cell]
theorem endpoint_last : endpoint 8192 = (1 : Real) / 2 := by norm_num [endpoint, cell]

theorem checked_full_integral_lt (cs : List Certificate) (hlen : cs.length = 8192)
    (hcheck : checkCells 0 cs = true) (n : Nat) (hn : n = 4 ∨ n = 7)
    (target : Nat) (hprice : totalPrice cs n + 4096 < target * 4096) :
    4 * (∫ x in (0 : Real)..(1 / 2), ‖iteratedDeriv n Real.smoothTransition x‖) < target := by
  have hcore := checked_cells_integral_le 0 cs hcheck n hn
  rw [hlen, Nat.zero_add, endpoint_zero, endpoint_last] at hcore
  have hend : 4 * (∫ x in (0 : Real)..(1 / 4096),
      ‖iteratedDeriv n Real.smoothTransition x‖) < 1 := by
    rcases hn with rfl | rfl
    · exact lt_of_le_of_lt d4d7_endpoint_integral_charges2756.1
        (lt_trans d4d7_endpoint_integral_charges_tiny2756.1 (by
          exact (div_lt_one (by positivity)).mpr (one_lt_pow₀ (by norm_num) (by norm_num))))
    · exact lt_of_le_of_lt d4d7_endpoint_integral_charges2756.2
        (lt_trans d4d7_endpoint_integral_charges_tiny2756.2 (by
          exact (div_lt_one (by positivity)).mpr (one_lt_pow₀ (by norm_num) (by norm_num))))
  have hc : Continuous (fun x : Real => ‖iteratedDeriv n Real.smoothTransition x‖) :=
    continuous_norm.comp (contDiff_one_iteratedDeriv_smoothTransition n).continuous
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (0 : Real) (1 / 4096))
    (hc.intervalIntegrable (1 / 4096 : Real) (1 / 2))
  have hpriceR : (totalPrice cs n : Real) / 4096 + 1 < (target : Real) := by
    have hR : (totalPrice cs n : Real) + 4096 < (target : Real) * 4096 := by
      exact_mod_cast hprice
    linarith
  rw [← hsplit, mul_add]
  linarith

end ConnesWeilRH.Dev.C1SeedCertificate3098
