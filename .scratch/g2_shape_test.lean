import Mathlib

/- RED-6 tactic-shape scratch: validates show/rw/simp only/norm_num chain
   on an 8-entry, 2-layer analogue of the grounding design.  NOT committed. -/

def tcQ (k : ℕ) : ℚ :=
  if k < 4 then ((-(2 / 35 : ℚ)) ^ k) / (k.factorial : ℚ) else 0

def lcQ (xs : List ℚ) (k : ℕ) : ℚ := List.getD xs k 0

def zeroL : List ℚ := (List.range 8).map fun k => if k = 0 then 1 else 0

def powerL : ℕ → List ℚ
  | 0 => zeroL
  | n + 1 =>
      let prev := powerL n
      (List.range 8).map fun k =>
        ∑ i ∈ Finset.range 4, if i ≤ k then lcQ prev (k - i) * tcQ i else 0

section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000000

private theorem range_8_lit : (List.range 8 : List Nat) = [0, 1, 2, 3, 4, 5, 6, 7] := by
  decide

private def g0 : List ℚ := [1, 0, 0, 0, 0, 0, 0, 0]

private theorem g0_eq : zeroL = g0 := by rfl

private def g1 : List ℚ :=
  [1, (-2 / 35), (2 / 1225), (-4 / 128625), 0, 0, 0, 0]

private theorem g1_eq : powerL 1 = g1 := by
  show ((List.range 8).map fun k => ∑ i ∈ Finset.range 4,
      if i ≤ k then lcQ zeroL (k - i) * tcQ i else 0) = g1
  rw [g0_eq]
  simp only [range_8_lit, g0, g1]
  norm_num (config := { maxSteps := 20000000 })
    [lcQ, tcQ, Finset.sum_range_succ, Finset.sum_empty,
    List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]

private def g2 : List ℚ :=
  [1, (-4 / 35), (8 / 1225), (-32 / 128625), (4 / 643125), (-16 / 157565625),
    (16 / 16544390625), 0]

private theorem g2_eq : powerL 2 = g2 := by
  show ((List.range 8).map fun k => ∑ i ∈ Finset.range 4,
      if i ≤ k then lcQ (powerL 1) (k - i) * tcQ i else 0) = g2
  rw [g1_eq]
  simp only [range_8_lit, g1, g2]
  norm_num (config := { maxSteps := 20000000 })
    [lcQ, tcQ, Finset.sum_range_succ, Finset.sum_empty,
    List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]

-- checkpoint-style consumer: single sum over the top layer
example : (∑ k ∈ Finset.range 8, lcQ (powerL 2) k) = (14757633361 / 16544390625) := by
  have h2 := g2_eq
  simp only [h2, g2, lcQ, Finset.sum_range_succ, Finset.sum_empty,
    List.getD_cons_zero, List.getD_cons_succ]
  norm_num (config := { maxSteps := 20000000 })

end

/- per-index value-theorem machinery: endpoint step helper + chained
   per-index equations + moment adapter (mini scale: indices 0..3) -/

def epQ2 : ℕ → ℚ
  | 0 => 2 * (97 / 100)
  | 1 => 0
  | k + 2 =>
      (97 / 100) / (((k : ℚ) + 1) * (1 - (97 / 100) ^ 2) ^ (k + 1)) +
        ((2 * (k : ℚ) + 1) / (2 * ((k : ℚ) + 1))) * epQ2 (k + 1)

def moQ2 : ℕ → ℚ
  | 0 => 2 * (97 / 100) ^ 3 / 3
  | k + 1 => epQ2 (k + 1) - epQ2 k

private theorem epQ2_step (n : ℕ) :
    epQ2 (n + 1 + 1) =
      (97 / 100) / (((n : ℚ) + 1) * (1 - (97 / 100) ^ 2) ^ (n + 1)) +
        ((2 * (n : ℚ) + 1) / (2 * ((n : ℚ) + 1))) * epQ2 (n + 1) := by
  rw [epQ2]

private theorem epQ2_at_0 : epQ2 0 = (97 / 50) := by
  norm_num [epQ2]

private theorem epQ2_at_1 : epQ2 1 = 0 := by
  rfl

private theorem epQ2_at_2 : epQ2 2 = (9700 / 591) := by
  show epQ2 (0 + 1 + 1) = _
  rw [epQ2_step]
  rw [epQ2_at_1]
  norm_num

private theorem epQ2_at_3 : epQ2 3 = (52799525 / 349281) := by
  show epQ2 (1 + 1 + 1) = _
  rw [epQ2_step]
  rw [epQ2_at_2]
  norm_num

private theorem moQ2_step (n : ℕ) : moQ2 (n + 1) = epQ2 (n + 1) - epQ2 n := by
  rw [moQ2]

private theorem moQ2_at_0 : moQ2 0 = 2 * (97 / 100) ^ 3 / 3 := by
  rfl

private theorem moQ2_at_1 : moQ2 1 = (-(97 / 50)) := by
  show moQ2 (0 + 1) = _
  rw [moQ2_step]
  rw [epQ2_at_1, epQ2_at_0]
  norm_num

-- consumer: sum over per-index lemmas (checkpoint shape)
example : (∑ k ∈ Finset.range 4, epQ2 k) =
    (2960491507 / 17464050) := by
  simp (config := { maxSteps := 20000000 }) only [Finset.sum_range_succ,
    Finset.sum_empty, epQ2_at_0, epQ2_at_1, epQ2_at_2, epQ2_at_3]
  norm_num (config := { maxSteps := 20000000 })
