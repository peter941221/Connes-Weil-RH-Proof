import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/- RED-9 scratch 1: does `rfl` close the integer grounding shape?
Mini cutoff-4 system over Q = 2^3 * 3! = 48, inner Finset.range 4,
zCoeff = if i < 4 then (-1)^i * 2^(3-i) * (6/i!) else 0.
Layer 1 = [48, -24, 6, -1, 0, 0, 0, 0]
Layer 2 = [2304, -2304, 1152, -384, 84, -12, 1, 0]
A wrong table MUST fail (proves rfl really evaluates). -/

def zCoeffS (i : ℕ) : ℤ :=
  if i < 4 then
    ((-1 : ℤ) ^ i * (2 : ℤ) ^ (3 - i) *
      ((Nat.factorial 3 / i.factorial : ℕ) : ℤ))
  else 0

def zLayerListS : ℕ → List ℤ
  | 0 => (List.range 8).map fun k => if k = 0 then 1 else 0
  | m + 1 =>
      (List.range 8).map fun k => ∑ i ∈ Finset.range 4,
        if i ≤ k then List.getD (zLayerListS m) (k - i) 0 *
          zCoeffS i else 0

def zTableS0 : List ℤ := [1, 0, 0, 0, 0, 0, 0, 0]

def zTableS1 : List ℤ := [48, -24, 6, -1, 0, 0, 0, 0]

def zTableS2 : List ℤ := [2304, -2304, 1152, -384, 84, -12, 1, 0]

theorem zGroundS0 : zLayerListS 0 = zTableS0 := by rfl

theorem zGroundS1 :
    zLayerListS 1 = zTableS1 := by
  show ((List.range 8).map fun k => ∑ i ∈ Finset.range 4,
      if i ≤ k then List.getD (zLayerListS 0) (k - i) 0 * zCoeffS i else 0)
    = zTableS1
  rw [zGroundS0]
  rfl

theorem zGroundS2 :
    zLayerListS 2 = zTableS2 := by
  show ((List.range 8).map fun k => ∑ i ∈ Finset.range 4,
      if i ≤ k then List.getD (zLayerListS 1) (k - i) 0 * zCoeffS i else 0)
    = zTableS2
  rw [zGroundS1]
  rfl

-- negative control: one WRONG entry must fail to close
-- (commented out; flip a digit to re-run the falsifier)
-- theorem zGroundS2_bad : zLayerListS 2 = [2305, -2304, 1152, -384, 84, -12, 1, 0] := by
--   rfl
