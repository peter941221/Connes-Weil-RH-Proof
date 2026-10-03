import ConnesWeilRH.Dev.C1RouteAKernelN10239Minus2555
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def sharedN10239MinusPosition2556 : ℝ := ((335478789119 : ℝ) /
        51200000000)

def sharedN10239MinusP000Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP000Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP000Output2556.1‖ ≤ (sharedN10239MinusP000Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP000BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP000Output2556,
    kernelN10239MinusP000Center2555, kernelN10239MinusP000Error2555, embedPair2542]

theorem sharedN10239MinusP000Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP000Output2556.1) + embedPair2542
            sharedN10239MinusP000Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP000Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP000Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP000Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP000Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP000Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP000Output2556, pairMagnitude2542]

def sharedN10239MinusP001Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP001Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP001Output2556.1‖ ≤ (sharedN10239MinusP001Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP001BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP001Output2556,
    kernelN10239MinusP001Center2555, kernelN10239MinusP001Error2555, embedPair2542]

theorem sharedN10239MinusP001Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP001Output2556.1) + embedPair2542
            sharedN10239MinusP001Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP001Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP001Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP001Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP001Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP001Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP001Output2556, pairMagnitude2542]

def sharedN10239MinusP002Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP002Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP002Output2556.1‖ ≤ (sharedN10239MinusP002Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP002BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP002Output2556,
    kernelN10239MinusP002Center2555, kernelN10239MinusP002Error2555, embedPair2542]

theorem sharedN10239MinusP002Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP002Output2556.1) + embedPair2542
            sharedN10239MinusP002Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP002Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP002Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP002Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP002Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP002Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP002Output2556, pairMagnitude2542]

def sharedN10239MinusP003Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP003Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP003Output2556.1‖ ≤ (sharedN10239MinusP003Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP003BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP003Output2556,
    kernelN10239MinusP003Center2555, kernelN10239MinusP003Error2555, embedPair2542]

theorem sharedN10239MinusP003Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP003Output2556.1) + embedPair2542
            sharedN10239MinusP003Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP003Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP003Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP003Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP003Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP003Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP003Output2556, pairMagnitude2542]

def sharedN10239MinusP004Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN10239MinusP004Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP004Output2556.1‖ ≤ (sharedN10239MinusP004Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP004BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP004Output2556,
    kernelN10239MinusP004Center2555, kernelN10239MinusP004Error2555, embedPair2542]

theorem sharedN10239MinusP004Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP004Output2556.1) + embedPair2542
            sharedN10239MinusP004Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP004Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP004Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP004Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP004Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP004Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP004Output2556, pairMagnitude2542]

def sharedN10239MinusP005Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP005Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP005Output2556.1‖ ≤ (sharedN10239MinusP005Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP005BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP005Output2556,
    kernelN10239MinusP005Center2555, kernelN10239MinusP005Error2555, embedPair2542]

theorem sharedN10239MinusP005Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP005Output2556.1) + embedPair2542
            sharedN10239MinusP005Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP005Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP005Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP005Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP005Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP005Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP005Output2556, pairMagnitude2542]

def sharedN10239MinusP006Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP006Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP006Output2556.1‖ ≤ (sharedN10239MinusP006Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP006BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP006Output2556,
    kernelN10239MinusP006Center2555, kernelN10239MinusP006Error2555, embedPair2542]

theorem sharedN10239MinusP006Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP006Output2556.1) + embedPair2542
            sharedN10239MinusP006Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP006Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP006Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP006Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP006Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP006Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP006Output2556, pairMagnitude2542]

def sharedN10239MinusP007Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP007Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP007Output2556.1‖ ≤ (sharedN10239MinusP007Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP007BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP007Output2556,
    kernelN10239MinusP007Center2555, kernelN10239MinusP007Error2555, embedPair2542]

theorem sharedN10239MinusP007Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP007Output2556.1) + embedPair2542
            sharedN10239MinusP007Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP007Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP007Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP007Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP007Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP007Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP007Output2556, pairMagnitude2542]

def sharedN10239MinusP008Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP008Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP008Output2556.1‖ ≤ (sharedN10239MinusP008Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP008BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP008Output2556,
    kernelN10239MinusP008Center2555, kernelN10239MinusP008Error2555, embedPair2542]

theorem sharedN10239MinusP008Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP008Output2556.1) + embedPair2542
            sharedN10239MinusP008Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP008Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP008Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP008Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP008Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP008Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP008Output2556, pairMagnitude2542]

def sharedN10239MinusP009Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP009Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP009Output2556.1‖ ≤ (sharedN10239MinusP009Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP009BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP009Output2556,
    kernelN10239MinusP009Center2555, kernelN10239MinusP009Error2555, embedPair2542]

theorem sharedN10239MinusP009Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP009Output2556.1) + embedPair2542
            sharedN10239MinusP009Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP009Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP009Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP009Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP009Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP009Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP009Output2556, pairMagnitude2542]

def sharedN10239MinusP010Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP010Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP010Output2556.1‖ ≤ (sharedN10239MinusP010Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP010BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP010Output2556,
    kernelN10239MinusP010Center2555, kernelN10239MinusP010Error2555, embedPair2542]

theorem sharedN10239MinusP010Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP010Output2556.1) + embedPair2542
            sharedN10239MinusP010Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP010Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP010Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP010Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP010Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP010Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP010Output2556, pairMagnitude2542]

def sharedN10239MinusP011Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP011Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP011Output2556.1‖ ≤ (sharedN10239MinusP011Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP011BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP011Output2556,
    kernelN10239MinusP011Center2555, kernelN10239MinusP011Error2555, embedPair2542]

theorem sharedN10239MinusP011Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP011Output2556.1) + embedPair2542
            sharedN10239MinusP011Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP011Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP011Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP011Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP011Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP011Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP011Output2556, pairMagnitude2542]

def sharedN10239MinusP012Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP012Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP012Output2556.1‖ ≤ (sharedN10239MinusP012Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP012BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP012Output2556,
    kernelN10239MinusP012Center2555, kernelN10239MinusP012Error2555, embedPair2542]

theorem sharedN10239MinusP012Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP012Output2556.1) + embedPair2542
            sharedN10239MinusP012Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP012Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP012Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP012Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP012Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP012Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP012Output2556, pairMagnitude2542]

def sharedN10239MinusP013Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP013Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP013Output2556.1‖ ≤ (sharedN10239MinusP013Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP013BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP013Output2556,
    kernelN10239MinusP013Center2555, kernelN10239MinusP013Error2555, embedPair2542]

theorem sharedN10239MinusP013Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP013Output2556.1) + embedPair2542
            sharedN10239MinusP013Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP013Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP013Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP013Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP013Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP013Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP013Output2556, pairMagnitude2542]

def sharedN10239MinusP014Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP014Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP014Output2556.1‖ ≤ (sharedN10239MinusP014Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP014BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP014Output2556,
    kernelN10239MinusP014Center2555, kernelN10239MinusP014Error2555, embedPair2542]

theorem sharedN10239MinusP014Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP014Output2556.1) + embedPair2542
            sharedN10239MinusP014Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP014Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP014Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP014Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP014Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP014Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP014Output2556, pairMagnitude2542]

def sharedN10239MinusP015Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP015Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP015Output2556.1‖ ≤ (sharedN10239MinusP015Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP015BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP015Output2556,
    kernelN10239MinusP015Center2555, kernelN10239MinusP015Error2555, embedPair2542]

theorem sharedN10239MinusP015Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP015Output2556.1) + embedPair2542
            sharedN10239MinusP015Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP015Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP015Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP015Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP015Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP015Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP015Output2556, pairMagnitude2542]

def sharedN10239MinusP016Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP016Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP016Output2556.1‖ ≤ (sharedN10239MinusP016Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP016BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP016Output2556,
    kernelN10239MinusP016Center2555, kernelN10239MinusP016Error2555, embedPair2542]

theorem sharedN10239MinusP016Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP016Output2556.1) + embedPair2542
            sharedN10239MinusP016Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP016Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP016Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP016Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP016Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP016Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP016Output2556, pairMagnitude2542]

def sharedN10239MinusP017Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP017Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP017Output2556.1‖ ≤ (sharedN10239MinusP017Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP017BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP017Output2556,
    kernelN10239MinusP017Center2555, kernelN10239MinusP017Error2555, embedPair2542]

theorem sharedN10239MinusP017Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP017Output2556.1) + embedPair2542
            sharedN10239MinusP017Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP017Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP017Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP017Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP017Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP017Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP017Output2556, pairMagnitude2542]

def sharedN10239MinusP018Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP018Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP018Output2556.1‖ ≤ (sharedN10239MinusP018Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP018BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP018Output2556,
    kernelN10239MinusP018Center2555, kernelN10239MinusP018Error2555, embedPair2542]

theorem sharedN10239MinusP018Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP018Output2556.1) + embedPair2542
            sharedN10239MinusP018Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP018Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP018Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP018Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP018Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP018Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP018Output2556, pairMagnitude2542]

def sharedN10239MinusP019Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP019Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP019Output2556.1‖ ≤ (sharedN10239MinusP019Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP019BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP019Output2556,
    kernelN10239MinusP019Center2555, kernelN10239MinusP019Error2555, embedPair2542]

theorem sharedN10239MinusP019Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP019Output2556.1) + embedPair2542
            sharedN10239MinusP019Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP019Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP019Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP019Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP019Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP019Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP019Output2556, pairMagnitude2542]

def sharedN10239MinusP020Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP020Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP020Output2556.1‖ ≤ (sharedN10239MinusP020Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP020BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP020Output2556,
    kernelN10239MinusP020Center2555, kernelN10239MinusP020Error2555, embedPair2542]

theorem sharedN10239MinusP020Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP020Output2556.1) + embedPair2542
            sharedN10239MinusP020Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP020Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP020Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP020Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP020Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP020Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP020Output2556, pairMagnitude2542]

def sharedN10239MinusP021Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP021Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP021Output2556.1‖ ≤ (sharedN10239MinusP021Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP021BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP021Output2556,
    kernelN10239MinusP021Center2555, kernelN10239MinusP021Error2555, embedPair2542]

theorem sharedN10239MinusP021Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP021Output2556.1) + embedPair2542
            sharedN10239MinusP021Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP021Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP021Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP021Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP021Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP021Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP021Output2556, pairMagnitude2542]

def sharedN10239MinusP022Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP022Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP022Output2556.1‖ ≤ (sharedN10239MinusP022Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP022BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP022Output2556,
    kernelN10239MinusP022Center2555, kernelN10239MinusP022Error2555, embedPair2542]

theorem sharedN10239MinusP022Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP022Output2556.1) + embedPair2542
            sharedN10239MinusP022Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP022Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP022Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP022Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP022Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP022Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP022Output2556, pairMagnitude2542]

def sharedN10239MinusP023Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP023Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP023Output2556.1‖ ≤ (sharedN10239MinusP023Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP023BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP023Output2556,
    kernelN10239MinusP023Center2555, kernelN10239MinusP023Error2555, embedPair2542]

theorem sharedN10239MinusP023Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP023Output2556.1) + embedPair2542
            sharedN10239MinusP023Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP023Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP023Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP023Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP023Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP023Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP023Output2556, pairMagnitude2542]

def sharedN10239MinusP024Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP024Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP024Output2556.1‖ ≤ (sharedN10239MinusP024Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP024BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP024Output2556,
    kernelN10239MinusP024Center2555, kernelN10239MinusP024Error2555, embedPair2542]

theorem sharedN10239MinusP024Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP024Output2556.1) + embedPair2542
            sharedN10239MinusP024Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP024Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP024Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP024Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP024Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP024Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP024Output2556, pairMagnitude2542]

def sharedN10239MinusP025Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP025Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP025Output2556.1‖ ≤ (sharedN10239MinusP025Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP025BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP025Output2556,
    kernelN10239MinusP025Center2555, kernelN10239MinusP025Error2555, embedPair2542]

theorem sharedN10239MinusP025Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP025Output2556.1) + embedPair2542
            sharedN10239MinusP025Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP025Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP025Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP025Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP025Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP025Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP025Output2556, pairMagnitude2542]

def sharedN10239MinusP026Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP026Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP026Output2556.1‖ ≤ (sharedN10239MinusP026Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP026BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP026Output2556,
    kernelN10239MinusP026Center2555, kernelN10239MinusP026Error2555, embedPair2542]

theorem sharedN10239MinusP026Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP026Output2556.1) + embedPair2542
            sharedN10239MinusP026Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP026Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP026Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP026Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP026Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP026Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP026Output2556, pairMagnitude2542]

def sharedN10239MinusP027Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP027Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP027Output2556.1‖ ≤ (sharedN10239MinusP027Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP027BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP027Output2556,
    kernelN10239MinusP027Center2555, kernelN10239MinusP027Error2555, embedPair2542]

theorem sharedN10239MinusP027Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP027Output2556.1) + embedPair2542
            sharedN10239MinusP027Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP027Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP027Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP027Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP027Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP027Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP027Output2556, pairMagnitude2542]

def sharedN10239MinusP028Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP028Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP028Output2556.1‖ ≤ (sharedN10239MinusP028Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP028BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP028Output2556,
    kernelN10239MinusP028Center2555, kernelN10239MinusP028Error2555, embedPair2542]

theorem sharedN10239MinusP028Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP028Output2556.1) + embedPair2542
            sharedN10239MinusP028Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP028Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP028Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP028Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP028Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP028Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP028Output2556, pairMagnitude2542]

def sharedN10239MinusP029Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239MinusP029Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP029Output2556.1‖ ≤ (sharedN10239MinusP029Output2556.2 : ℝ) := by
  have h := kernelN10239MinusP029BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239MinusPosition2556, kernelN10239MinusPosition2555,
      sharedN10239MinusP029Output2556,
    kernelN10239MinusP029Center2555, kernelN10239MinusP029Error2555, embedPair2542]

theorem sharedN10239MinusP029Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN10239MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN10239MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP029Output2556.1) + embedPair2542
            sharedN10239MinusP029Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN10239MinusPosition2556 - embedPair2542
            sharedN10239MinusP029Output2556.1‖ + ‖embedPair2542
            sharedN10239MinusP029Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239MinusP029Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239MinusP029Output2556.1 : ℝ) :=
      add_le_add sharedN10239MinusP029Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239MinusP029Output2556, pairMagnitude2542]

noncomputable def sharedN10239MinusValue2556 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 sharedN10239MinusP000Output2556.1
  | 1 => embedPair2542 sharedN10239MinusP001Output2556.1
  | 2 => embedPair2542 sharedN10239MinusP002Output2556.1
  | 3 => embedPair2542 sharedN10239MinusP003Output2556.1
  | 4 => embedPair2542 sharedN10239MinusP004Output2556.1
  | 5 => embedPair2542 sharedN10239MinusP005Output2556.1
  | 6 => embedPair2542 sharedN10239MinusP006Output2556.1
  | 7 => embedPair2542 sharedN10239MinusP007Output2556.1
  | 8 => embedPair2542 sharedN10239MinusP008Output2556.1
  | 9 => embedPair2542 sharedN10239MinusP009Output2556.1
  | 10 => embedPair2542 sharedN10239MinusP010Output2556.1
  | 11 => embedPair2542 sharedN10239MinusP011Output2556.1
  | 12 => embedPair2542 sharedN10239MinusP012Output2556.1
  | 13 => embedPair2542 sharedN10239MinusP013Output2556.1
  | 14 => embedPair2542 sharedN10239MinusP014Output2556.1
  | 15 => embedPair2542 sharedN10239MinusP015Output2556.1
  | 16 => embedPair2542 sharedN10239MinusP016Output2556.1
  | 17 => embedPair2542 sharedN10239MinusP017Output2556.1
  | 18 => embedPair2542 sharedN10239MinusP018Output2556.1
  | 19 => embedPair2542 sharedN10239MinusP019Output2556.1
  | 20 => embedPair2542 sharedN10239MinusP020Output2556.1
  | 21 => embedPair2542 sharedN10239MinusP021Output2556.1
  | 22 => embedPair2542 sharedN10239MinusP022Output2556.1
  | 23 => embedPair2542 sharedN10239MinusP023Output2556.1
  | 24 => embedPair2542 sharedN10239MinusP024Output2556.1
  | 25 => embedPair2542 sharedN10239MinusP025Output2556.1
  | 26 => embedPair2542 sharedN10239MinusP026Output2556.1
  | 27 => embedPair2542 sharedN10239MinusP027Output2556.1
  | 28 => embedPair2542 sharedN10239MinusP028Output2556.1
  | 29 => embedPair2542 sharedN10239MinusP029Output2556.1
  | _ => 0

noncomputable def sharedN10239MinusError2556 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (sharedN10239MinusP000Output2556.2 : ℝ)
  | 1 => (sharedN10239MinusP001Output2556.2 : ℝ)
  | 2 => (sharedN10239MinusP002Output2556.2 : ℝ)
  | 3 => (sharedN10239MinusP003Output2556.2 : ℝ)
  | 4 => (sharedN10239MinusP004Output2556.2 : ℝ)
  | 5 => (sharedN10239MinusP005Output2556.2 : ℝ)
  | 6 => (sharedN10239MinusP006Output2556.2 : ℝ)
  | 7 => (sharedN10239MinusP007Output2556.2 : ℝ)
  | 8 => (sharedN10239MinusP008Output2556.2 : ℝ)
  | 9 => (sharedN10239MinusP009Output2556.2 : ℝ)
  | 10 => (sharedN10239MinusP010Output2556.2 : ℝ)
  | 11 => (sharedN10239MinusP011Output2556.2 : ℝ)
  | 12 => (sharedN10239MinusP012Output2556.2 : ℝ)
  | 13 => (sharedN10239MinusP013Output2556.2 : ℝ)
  | 14 => (sharedN10239MinusP014Output2556.2 : ℝ)
  | 15 => (sharedN10239MinusP015Output2556.2 : ℝ)
  | 16 => (sharedN10239MinusP016Output2556.2 : ℝ)
  | 17 => (sharedN10239MinusP017Output2556.2 : ℝ)
  | 18 => (sharedN10239MinusP018Output2556.2 : ℝ)
  | 19 => (sharedN10239MinusP019Output2556.2 : ℝ)
  | 20 => (sharedN10239MinusP020Output2556.2 : ℝ)
  | 21 => (sharedN10239MinusP021Output2556.2 : ℝ)
  | 22 => (sharedN10239MinusP022Output2556.2 : ℝ)
  | 23 => (sharedN10239MinusP023Output2556.2 : ℝ)
  | 24 => (sharedN10239MinusP024Output2556.2 : ℝ)
  | 25 => (sharedN10239MinusP025Output2556.2 : ℝ)
  | 26 => (sharedN10239MinusP026Output2556.2 : ℝ)
  | 27 => (sharedN10239MinusP027Output2556.2 : ℝ)
  | 28 => (sharedN10239MinusP028Output2556.2 : ℝ)
  | 29 => (sharedN10239MinusP029Output2556.2 : ℝ)
  | _ => 0

theorem sharedN10239MinusExp_error2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN10239MinusPosition2556 - sharedN10239MinusValue2556 i‖
            ≤ sharedN10239MinusError2556 i := by
  fin_cases i
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP000Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP001Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP002Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP003Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP004Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP005Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP006Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP007Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP008Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP009Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP010Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP011Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP012Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP013Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP014Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP015Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP016Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP017Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP018Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP019Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP020Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP021Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP022Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP023Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP024Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP025Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP026Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP027Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP028Error2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP029Error2556

theorem sharedN10239MinusUnit_norm2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN10239MinusPosition2556‖ ≤ 1 := by
  fin_cases i
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP000Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP001Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP002Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP003Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP004Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP005Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP006Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP007Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP008Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP009Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP010Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP011Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP012Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP013Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP014Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP015Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP016Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP017Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP018Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP019Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP020Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP021Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP022Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP023Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP024Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP025Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP026Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP027Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP028Norm2556
  · simpa only [sharedN10239MinusValue2556, sharedN10239MinusError2556] using
      sharedN10239MinusP029Norm2556

noncomputable def sharedN10239MinusSumValue2556 : ℂ := ⟨(0 : ℝ),
    (0 : ℝ)⟩

noncomputable def sharedN10239MinusUpper2556 : ℝ := ((1 : ℝ) /
        5000000000)

theorem sharedN10239MinusSum_eq2556 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN10239MinusValue2556 i) =
      sharedN10239MinusSumValue2556 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN10239MinusValue2556,
      sharedN10239MinusSumValue2556, embedPair2542, sharedN10239MinusP000Output2556,
      sharedN10239MinusP001Output2556,
      sharedN10239MinusP002Output2556,
      sharedN10239MinusP003Output2556,
      sharedN10239MinusP004Output2556,
      sharedN10239MinusP005Output2556,
      sharedN10239MinusP006Output2556,
      sharedN10239MinusP007Output2556,
      sharedN10239MinusP008Output2556,
      sharedN10239MinusP009Output2556,
      sharedN10239MinusP010Output2556,
      sharedN10239MinusP011Output2556,
      sharedN10239MinusP012Output2556,
      sharedN10239MinusP013Output2556,
      sharedN10239MinusP014Output2556,
      sharedN10239MinusP015Output2556,
      sharedN10239MinusP016Output2556,
      sharedN10239MinusP017Output2556,
      sharedN10239MinusP018Output2556,
      sharedN10239MinusP019Output2556,
      sharedN10239MinusP020Output2556,
      sharedN10239MinusP021Output2556,
      sharedN10239MinusP022Output2556,
      sharedN10239MinusP023Output2556,
      sharedN10239MinusP024Output2556,
      sharedN10239MinusP025Output2556,
      sharedN10239MinusP026Output2556,
      sharedN10239MinusP027Output2556,
      sharedN10239MinusP028Output2556,
      sharedN10239MinusP029Output2556, Complex.mul_re, Complex.mul_im]

theorem sharedN10239MinusSum_norm2556 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN10239MinusValue2556 i‖ ≤
      ((1 : ℝ) /
        10000000000) := by
  rw [sharedN10239MinusSum_eq2556]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [sharedN10239MinusSumValue2556]

theorem sharedN10239MinusEvaluation_charge2556 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * sharedN10239MinusError2556 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN10239MinusError2556,
      sharedN10239MinusP000Output2556,
      sharedN10239MinusP001Output2556,
      sharedN10239MinusP002Output2556,
      sharedN10239MinusP003Output2556,
      sharedN10239MinusP004Output2556,
      sharedN10239MinusP005Output2556,
      sharedN10239MinusP006Output2556,
      sharedN10239MinusP007Output2556,
      sharedN10239MinusP008Output2556,
      sharedN10239MinusP009Output2556,
      sharedN10239MinusP010Output2556,
      sharedN10239MinusP011Output2556,
      sharedN10239MinusP012Output2556,
      sharedN10239MinusP013Output2556,
      sharedN10239MinusP014Output2556,
      sharedN10239MinusP015Output2556,
      sharedN10239MinusP016Output2556,
      sharedN10239MinusP017Output2556,
      sharedN10239MinusP018Output2556,
      sharedN10239MinusP019Output2556,
      sharedN10239MinusP020Output2556,
      sharedN10239MinusP021Output2556,
      sharedN10239MinusP022Output2556,
      sharedN10239MinusP023Output2556,
      sharedN10239MinusP024Output2556,
      sharedN10239MinusP025Output2556,
      sharedN10239MinusP026Output2556,
      sharedN10239MinusP027Output2556,
      sharedN10239MinusP028Output2556,
      sharedN10239MinusP029Output2556]

theorem sharedN10239MinusSigned_le2556 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 sharedN10239MinusPosition2556 ≤ sharedN10239MinusUpper2556 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN10239MinusPosition2556‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN10239MinusValue2556 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * sharedN10239MinusError2556 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (sharedN10239MinusExp_error2556 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN10239MinusPosition2556‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (sharedN10239MinusUnit_norm2556 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN10239MinusPosition2556‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 sharedN10239MinusUpper2556
  linarith [sharedN10239MinusSum_norm2556, sharedN10239MinusEvaluation_charge2556]

theorem sharedN10239MinusPhysical_le2556 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 sharedN10239MinusPosition2556‖ ≤
      sharedN10239MinusUpper2556 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        sharedN10239MinusPosition2556
  simpa only [iteratedDeriv_zero] using h.trans sharedN10239MinusSigned_le2556

theorem sharedN10239MinusGrid2556 :
    -stripRadius2303 + (10239 : ℝ)*(2*stripRadius2303/10240) = sharedN10239MinusPosition2556 :=
        by
  norm_num [stripRadius2303, sharedN10239MinusPosition2556]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.sharedN10239MinusSigned_le2556
#print axioms ConnesWeilRH.Dev.sharedN10239MinusPhysical_le2556
