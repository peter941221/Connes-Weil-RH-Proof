import ConnesWeilRH.Dev.C1RouteAKernelN10239Plus2555
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def sharedN10239PlusPosition2556 : ℝ := ((335478789119 : ℝ) /
        51200000000)

def sharedN10239PlusP000Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP000Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP000Output2556.1‖ ≤ (sharedN10239PlusP000Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP000BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP000Output2556,
    kernelN10239PlusP000Center2555, kernelN10239PlusP000Error2555, embedPair2542]

theorem sharedN10239PlusP000Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP000Output2556.1) + embedPair2542
            sharedN10239PlusP000Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP000Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP000Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP000Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP000Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP000Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP000Output2556, pairMagnitude2542]

def sharedN10239PlusP001Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP001Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP001Output2556.1‖ ≤ (sharedN10239PlusP001Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP001BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP001Output2556,
    kernelN10239PlusP001Center2555, kernelN10239PlusP001Error2555, embedPair2542]

theorem sharedN10239PlusP001Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP001Output2556.1) + embedPair2542
            sharedN10239PlusP001Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP001Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP001Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP001Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP001Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP001Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP001Output2556, pairMagnitude2542]

def sharedN10239PlusP002Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP002Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP002Output2556.1‖ ≤ (sharedN10239PlusP002Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP002BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP002Output2556,
    kernelN10239PlusP002Center2555, kernelN10239PlusP002Error2555, embedPair2542]

theorem sharedN10239PlusP002Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP002Output2556.1) + embedPair2542
            sharedN10239PlusP002Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP002Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP002Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP002Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP002Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP002Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP002Output2556, pairMagnitude2542]

def sharedN10239PlusP003Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP003Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP003Output2556.1‖ ≤ (sharedN10239PlusP003Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP003BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP003Output2556,
    kernelN10239PlusP003Center2555, kernelN10239PlusP003Error2555, embedPair2542]

theorem sharedN10239PlusP003Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP003Output2556.1) + embedPair2542
            sharedN10239PlusP003Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP003Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP003Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP003Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP003Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP003Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP003Output2556, pairMagnitude2542]

def sharedN10239PlusP004Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN10239PlusP004Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP004Output2556.1‖ ≤ (sharedN10239PlusP004Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP004BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP004Output2556,
    kernelN10239PlusP004Center2555, kernelN10239PlusP004Error2555, embedPair2542]

theorem sharedN10239PlusP004Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP004Output2556.1) + embedPair2542
            sharedN10239PlusP004Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP004Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP004Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP004Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP004Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP004Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP004Output2556, pairMagnitude2542]

def sharedN10239PlusP005Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP005Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP005Output2556.1‖ ≤ (sharedN10239PlusP005Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP005BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP005Output2556,
    kernelN10239PlusP005Center2555, kernelN10239PlusP005Error2555, embedPair2542]

theorem sharedN10239PlusP005Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP005Output2556.1) + embedPair2542
            sharedN10239PlusP005Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP005Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP005Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP005Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP005Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP005Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP005Output2556, pairMagnitude2542]

def sharedN10239PlusP006Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP006Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP006Output2556.1‖ ≤ (sharedN10239PlusP006Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP006BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP006Output2556,
    kernelN10239PlusP006Center2555, kernelN10239PlusP006Error2555, embedPair2542]

theorem sharedN10239PlusP006Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP006Output2556.1) + embedPair2542
            sharedN10239PlusP006Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP006Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP006Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP006Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP006Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP006Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP006Output2556, pairMagnitude2542]

def sharedN10239PlusP007Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP007Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP007Output2556.1‖ ≤ (sharedN10239PlusP007Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP007BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP007Output2556,
    kernelN10239PlusP007Center2555, kernelN10239PlusP007Error2555, embedPair2542]

theorem sharedN10239PlusP007Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP007Output2556.1) + embedPair2542
            sharedN10239PlusP007Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP007Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP007Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP007Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP007Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP007Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP007Output2556, pairMagnitude2542]

def sharedN10239PlusP008Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP008Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP008Output2556.1‖ ≤ (sharedN10239PlusP008Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP008BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP008Output2556,
    kernelN10239PlusP008Center2555, kernelN10239PlusP008Error2555, embedPair2542]

theorem sharedN10239PlusP008Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP008Output2556.1) + embedPair2542
            sharedN10239PlusP008Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP008Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP008Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP008Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP008Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP008Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP008Output2556, pairMagnitude2542]

def sharedN10239PlusP009Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP009Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP009Output2556.1‖ ≤ (sharedN10239PlusP009Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP009BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP009Output2556,
    kernelN10239PlusP009Center2555, kernelN10239PlusP009Error2555, embedPair2542]

theorem sharedN10239PlusP009Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP009Output2556.1) + embedPair2542
            sharedN10239PlusP009Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP009Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP009Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP009Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP009Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP009Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP009Output2556, pairMagnitude2542]

def sharedN10239PlusP010Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP010Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP010Output2556.1‖ ≤ (sharedN10239PlusP010Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP010BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP010Output2556,
    kernelN10239PlusP010Center2555, kernelN10239PlusP010Error2555, embedPair2542]

theorem sharedN10239PlusP010Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP010Output2556.1) + embedPair2542
            sharedN10239PlusP010Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP010Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP010Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP010Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP010Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP010Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP010Output2556, pairMagnitude2542]

def sharedN10239PlusP011Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP011Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP011Output2556.1‖ ≤ (sharedN10239PlusP011Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP011BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP011Output2556,
    kernelN10239PlusP011Center2555, kernelN10239PlusP011Error2555, embedPair2542]

theorem sharedN10239PlusP011Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP011Output2556.1) + embedPair2542
            sharedN10239PlusP011Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP011Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP011Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP011Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP011Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP011Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP011Output2556, pairMagnitude2542]

def sharedN10239PlusP012Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP012Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP012Output2556.1‖ ≤ (sharedN10239PlusP012Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP012BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP012Output2556,
    kernelN10239PlusP012Center2555, kernelN10239PlusP012Error2555, embedPair2542]

theorem sharedN10239PlusP012Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP012Output2556.1) + embedPair2542
            sharedN10239PlusP012Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP012Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP012Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP012Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP012Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP012Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP012Output2556, pairMagnitude2542]

def sharedN10239PlusP013Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP013Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP013Output2556.1‖ ≤ (sharedN10239PlusP013Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP013BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP013Output2556,
    kernelN10239PlusP013Center2555, kernelN10239PlusP013Error2555, embedPair2542]

theorem sharedN10239PlusP013Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP013Output2556.1) + embedPair2542
            sharedN10239PlusP013Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP013Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP013Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP013Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP013Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP013Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP013Output2556, pairMagnitude2542]

def sharedN10239PlusP014Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP014Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP014Output2556.1‖ ≤ (sharedN10239PlusP014Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP014BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP014Output2556,
    kernelN10239PlusP014Center2555, kernelN10239PlusP014Error2555, embedPair2542]

theorem sharedN10239PlusP014Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP014Output2556.1) + embedPair2542
            sharedN10239PlusP014Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP014Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP014Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP014Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP014Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP014Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP014Output2556, pairMagnitude2542]

def sharedN10239PlusP015Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP015Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP015Output2556.1‖ ≤ (sharedN10239PlusP015Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP015BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP015Output2556,
    kernelN10239PlusP015Center2555, kernelN10239PlusP015Error2555, embedPair2542]

theorem sharedN10239PlusP015Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP015Output2556.1) + embedPair2542
            sharedN10239PlusP015Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP015Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP015Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP015Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP015Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP015Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP015Output2556, pairMagnitude2542]

def sharedN10239PlusP016Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP016Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP016Output2556.1‖ ≤ (sharedN10239PlusP016Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP016BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP016Output2556,
    kernelN10239PlusP016Center2555, kernelN10239PlusP016Error2555, embedPair2542]

theorem sharedN10239PlusP016Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP016Output2556.1) + embedPair2542
            sharedN10239PlusP016Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP016Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP016Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP016Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP016Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP016Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP016Output2556, pairMagnitude2542]

def sharedN10239PlusP017Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP017Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP017Output2556.1‖ ≤ (sharedN10239PlusP017Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP017BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP017Output2556,
    kernelN10239PlusP017Center2555, kernelN10239PlusP017Error2555, embedPair2542]

theorem sharedN10239PlusP017Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP017Output2556.1) + embedPair2542
            sharedN10239PlusP017Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP017Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP017Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP017Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP017Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP017Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP017Output2556, pairMagnitude2542]

def sharedN10239PlusP018Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP018Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP018Output2556.1‖ ≤ (sharedN10239PlusP018Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP018BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP018Output2556,
    kernelN10239PlusP018Center2555, kernelN10239PlusP018Error2555, embedPair2542]

theorem sharedN10239PlusP018Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP018Output2556.1) + embedPair2542
            sharedN10239PlusP018Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP018Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP018Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP018Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP018Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP018Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP018Output2556, pairMagnitude2542]

def sharedN10239PlusP019Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP019Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP019Output2556.1‖ ≤ (sharedN10239PlusP019Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP019BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP019Output2556,
    kernelN10239PlusP019Center2555, kernelN10239PlusP019Error2555, embedPair2542]

theorem sharedN10239PlusP019Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP019Output2556.1) + embedPair2542
            sharedN10239PlusP019Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP019Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP019Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP019Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP019Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP019Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP019Output2556, pairMagnitude2542]

def sharedN10239PlusP020Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP020Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP020Output2556.1‖ ≤ (sharedN10239PlusP020Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP020BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP020Output2556,
    kernelN10239PlusP020Center2555, kernelN10239PlusP020Error2555, embedPair2542]

theorem sharedN10239PlusP020Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP020Output2556.1) + embedPair2542
            sharedN10239PlusP020Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP020Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP020Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP020Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP020Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP020Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP020Output2556, pairMagnitude2542]

def sharedN10239PlusP021Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP021Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP021Output2556.1‖ ≤ (sharedN10239PlusP021Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP021BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP021Output2556,
    kernelN10239PlusP021Center2555, kernelN10239PlusP021Error2555, embedPair2542]

theorem sharedN10239PlusP021Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP021Output2556.1) + embedPair2542
            sharedN10239PlusP021Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP021Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP021Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP021Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP021Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP021Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP021Output2556, pairMagnitude2542]

def sharedN10239PlusP022Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP022Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP022Output2556.1‖ ≤ (sharedN10239PlusP022Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP022BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP022Output2556,
    kernelN10239PlusP022Center2555, kernelN10239PlusP022Error2555, embedPair2542]

theorem sharedN10239PlusP022Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP022Output2556.1) + embedPair2542
            sharedN10239PlusP022Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP022Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP022Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP022Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP022Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP022Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP022Output2556, pairMagnitude2542]

def sharedN10239PlusP023Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP023Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP023Output2556.1‖ ≤ (sharedN10239PlusP023Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP023BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP023Output2556,
    kernelN10239PlusP023Center2555, kernelN10239PlusP023Error2555, embedPair2542]

theorem sharedN10239PlusP023Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP023Output2556.1) + embedPair2542
            sharedN10239PlusP023Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP023Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP023Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP023Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP023Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP023Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP023Output2556, pairMagnitude2542]

def sharedN10239PlusP024Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP024Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP024Output2556.1‖ ≤ (sharedN10239PlusP024Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP024BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP024Output2556,
    kernelN10239PlusP024Center2555, kernelN10239PlusP024Error2555, embedPair2542]

theorem sharedN10239PlusP024Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP024Output2556.1) + embedPair2542
            sharedN10239PlusP024Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP024Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP024Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP024Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP024Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP024Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP024Output2556, pairMagnitude2542]

def sharedN10239PlusP025Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP025Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP025Output2556.1‖ ≤ (sharedN10239PlusP025Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP025BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP025Output2556,
    kernelN10239PlusP025Center2555, kernelN10239PlusP025Error2555, embedPair2542]

theorem sharedN10239PlusP025Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP025Output2556.1) + embedPair2542
            sharedN10239PlusP025Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP025Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP025Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP025Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP025Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP025Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP025Output2556, pairMagnitude2542]

def sharedN10239PlusP026Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP026Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP026Output2556.1‖ ≤ (sharedN10239PlusP026Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP026BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP026Output2556,
    kernelN10239PlusP026Center2555, kernelN10239PlusP026Error2555, embedPair2542]

theorem sharedN10239PlusP026Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP026Output2556.1) + embedPair2542
            sharedN10239PlusP026Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP026Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP026Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP026Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP026Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP026Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP026Output2556, pairMagnitude2542]

def sharedN10239PlusP027Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP027Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP027Output2556.1‖ ≤ (sharedN10239PlusP027Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP027BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP027Output2556,
    kernelN10239PlusP027Center2555, kernelN10239PlusP027Error2555, embedPair2542]

theorem sharedN10239PlusP027Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP027Output2556.1) + embedPair2542
            sharedN10239PlusP027Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP027Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP027Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP027Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP027Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP027Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP027Output2556, pairMagnitude2542]

def sharedN10239PlusP028Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP028Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP028Output2556.1‖ ≤ (sharedN10239PlusP028Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP028BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP028Output2556,
    kernelN10239PlusP028Center2555, kernelN10239PlusP028Error2555, embedPair2542]

theorem sharedN10239PlusP028Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP028Output2556.1) + embedPair2542
            sharedN10239PlusP028Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP028Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP028Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP028Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP028Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP028Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP028Output2556, pairMagnitude2542]

def sharedN10239PlusP029Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN10239PlusP029Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP029Output2556.1‖ ≤ (sharedN10239PlusP029Output2556.2 : ℝ) := by
  have h := kernelN10239PlusP029BaseError2555
  convert h using 1
  all_goals norm_num [sharedN10239PlusPosition2556, kernelN10239PlusPosition2555,
      sharedN10239PlusP029Output2556,
    kernelN10239PlusP029Center2555, kernelN10239PlusP029Error2555, embedPair2542]

theorem sharedN10239PlusP029Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN10239PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN10239PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP029Output2556.1) + embedPair2542
            sharedN10239PlusP029Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN10239PlusPosition2556 - embedPair2542
            sharedN10239PlusP029Output2556.1‖ + ‖embedPair2542
            sharedN10239PlusP029Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN10239PlusP029Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN10239PlusP029Output2556.1 : ℝ) :=
      add_le_add sharedN10239PlusP029Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN10239PlusP029Output2556, pairMagnitude2542]

noncomputable def sharedN10239PlusValue2556 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 sharedN10239PlusP000Output2556.1
  | 1 => embedPair2542 sharedN10239PlusP001Output2556.1
  | 2 => embedPair2542 sharedN10239PlusP002Output2556.1
  | 3 => embedPair2542 sharedN10239PlusP003Output2556.1
  | 4 => embedPair2542 sharedN10239PlusP004Output2556.1
  | 5 => embedPair2542 sharedN10239PlusP005Output2556.1
  | 6 => embedPair2542 sharedN10239PlusP006Output2556.1
  | 7 => embedPair2542 sharedN10239PlusP007Output2556.1
  | 8 => embedPair2542 sharedN10239PlusP008Output2556.1
  | 9 => embedPair2542 sharedN10239PlusP009Output2556.1
  | 10 => embedPair2542 sharedN10239PlusP010Output2556.1
  | 11 => embedPair2542 sharedN10239PlusP011Output2556.1
  | 12 => embedPair2542 sharedN10239PlusP012Output2556.1
  | 13 => embedPair2542 sharedN10239PlusP013Output2556.1
  | 14 => embedPair2542 sharedN10239PlusP014Output2556.1
  | 15 => embedPair2542 sharedN10239PlusP015Output2556.1
  | 16 => embedPair2542 sharedN10239PlusP016Output2556.1
  | 17 => embedPair2542 sharedN10239PlusP017Output2556.1
  | 18 => embedPair2542 sharedN10239PlusP018Output2556.1
  | 19 => embedPair2542 sharedN10239PlusP019Output2556.1
  | 20 => embedPair2542 sharedN10239PlusP020Output2556.1
  | 21 => embedPair2542 sharedN10239PlusP021Output2556.1
  | 22 => embedPair2542 sharedN10239PlusP022Output2556.1
  | 23 => embedPair2542 sharedN10239PlusP023Output2556.1
  | 24 => embedPair2542 sharedN10239PlusP024Output2556.1
  | 25 => embedPair2542 sharedN10239PlusP025Output2556.1
  | 26 => embedPair2542 sharedN10239PlusP026Output2556.1
  | 27 => embedPair2542 sharedN10239PlusP027Output2556.1
  | 28 => embedPair2542 sharedN10239PlusP028Output2556.1
  | 29 => embedPair2542 sharedN10239PlusP029Output2556.1
  | _ => 0

noncomputable def sharedN10239PlusError2556 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (sharedN10239PlusP000Output2556.2 : ℝ)
  | 1 => (sharedN10239PlusP001Output2556.2 : ℝ)
  | 2 => (sharedN10239PlusP002Output2556.2 : ℝ)
  | 3 => (sharedN10239PlusP003Output2556.2 : ℝ)
  | 4 => (sharedN10239PlusP004Output2556.2 : ℝ)
  | 5 => (sharedN10239PlusP005Output2556.2 : ℝ)
  | 6 => (sharedN10239PlusP006Output2556.2 : ℝ)
  | 7 => (sharedN10239PlusP007Output2556.2 : ℝ)
  | 8 => (sharedN10239PlusP008Output2556.2 : ℝ)
  | 9 => (sharedN10239PlusP009Output2556.2 : ℝ)
  | 10 => (sharedN10239PlusP010Output2556.2 : ℝ)
  | 11 => (sharedN10239PlusP011Output2556.2 : ℝ)
  | 12 => (sharedN10239PlusP012Output2556.2 : ℝ)
  | 13 => (sharedN10239PlusP013Output2556.2 : ℝ)
  | 14 => (sharedN10239PlusP014Output2556.2 : ℝ)
  | 15 => (sharedN10239PlusP015Output2556.2 : ℝ)
  | 16 => (sharedN10239PlusP016Output2556.2 : ℝ)
  | 17 => (sharedN10239PlusP017Output2556.2 : ℝ)
  | 18 => (sharedN10239PlusP018Output2556.2 : ℝ)
  | 19 => (sharedN10239PlusP019Output2556.2 : ℝ)
  | 20 => (sharedN10239PlusP020Output2556.2 : ℝ)
  | 21 => (sharedN10239PlusP021Output2556.2 : ℝ)
  | 22 => (sharedN10239PlusP022Output2556.2 : ℝ)
  | 23 => (sharedN10239PlusP023Output2556.2 : ℝ)
  | 24 => (sharedN10239PlusP024Output2556.2 : ℝ)
  | 25 => (sharedN10239PlusP025Output2556.2 : ℝ)
  | 26 => (sharedN10239PlusP026Output2556.2 : ℝ)
  | 27 => (sharedN10239PlusP027Output2556.2 : ℝ)
  | 28 => (sharedN10239PlusP028Output2556.2 : ℝ)
  | 29 => (sharedN10239PlusP029Output2556.2 : ℝ)
  | _ => 0

theorem sharedN10239PlusExp_error2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN10239PlusPosition2556 - sharedN10239PlusValue2556 i‖ ≤
            sharedN10239PlusError2556 i := by
  fin_cases i
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP000Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP001Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP002Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP003Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP004Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP005Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP006Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP007Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP008Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP009Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP010Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP011Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP012Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP013Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP014Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP015Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP016Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP017Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP018Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP019Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP020Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP021Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP022Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP023Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP024Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP025Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP026Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP027Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP028Error2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP029Error2556

theorem sharedN10239PlusUnit_norm2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN10239PlusPosition2556‖ ≤ 1 := by
  fin_cases i
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP000Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP001Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP002Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP003Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP004Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP005Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP006Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP007Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP008Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP009Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP010Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP011Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP012Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP013Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP014Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP015Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP016Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP017Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP018Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP019Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP020Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP021Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP022Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP023Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP024Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP025Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP026Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP027Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP028Norm2556
  · simpa only [sharedN10239PlusValue2556, sharedN10239PlusError2556] using
      sharedN10239PlusP029Norm2556

noncomputable def sharedN10239PlusSumValue2556 : ℂ := ⟨(0 : ℝ),
    (0 : ℝ)⟩

noncomputable def sharedN10239PlusUpper2556 : ℝ := ((1 : ℝ) /
        5000000000)

theorem sharedN10239PlusSum_eq2556 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN10239PlusValue2556 i) =
      sharedN10239PlusSumValue2556 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN10239PlusValue2556,
      sharedN10239PlusSumValue2556, embedPair2542, sharedN10239PlusP000Output2556,
      sharedN10239PlusP001Output2556,
      sharedN10239PlusP002Output2556,
      sharedN10239PlusP003Output2556,
      sharedN10239PlusP004Output2556,
      sharedN10239PlusP005Output2556,
      sharedN10239PlusP006Output2556,
      sharedN10239PlusP007Output2556,
      sharedN10239PlusP008Output2556,
      sharedN10239PlusP009Output2556,
      sharedN10239PlusP010Output2556,
      sharedN10239PlusP011Output2556,
      sharedN10239PlusP012Output2556,
      sharedN10239PlusP013Output2556,
      sharedN10239PlusP014Output2556,
      sharedN10239PlusP015Output2556,
      sharedN10239PlusP016Output2556,
      sharedN10239PlusP017Output2556,
      sharedN10239PlusP018Output2556,
      sharedN10239PlusP019Output2556,
      sharedN10239PlusP020Output2556,
      sharedN10239PlusP021Output2556,
      sharedN10239PlusP022Output2556,
      sharedN10239PlusP023Output2556,
      sharedN10239PlusP024Output2556,
      sharedN10239PlusP025Output2556,
      sharedN10239PlusP026Output2556,
      sharedN10239PlusP027Output2556,
      sharedN10239PlusP028Output2556,
      sharedN10239PlusP029Output2556, Complex.mul_re, Complex.mul_im]

theorem sharedN10239PlusSum_norm2556 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN10239PlusValue2556 i‖ ≤
      ((1 : ℝ) /
        10000000000) := by
  rw [sharedN10239PlusSum_eq2556]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [sharedN10239PlusSumValue2556]

theorem sharedN10239PlusEvaluation_charge2556 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * sharedN10239PlusError2556 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN10239PlusError2556,
      sharedN10239PlusP000Output2556,
      sharedN10239PlusP001Output2556,
      sharedN10239PlusP002Output2556,
      sharedN10239PlusP003Output2556,
      sharedN10239PlusP004Output2556,
      sharedN10239PlusP005Output2556,
      sharedN10239PlusP006Output2556,
      sharedN10239PlusP007Output2556,
      sharedN10239PlusP008Output2556,
      sharedN10239PlusP009Output2556,
      sharedN10239PlusP010Output2556,
      sharedN10239PlusP011Output2556,
      sharedN10239PlusP012Output2556,
      sharedN10239PlusP013Output2556,
      sharedN10239PlusP014Output2556,
      sharedN10239PlusP015Output2556,
      sharedN10239PlusP016Output2556,
      sharedN10239PlusP017Output2556,
      sharedN10239PlusP018Output2556,
      sharedN10239PlusP019Output2556,
      sharedN10239PlusP020Output2556,
      sharedN10239PlusP021Output2556,
      sharedN10239PlusP022Output2556,
      sharedN10239PlusP023Output2556,
      sharedN10239PlusP024Output2556,
      sharedN10239PlusP025Output2556,
      sharedN10239PlusP026Output2556,
      sharedN10239PlusP027Output2556,
      sharedN10239PlusP028Output2556,
      sharedN10239PlusP029Output2556]

theorem sharedN10239PlusSigned_le2556 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 sharedN10239PlusPosition2556 ≤ sharedN10239PlusUpper2556 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN10239PlusPosition2556‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN10239PlusValue2556 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * sharedN10239PlusError2556 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (sharedN10239PlusExp_error2556 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN10239PlusPosition2556‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (sharedN10239PlusUnit_norm2556 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN10239PlusPosition2556‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 sharedN10239PlusUpper2556
  linarith [sharedN10239PlusSum_norm2556, sharedN10239PlusEvaluation_charge2556]

theorem sharedN10239PlusPhysical_le2556 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 sharedN10239PlusPosition2556‖ ≤
      sharedN10239PlusUpper2556 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        sharedN10239PlusPosition2556
  simpa only [iteratedDeriv_zero] using h.trans sharedN10239PlusSigned_le2556

theorem sharedN10239PlusGrid2556 :
    -stripRadius2303 + (10239 : ℝ)*(2*stripRadius2303/10240) = sharedN10239PlusPosition2556 :=
        by
  norm_num [stripRadius2303, sharedN10239PlusPosition2556]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.sharedN10239PlusSigned_le2556
#print axioms ConnesWeilRH.Dev.sharedN10239PlusPhysical_le2556
