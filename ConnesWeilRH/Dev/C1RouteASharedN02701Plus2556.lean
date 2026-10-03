import ConnesWeilRH.Dev.C1RouteAKernelN02701Plus2555
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def sharedN02701PlusPosition2556 : ℝ := (((-158531586419) : ℝ) /
        51200000000)

def sharedN02701PlusP000Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02701PlusP000Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP000Output2556.1‖ ≤ (sharedN02701PlusP000Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP000BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP000Output2556,
    kernelN02701PlusP000Center2555, kernelN02701PlusP000Error2555, embedPair2542]

theorem sharedN02701PlusP000Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP000Output2556.1) + embedPair2542
            sharedN02701PlusP000Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP000Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP000Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP000Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP000Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP000Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP000Output2556, pairMagnitude2542]

def sharedN02701PlusP001Output2556 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP001Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP001Output2556.1‖ ≤ (sharedN02701PlusP001Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP001BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP001Output2556,
    kernelN02701PlusP001Center2555, kernelN02701PlusP001Error2555, embedPair2542]

theorem sharedN02701PlusP001Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP001Output2556.1) + embedPair2542
            sharedN02701PlusP001Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP001Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP001Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP001Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP001Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP001Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP001Output2556, pairMagnitude2542]

def sharedN02701PlusP002Output2556 : RatState2542 :=
  (((((-168036782698919993429) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-252698714645137902289) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((2260016183526325913 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP002Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP002Output2556.1‖ ≤ (sharedN02701PlusP002Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP002BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP002Output2556,
    kernelN02701PlusP002Center2555, kernelN02701PlusP002Error2555, embedPair2542]

theorem sharedN02701PlusP002Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP002Output2556.1) + embedPair2542
            sharedN02701PlusP002Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP002Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP002Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP002Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP002Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP002Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP002Output2556, pairMagnitude2542]

def sharedN02701PlusP003Output2556 : RatState2542 :=
  (((((-5788973884569169910793434755) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-4352815604563173678616329029) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((36476409710489096549727441 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP003Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP003Output2556.1‖ ≤ (sharedN02701PlusP003Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP003BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP003Output2556,
    kernelN02701PlusP003Center2555, kernelN02701PlusP003Error2555, embedPair2542]

theorem sharedN02701PlusP003Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP003Output2556.1) + embedPair2542
            sharedN02701PlusP003Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP003Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP003Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP003Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP003Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP003Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP003Output2556, pairMagnitude2542]

def sharedN02701PlusP004Output2556 : RatState2542 :=
  (((((-725790656500916187131713370187) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((4365862355930743774088204387843 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((17853934217737043702764082891 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP004Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP004Output2556.1‖ ≤ (sharedN02701PlusP004Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP004BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP004Output2556,
    kernelN02701PlusP004Center2555, kernelN02701PlusP004Error2555, embedPair2542]

theorem sharedN02701PlusP004Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP004Output2556.1) + embedPair2542
            sharedN02701PlusP004Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP004Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP004Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP004Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP004Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP004Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP004Output2556, pairMagnitude2542]

def sharedN02701PlusP005Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02701PlusP005Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP005Output2556.1‖ ≤ (sharedN02701PlusP005Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP005BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP005Output2556,
    kernelN02701PlusP005Center2555, kernelN02701PlusP005Error2555, embedPair2542]

theorem sharedN02701PlusP005Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP005Output2556.1) + embedPair2542
            sharedN02701PlusP005Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP005Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP005Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP005Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP005Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP005Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP005Output2556, pairMagnitude2542]

def sharedN02701PlusP006Output2556 : RatState2542 :=
  ((((483449294895075 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((2446198475405 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP006Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP006Output2556.1‖ ≤ (sharedN02701PlusP006Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP006BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP006Output2556,
    kernelN02701PlusP006Center2555, kernelN02701PlusP006Error2555, embedPair2542]

theorem sharedN02701PlusP006Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP006Output2556.1) + embedPair2542
            sharedN02701PlusP006Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP006Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP006Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP006Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP006Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP006Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP006Output2556, pairMagnitude2542]

def sharedN02701PlusP007Output2556 : RatState2542 :=
  ((((163354299886446954699714643 : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)),
    ((0 : ℚ) /
        1)),
    ((759335337735088749674751 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN02701PlusP007Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP007Output2556.1‖ ≤ (sharedN02701PlusP007Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP007BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP007Output2556,
    kernelN02701PlusP007Center2555, kernelN02701PlusP007Error2555, embedPair2542]

theorem sharedN02701PlusP007Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP007Output2556.1) + embedPair2542
            sharedN02701PlusP007Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP007Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP007Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP007Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP007Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP007Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP007Output2556, pairMagnitude2542]

def sharedN02701PlusP008Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP008Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP008Output2556.1‖ ≤ (sharedN02701PlusP008Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP008BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP008Output2556,
    kernelN02701PlusP008Center2555, kernelN02701PlusP008Error2555, embedPair2542]

theorem sharedN02701PlusP008Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP008Output2556.1) + embedPair2542
            sharedN02701PlusP008Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP008Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP008Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP008Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP008Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP008Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP008Output2556, pairMagnitude2542]

def sharedN02701PlusP009Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP009Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP009Output2556.1‖ ≤ (sharedN02701PlusP009Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP009BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP009Output2556,
    kernelN02701PlusP009Center2555, kernelN02701PlusP009Error2555, embedPair2542]

theorem sharedN02701PlusP009Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP009Output2556.1) + embedPair2542
            sharedN02701PlusP009Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP009Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP009Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP009Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP009Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP009Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP009Output2556, pairMagnitude2542]

def sharedN02701PlusP010Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP010Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP010Output2556.1‖ ≤ (sharedN02701PlusP010Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP010BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP010Output2556,
    kernelN02701PlusP010Center2555, kernelN02701PlusP010Error2555, embedPair2542]

theorem sharedN02701PlusP010Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP010Output2556.1) + embedPair2542
            sharedN02701PlusP010Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP010Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP010Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP010Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP010Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP010Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP010Output2556, pairMagnitude2542]

def sharedN02701PlusP011Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP011Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP011Output2556.1‖ ≤ (sharedN02701PlusP011Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP011BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP011Output2556,
    kernelN02701PlusP011Center2555, kernelN02701PlusP011Error2555, embedPair2542]

theorem sharedN02701PlusP011Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP011Output2556.1) + embedPair2542
            sharedN02701PlusP011Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP011Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP011Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP011Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP011Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP011Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP011Output2556, pairMagnitude2542]

def sharedN02701PlusP012Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP012Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP012Output2556.1‖ ≤ (sharedN02701PlusP012Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP012BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP012Output2556,
    kernelN02701PlusP012Center2555, kernelN02701PlusP012Error2555, embedPair2542]

theorem sharedN02701PlusP012Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP012Output2556.1) + embedPair2542
            sharedN02701PlusP012Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP012Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP012Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP012Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP012Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP012Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP012Output2556, pairMagnitude2542]

def sharedN02701PlusP013Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP013Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP013Output2556.1‖ ≤ (sharedN02701PlusP013Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP013BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP013Output2556,
    kernelN02701PlusP013Center2555, kernelN02701PlusP013Error2555, embedPair2542]

theorem sharedN02701PlusP013Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP013Output2556.1) + embedPair2542
            sharedN02701PlusP013Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP013Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP013Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP013Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP013Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP013Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP013Output2556, pairMagnitude2542]

def sharedN02701PlusP014Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP014Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP014Output2556.1‖ ≤ (sharedN02701PlusP014Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP014BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP014Output2556,
    kernelN02701PlusP014Center2555, kernelN02701PlusP014Error2555, embedPair2542]

theorem sharedN02701PlusP014Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP014Output2556.1) + embedPair2542
            sharedN02701PlusP014Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP014Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP014Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP014Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP014Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP014Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP014Output2556, pairMagnitude2542]

def sharedN02701PlusP015Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP015Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP015Output2556.1‖ ≤ (sharedN02701PlusP015Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP015BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP015Output2556,
    kernelN02701PlusP015Center2555, kernelN02701PlusP015Error2555, embedPair2542]

theorem sharedN02701PlusP015Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP015Output2556.1) + embedPair2542
            sharedN02701PlusP015Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP015Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP015Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP015Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP015Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP015Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP015Output2556, pairMagnitude2542]

def sharedN02701PlusP016Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP016Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP016Output2556.1‖ ≤ (sharedN02701PlusP016Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP016BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP016Output2556,
    kernelN02701PlusP016Center2555, kernelN02701PlusP016Error2555, embedPair2542]

theorem sharedN02701PlusP016Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP016Output2556.1) + embedPair2542
            sharedN02701PlusP016Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP016Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP016Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP016Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP016Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP016Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP016Output2556, pairMagnitude2542]

def sharedN02701PlusP017Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP017Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP017Output2556.1‖ ≤ (sharedN02701PlusP017Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP017BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP017Output2556,
    kernelN02701PlusP017Center2555, kernelN02701PlusP017Error2555, embedPair2542]

theorem sharedN02701PlusP017Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP017Output2556.1) + embedPair2542
            sharedN02701PlusP017Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP017Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP017Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP017Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP017Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP017Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP017Output2556, pairMagnitude2542]

def sharedN02701PlusP018Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP018Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP018Output2556.1‖ ≤ (sharedN02701PlusP018Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP018BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP018Output2556,
    kernelN02701PlusP018Center2555, kernelN02701PlusP018Error2555, embedPair2542]

theorem sharedN02701PlusP018Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP018Output2556.1) + embedPair2542
            sharedN02701PlusP018Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP018Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP018Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP018Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP018Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP018Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP018Output2556, pairMagnitude2542]

def sharedN02701PlusP019Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP019Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP019Output2556.1‖ ≤ (sharedN02701PlusP019Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP019BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP019Output2556,
    kernelN02701PlusP019Center2555, kernelN02701PlusP019Error2555, embedPair2542]

theorem sharedN02701PlusP019Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP019Output2556.1) + embedPair2542
            sharedN02701PlusP019Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP019Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP019Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP019Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP019Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP019Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP019Output2556, pairMagnitude2542]

def sharedN02701PlusP020Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP020Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP020Output2556.1‖ ≤ (sharedN02701PlusP020Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP020BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP020Output2556,
    kernelN02701PlusP020Center2555, kernelN02701PlusP020Error2555, embedPair2542]

theorem sharedN02701PlusP020Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP020Output2556.1) + embedPair2542
            sharedN02701PlusP020Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP020Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP020Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP020Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP020Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP020Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP020Output2556, pairMagnitude2542]

def sharedN02701PlusP021Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP021Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP021Output2556.1‖ ≤ (sharedN02701PlusP021Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP021BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP021Output2556,
    kernelN02701PlusP021Center2555, kernelN02701PlusP021Error2555, embedPair2542]

theorem sharedN02701PlusP021Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP021Output2556.1) + embedPair2542
            sharedN02701PlusP021Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP021Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP021Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP021Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP021Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP021Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP021Output2556, pairMagnitude2542]

def sharedN02701PlusP022Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP022Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP022Output2556.1‖ ≤ (sharedN02701PlusP022Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP022BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP022Output2556,
    kernelN02701PlusP022Center2555, kernelN02701PlusP022Error2555, embedPair2542]

theorem sharedN02701PlusP022Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP022Output2556.1) + embedPair2542
            sharedN02701PlusP022Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP022Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP022Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP022Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP022Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP022Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP022Output2556, pairMagnitude2542]

def sharedN02701PlusP023Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP023Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP023Output2556.1‖ ≤ (sharedN02701PlusP023Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP023BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP023Output2556,
    kernelN02701PlusP023Center2555, kernelN02701PlusP023Error2555, embedPair2542]

theorem sharedN02701PlusP023Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP023Output2556.1) + embedPair2542
            sharedN02701PlusP023Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP023Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP023Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP023Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP023Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP023Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP023Output2556, pairMagnitude2542]

def sharedN02701PlusP024Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP024Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP024Output2556.1‖ ≤ (sharedN02701PlusP024Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP024BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP024Output2556,
    kernelN02701PlusP024Center2555, kernelN02701PlusP024Error2555, embedPair2542]

theorem sharedN02701PlusP024Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP024Output2556.1) + embedPair2542
            sharedN02701PlusP024Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP024Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP024Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP024Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP024Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP024Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP024Output2556, pairMagnitude2542]

def sharedN02701PlusP025Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP025Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP025Output2556.1‖ ≤ (sharedN02701PlusP025Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP025BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP025Output2556,
    kernelN02701PlusP025Center2555, kernelN02701PlusP025Error2555, embedPair2542]

theorem sharedN02701PlusP025Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP025Output2556.1) + embedPair2542
            sharedN02701PlusP025Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP025Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP025Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP025Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP025Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP025Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP025Output2556, pairMagnitude2542]

def sharedN02701PlusP026Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP026Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP026Output2556.1‖ ≤ (sharedN02701PlusP026Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP026BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP026Output2556,
    kernelN02701PlusP026Center2555, kernelN02701PlusP026Error2555, embedPair2542]

theorem sharedN02701PlusP026Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP026Output2556.1) + embedPair2542
            sharedN02701PlusP026Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP026Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP026Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP026Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP026Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP026Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP026Output2556, pairMagnitude2542]

def sharedN02701PlusP027Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP027Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP027Output2556.1‖ ≤ (sharedN02701PlusP027Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP027BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP027Output2556,
    kernelN02701PlusP027Center2555, kernelN02701PlusP027Error2555, embedPair2542]

theorem sharedN02701PlusP027Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP027Output2556.1) + embedPair2542
            sharedN02701PlusP027Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP027Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP027Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP027Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP027Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP027Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP027Output2556, pairMagnitude2542]

def sharedN02701PlusP028Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP028Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP028Output2556.1‖ ≤ (sharedN02701PlusP028Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP028BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP028Output2556,
    kernelN02701PlusP028Center2555, kernelN02701PlusP028Error2555, embedPair2542]

theorem sharedN02701PlusP028Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP028Output2556.1) + embedPair2542
            sharedN02701PlusP028Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP028Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP028Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP028Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP028Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP028Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP028Output2556, pairMagnitude2542]

def sharedN02701PlusP029Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701PlusP029Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP029Output2556.1‖ ≤ (sharedN02701PlusP029Output2556.2 : ℝ) := by
  have h := kernelN02701PlusP029BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555,
      sharedN02701PlusP029Output2556,
    kernelN02701PlusP029Center2555, kernelN02701PlusP029Error2555, embedPair2542]

theorem sharedN02701PlusP029Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02701PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02701PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP029Output2556.1) + embedPair2542
            sharedN02701PlusP029Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02701PlusPosition2556 - embedPair2542
            sharedN02701PlusP029Output2556.1‖ + ‖embedPair2542
            sharedN02701PlusP029Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701PlusP029Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701PlusP029Output2556.1 : ℝ) :=
      add_le_add sharedN02701PlusP029Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701PlusP029Output2556, pairMagnitude2542]

noncomputable def sharedN02701PlusValue2556 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 sharedN02701PlusP000Output2556.1
  | 1 => embedPair2542 sharedN02701PlusP001Output2556.1
  | 2 => embedPair2542 sharedN02701PlusP002Output2556.1
  | 3 => embedPair2542 sharedN02701PlusP003Output2556.1
  | 4 => embedPair2542 sharedN02701PlusP004Output2556.1
  | 5 => embedPair2542 sharedN02701PlusP005Output2556.1
  | 6 => embedPair2542 sharedN02701PlusP006Output2556.1
  | 7 => embedPair2542 sharedN02701PlusP007Output2556.1
  | 8 => embedPair2542 sharedN02701PlusP008Output2556.1
  | 9 => embedPair2542 sharedN02701PlusP009Output2556.1
  | 10 => embedPair2542 sharedN02701PlusP010Output2556.1
  | 11 => embedPair2542 sharedN02701PlusP011Output2556.1
  | 12 => embedPair2542 sharedN02701PlusP012Output2556.1
  | 13 => embedPair2542 sharedN02701PlusP013Output2556.1
  | 14 => embedPair2542 sharedN02701PlusP014Output2556.1
  | 15 => embedPair2542 sharedN02701PlusP015Output2556.1
  | 16 => embedPair2542 sharedN02701PlusP016Output2556.1
  | 17 => embedPair2542 sharedN02701PlusP017Output2556.1
  | 18 => embedPair2542 sharedN02701PlusP018Output2556.1
  | 19 => embedPair2542 sharedN02701PlusP019Output2556.1
  | 20 => embedPair2542 sharedN02701PlusP020Output2556.1
  | 21 => embedPair2542 sharedN02701PlusP021Output2556.1
  | 22 => embedPair2542 sharedN02701PlusP022Output2556.1
  | 23 => embedPair2542 sharedN02701PlusP023Output2556.1
  | 24 => embedPair2542 sharedN02701PlusP024Output2556.1
  | 25 => embedPair2542 sharedN02701PlusP025Output2556.1
  | 26 => embedPair2542 sharedN02701PlusP026Output2556.1
  | 27 => embedPair2542 sharedN02701PlusP027Output2556.1
  | 28 => embedPair2542 sharedN02701PlusP028Output2556.1
  | 29 => embedPair2542 sharedN02701PlusP029Output2556.1
  | _ => 0

noncomputable def sharedN02701PlusError2556 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (sharedN02701PlusP000Output2556.2 : ℝ)
  | 1 => (sharedN02701PlusP001Output2556.2 : ℝ)
  | 2 => (sharedN02701PlusP002Output2556.2 : ℝ)
  | 3 => (sharedN02701PlusP003Output2556.2 : ℝ)
  | 4 => (sharedN02701PlusP004Output2556.2 : ℝ)
  | 5 => (sharedN02701PlusP005Output2556.2 : ℝ)
  | 6 => (sharedN02701PlusP006Output2556.2 : ℝ)
  | 7 => (sharedN02701PlusP007Output2556.2 : ℝ)
  | 8 => (sharedN02701PlusP008Output2556.2 : ℝ)
  | 9 => (sharedN02701PlusP009Output2556.2 : ℝ)
  | 10 => (sharedN02701PlusP010Output2556.2 : ℝ)
  | 11 => (sharedN02701PlusP011Output2556.2 : ℝ)
  | 12 => (sharedN02701PlusP012Output2556.2 : ℝ)
  | 13 => (sharedN02701PlusP013Output2556.2 : ℝ)
  | 14 => (sharedN02701PlusP014Output2556.2 : ℝ)
  | 15 => (sharedN02701PlusP015Output2556.2 : ℝ)
  | 16 => (sharedN02701PlusP016Output2556.2 : ℝ)
  | 17 => (sharedN02701PlusP017Output2556.2 : ℝ)
  | 18 => (sharedN02701PlusP018Output2556.2 : ℝ)
  | 19 => (sharedN02701PlusP019Output2556.2 : ℝ)
  | 20 => (sharedN02701PlusP020Output2556.2 : ℝ)
  | 21 => (sharedN02701PlusP021Output2556.2 : ℝ)
  | 22 => (sharedN02701PlusP022Output2556.2 : ℝ)
  | 23 => (sharedN02701PlusP023Output2556.2 : ℝ)
  | 24 => (sharedN02701PlusP024Output2556.2 : ℝ)
  | 25 => (sharedN02701PlusP025Output2556.2 : ℝ)
  | 26 => (sharedN02701PlusP026Output2556.2 : ℝ)
  | 27 => (sharedN02701PlusP027Output2556.2 : ℝ)
  | 28 => (sharedN02701PlusP028Output2556.2 : ℝ)
  | 29 => (sharedN02701PlusP029Output2556.2 : ℝ)
  | _ => 0

theorem sharedN02701PlusExp_error2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN02701PlusPosition2556 - sharedN02701PlusValue2556 i‖ ≤
            sharedN02701PlusError2556 i := by
  fin_cases i
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP000Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP001Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP002Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP003Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP004Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP005Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP006Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP007Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP008Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP009Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP010Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP011Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP012Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP013Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP014Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP015Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP016Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP017Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP018Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP019Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP020Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP021Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP022Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP023Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP024Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP025Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP026Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP027Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP028Error2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP029Error2556

theorem sharedN02701PlusUnit_norm2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN02701PlusPosition2556‖ ≤ 1 := by
  fin_cases i
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP000Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP001Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP002Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP003Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP004Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP005Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP006Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP007Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP008Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP009Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP010Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP011Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP012Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP013Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP014Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP015Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP016Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP017Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP018Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP019Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP020Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP021Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP022Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP023Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP024Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP025Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP026Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP027Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP028Norm2556
  · simpa only [sharedN02701PlusValue2556, sharedN02701PlusError2556] using
      sharedN02701PlusP029Norm2556

noncomputable def sharedN02701PlusSumValue2556 : ℂ := ⟨(((((2012270062079733098 * 10^40
        + 6805000908639757394970576341859388399611) * 10^40
        + 6002517447148145730972294829302289287872) * 10^40
        + 2069220137625683244044856378349348968967) : ℝ) /
        (((24973988402527937851052777 * 10^40
        + 8383453304459887851413197692068732556770) * 10^40
        + 297391055812496096244882450793576927861) * 10^40
        + 5448971252983163583805434306282450321408)),
    (((((828898507977728844 * 10^40
        + 1259640434600071446405843059810935214101) * 10^40
        + 8809712779601228861446180868601729278408) * 10^40
        + 4282641975107424831149099741573090031983) : ℝ) /
        (((24973988402527937851052777 * 10^40
        + 8383453304459887851413197692068732556770) * 10^40
        + 297391055812496096244882450793576927861) * 10^40
        + 5448971252983163583805434306282450321408))⟩

noncomputable def sharedN02701PlusUpper2556 : ℝ := ((873 : ℝ) /
        10000000000)

theorem sharedN02701PlusSum_eq2556 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN02701PlusValue2556 i) =
      sharedN02701PlusSumValue2556 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN02701PlusValue2556,
      sharedN02701PlusSumValue2556, embedPair2542, sharedN02701PlusP000Output2556,
      sharedN02701PlusP001Output2556,
      sharedN02701PlusP002Output2556,
      sharedN02701PlusP003Output2556,
      sharedN02701PlusP004Output2556,
      sharedN02701PlusP005Output2556,
      sharedN02701PlusP006Output2556,
      sharedN02701PlusP007Output2556,
      sharedN02701PlusP008Output2556,
      sharedN02701PlusP009Output2556,
      sharedN02701PlusP010Output2556,
      sharedN02701PlusP011Output2556,
      sharedN02701PlusP012Output2556,
      sharedN02701PlusP013Output2556,
      sharedN02701PlusP014Output2556,
      sharedN02701PlusP015Output2556,
      sharedN02701PlusP016Output2556,
      sharedN02701PlusP017Output2556,
      sharedN02701PlusP018Output2556,
      sharedN02701PlusP019Output2556,
      sharedN02701PlusP020Output2556,
      sharedN02701PlusP021Output2556,
      sharedN02701PlusP022Output2556,
      sharedN02701PlusP023Output2556,
      sharedN02701PlusP024Output2556,
      sharedN02701PlusP025Output2556,
      sharedN02701PlusP026Output2556,
      sharedN02701PlusP027Output2556,
      sharedN02701PlusP028Output2556,
      sharedN02701PlusP029Output2556, Complex.mul_re, Complex.mul_im]

theorem sharedN02701PlusSum_norm2556 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN02701PlusValue2556 i‖ ≤
      ((109 : ℝ) /
        1250000000) := by
  rw [sharedN02701PlusSum_eq2556]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [sharedN02701PlusSumValue2556]

theorem sharedN02701PlusEvaluation_charge2556 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * sharedN02701PlusError2556 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN02701PlusError2556,
      sharedN02701PlusP000Output2556,
      sharedN02701PlusP001Output2556,
      sharedN02701PlusP002Output2556,
      sharedN02701PlusP003Output2556,
      sharedN02701PlusP004Output2556,
      sharedN02701PlusP005Output2556,
      sharedN02701PlusP006Output2556,
      sharedN02701PlusP007Output2556,
      sharedN02701PlusP008Output2556,
      sharedN02701PlusP009Output2556,
      sharedN02701PlusP010Output2556,
      sharedN02701PlusP011Output2556,
      sharedN02701PlusP012Output2556,
      sharedN02701PlusP013Output2556,
      sharedN02701PlusP014Output2556,
      sharedN02701PlusP015Output2556,
      sharedN02701PlusP016Output2556,
      sharedN02701PlusP017Output2556,
      sharedN02701PlusP018Output2556,
      sharedN02701PlusP019Output2556,
      sharedN02701PlusP020Output2556,
      sharedN02701PlusP021Output2556,
      sharedN02701PlusP022Output2556,
      sharedN02701PlusP023Output2556,
      sharedN02701PlusP024Output2556,
      sharedN02701PlusP025Output2556,
      sharedN02701PlusP026Output2556,
      sharedN02701PlusP027Output2556,
      sharedN02701PlusP028Output2556,
      sharedN02701PlusP029Output2556]

theorem sharedN02701PlusSigned_le2556 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 sharedN02701PlusPosition2556 ≤ sharedN02701PlusUpper2556 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN02701PlusPosition2556‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN02701PlusValue2556 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * sharedN02701PlusError2556 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (sharedN02701PlusExp_error2556 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN02701PlusPosition2556‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (sharedN02701PlusUnit_norm2556 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN02701PlusPosition2556‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 sharedN02701PlusUpper2556
  linarith [sharedN02701PlusSum_norm2556, sharedN02701PlusEvaluation_charge2556]

theorem sharedN02701PlusPhysical_le2556 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 sharedN02701PlusPosition2556‖ ≤
      sharedN02701PlusUpper2556 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        sharedN02701PlusPosition2556
  simpa only [iteratedDeriv_zero] using h.trans sharedN02701PlusSigned_le2556

theorem sharedN02701PlusGrid2556 :
    -stripRadius2303 + (2701 : ℝ)*(2*stripRadius2303/10240) = sharedN02701PlusPosition2556 := by
  norm_num [stripRadius2303, sharedN02701PlusPosition2556]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.sharedN02701PlusSigned_le2556
#print axioms ConnesWeilRH.Dev.sharedN02701PlusPhysical_le2556
