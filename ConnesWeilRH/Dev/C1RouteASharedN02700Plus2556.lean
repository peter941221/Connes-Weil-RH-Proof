import ConnesWeilRH.Dev.C1RouteAKernelN02700Plus2555
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def sharedN02700PlusPosition2556 : ℝ := (((-7929856121) : ℝ) /
        2560000000)

def sharedN02700PlusP000Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP000Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP000Output2556.1‖ ≤ (sharedN02700PlusP000Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP000BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP000Output2556,
    kernelN02700PlusP000Center2555, kernelN02700PlusP000Error2555, embedPair2542]

theorem sharedN02700PlusP000Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP000Output2556.1) + embedPair2542
            sharedN02700PlusP000Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP000Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP000Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP000Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP000Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP000Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP000Output2556, pairMagnitude2542]

def sharedN02700PlusP001Output2556 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02700PlusP001Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP001Output2556.1‖ ≤ (sharedN02700PlusP001Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP001BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP001Output2556,
    kernelN02700PlusP001Center2555, kernelN02700PlusP001Error2555, embedPair2542]

theorem sharedN02700PlusP001Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP001Output2556.1) + embedPair2542
            sharedN02700PlusP001Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP001Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP001Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP001Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP001Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP001Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP001Output2556, pairMagnitude2542]

def sharedN02700PlusP002Output2556 : RatState2542 :=
  (((((-342022637592315929245) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-462193622279321905361) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((2124679950171895707 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02700PlusP002Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP002Output2556.1‖ ≤ (sharedN02700PlusP002Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP002BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP002Output2556,
    kernelN02700PlusP002Center2555, kernelN02700PlusP002Error2555, embedPair2542]

theorem sharedN02700PlusP002Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP002Output2556.1) + embedPair2542
            sharedN02700PlusP002Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP002Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP002Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP002Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP002Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP002Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP002Output2556, pairMagnitude2542]

def sharedN02700PlusP003Output2556 : RatState2542 :=
  (((((-3050957105819623379802289723) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-4122922757640557388486708103) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((35512274632534440194531833 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02700PlusP003Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP003Output2556.1‖ ≤ (sharedN02700PlusP003Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP003BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP003Output2556,
    kernelN02700PlusP003Center2555, kernelN02700PlusP003Error2555, embedPair2542]

theorem sharedN02700PlusP003Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP003Output2556.1) + embedPair2542
            sharedN02700PlusP003Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP003Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP003Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP003Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP003Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP003Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP003Output2556, pairMagnitude2542]

def sharedN02700PlusP004Output2556 : RatState2542 :=
  (((((-3088285000154142764160101575539) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((4173365952909685099392742956493 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((4385370515285168518352942979 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem sharedN02700PlusP004Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP004Output2556.1‖ ≤ (sharedN02700PlusP004Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP004BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP004Output2556,
    kernelN02700PlusP004Center2555, kernelN02700PlusP004Error2555, embedPair2542]

theorem sharedN02700PlusP004Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP004Output2556.1) + embedPair2542
            sharedN02700PlusP004Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP004Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP004Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP004Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP004Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP004Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP004Output2556, pairMagnitude2542]

def sharedN02700PlusP005Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP005Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP005Output2556.1‖ ≤ (sharedN02700PlusP005Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP005BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP005Output2556,
    kernelN02700PlusP005Center2555, kernelN02700PlusP005Error2555, embedPair2542]

theorem sharedN02700PlusP005Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP005Output2556.1) + embedPair2542
            sharedN02700PlusP005Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP005Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP005Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP005Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP005Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP005Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP005Output2556, pairMagnitude2542]

def sharedN02700PlusP006Output2556 : RatState2542 :=
  ((((440386906605911 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((2424345947741 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02700PlusP006Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP006Output2556.1‖ ≤ (sharedN02700PlusP006Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP006BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP006Output2556,
    kernelN02700PlusP006Center2555, kernelN02700PlusP006Error2555, embedPair2542]

theorem sharedN02700PlusP006Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP006Output2556.1) + embedPair2542
            sharedN02700PlusP006Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP006Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP006Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP006Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP006Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP006Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP006Output2556, pairMagnitude2542]

def sharedN02700PlusP007Output2556 : RatState2542 :=
  ((((1282254638493795595923663161 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1)),
    ((372637180338657148206451 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem sharedN02700PlusP007Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP007Output2556.1‖ ≤ (sharedN02700PlusP007Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP007BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP007Output2556,
    kernelN02700PlusP007Center2555, kernelN02700PlusP007Error2555, embedPair2542]

theorem sharedN02700PlusP007Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP007Output2556.1) + embedPair2542
            sharedN02700PlusP007Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP007Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP007Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP007Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP007Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP007Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP007Output2556, pairMagnitude2542]

def sharedN02700PlusP008Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP008Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP008Output2556.1‖ ≤ (sharedN02700PlusP008Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP008BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP008Output2556,
    kernelN02700PlusP008Center2555, kernelN02700PlusP008Error2555, embedPair2542]

theorem sharedN02700PlusP008Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP008Output2556.1) + embedPair2542
            sharedN02700PlusP008Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP008Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP008Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP008Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP008Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP008Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP008Output2556, pairMagnitude2542]

def sharedN02700PlusP009Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP009Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP009Output2556.1‖ ≤ (sharedN02700PlusP009Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP009BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP009Output2556,
    kernelN02700PlusP009Center2555, kernelN02700PlusP009Error2555, embedPair2542]

theorem sharedN02700PlusP009Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP009Output2556.1) + embedPair2542
            sharedN02700PlusP009Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP009Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP009Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP009Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP009Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP009Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP009Output2556, pairMagnitude2542]

def sharedN02700PlusP010Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP010Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP010Output2556.1‖ ≤ (sharedN02700PlusP010Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP010BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP010Output2556,
    kernelN02700PlusP010Center2555, kernelN02700PlusP010Error2555, embedPair2542]

theorem sharedN02700PlusP010Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP010Output2556.1) + embedPair2542
            sharedN02700PlusP010Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP010Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP010Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP010Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP010Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP010Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP010Output2556, pairMagnitude2542]

def sharedN02700PlusP011Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP011Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP011Output2556.1‖ ≤ (sharedN02700PlusP011Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP011BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP011Output2556,
    kernelN02700PlusP011Center2555, kernelN02700PlusP011Error2555, embedPair2542]

theorem sharedN02700PlusP011Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP011Output2556.1) + embedPair2542
            sharedN02700PlusP011Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP011Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP011Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP011Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP011Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP011Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP011Output2556, pairMagnitude2542]

def sharedN02700PlusP012Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP012Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP012Output2556.1‖ ≤ (sharedN02700PlusP012Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP012BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP012Output2556,
    kernelN02700PlusP012Center2555, kernelN02700PlusP012Error2555, embedPair2542]

theorem sharedN02700PlusP012Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP012Output2556.1) + embedPair2542
            sharedN02700PlusP012Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP012Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP012Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP012Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP012Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP012Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP012Output2556, pairMagnitude2542]

def sharedN02700PlusP013Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP013Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP013Output2556.1‖ ≤ (sharedN02700PlusP013Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP013BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP013Output2556,
    kernelN02700PlusP013Center2555, kernelN02700PlusP013Error2555, embedPair2542]

theorem sharedN02700PlusP013Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP013Output2556.1) + embedPair2542
            sharedN02700PlusP013Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP013Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP013Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP013Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP013Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP013Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP013Output2556, pairMagnitude2542]

def sharedN02700PlusP014Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP014Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP014Output2556.1‖ ≤ (sharedN02700PlusP014Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP014BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP014Output2556,
    kernelN02700PlusP014Center2555, kernelN02700PlusP014Error2555, embedPair2542]

theorem sharedN02700PlusP014Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP014Output2556.1) + embedPair2542
            sharedN02700PlusP014Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP014Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP014Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP014Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP014Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP014Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP014Output2556, pairMagnitude2542]

def sharedN02700PlusP015Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP015Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP015Output2556.1‖ ≤ (sharedN02700PlusP015Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP015BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP015Output2556,
    kernelN02700PlusP015Center2555, kernelN02700PlusP015Error2555, embedPair2542]

theorem sharedN02700PlusP015Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP015Output2556.1) + embedPair2542
            sharedN02700PlusP015Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP015Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP015Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP015Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP015Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP015Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP015Output2556, pairMagnitude2542]

def sharedN02700PlusP016Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP016Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP016Output2556.1‖ ≤ (sharedN02700PlusP016Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP016BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP016Output2556,
    kernelN02700PlusP016Center2555, kernelN02700PlusP016Error2555, embedPair2542]

theorem sharedN02700PlusP016Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP016Output2556.1) + embedPair2542
            sharedN02700PlusP016Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP016Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP016Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP016Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP016Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP016Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP016Output2556, pairMagnitude2542]

def sharedN02700PlusP017Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP017Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP017Output2556.1‖ ≤ (sharedN02700PlusP017Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP017BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP017Output2556,
    kernelN02700PlusP017Center2555, kernelN02700PlusP017Error2555, embedPair2542]

theorem sharedN02700PlusP017Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP017Output2556.1) + embedPair2542
            sharedN02700PlusP017Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP017Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP017Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP017Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP017Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP017Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP017Output2556, pairMagnitude2542]

def sharedN02700PlusP018Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP018Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP018Output2556.1‖ ≤ (sharedN02700PlusP018Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP018BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP018Output2556,
    kernelN02700PlusP018Center2555, kernelN02700PlusP018Error2555, embedPair2542]

theorem sharedN02700PlusP018Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP018Output2556.1) + embedPair2542
            sharedN02700PlusP018Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP018Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP018Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP018Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP018Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP018Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP018Output2556, pairMagnitude2542]

def sharedN02700PlusP019Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP019Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP019Output2556.1‖ ≤ (sharedN02700PlusP019Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP019BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP019Output2556,
    kernelN02700PlusP019Center2555, kernelN02700PlusP019Error2555, embedPair2542]

theorem sharedN02700PlusP019Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP019Output2556.1) + embedPair2542
            sharedN02700PlusP019Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP019Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP019Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP019Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP019Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP019Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP019Output2556, pairMagnitude2542]

def sharedN02700PlusP020Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP020Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP020Output2556.1‖ ≤ (sharedN02700PlusP020Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP020BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP020Output2556,
    kernelN02700PlusP020Center2555, kernelN02700PlusP020Error2555, embedPair2542]

theorem sharedN02700PlusP020Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP020Output2556.1) + embedPair2542
            sharedN02700PlusP020Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP020Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP020Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP020Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP020Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP020Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP020Output2556, pairMagnitude2542]

def sharedN02700PlusP021Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP021Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP021Output2556.1‖ ≤ (sharedN02700PlusP021Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP021BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP021Output2556,
    kernelN02700PlusP021Center2555, kernelN02700PlusP021Error2555, embedPair2542]

theorem sharedN02700PlusP021Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP021Output2556.1) + embedPair2542
            sharedN02700PlusP021Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP021Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP021Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP021Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP021Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP021Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP021Output2556, pairMagnitude2542]

def sharedN02700PlusP022Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP022Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP022Output2556.1‖ ≤ (sharedN02700PlusP022Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP022BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP022Output2556,
    kernelN02700PlusP022Center2555, kernelN02700PlusP022Error2555, embedPair2542]

theorem sharedN02700PlusP022Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP022Output2556.1) + embedPair2542
            sharedN02700PlusP022Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP022Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP022Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP022Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP022Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP022Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP022Output2556, pairMagnitude2542]

def sharedN02700PlusP023Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP023Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP023Output2556.1‖ ≤ (sharedN02700PlusP023Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP023BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP023Output2556,
    kernelN02700PlusP023Center2555, kernelN02700PlusP023Error2555, embedPair2542]

theorem sharedN02700PlusP023Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP023Output2556.1) + embedPair2542
            sharedN02700PlusP023Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP023Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP023Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP023Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP023Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP023Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP023Output2556, pairMagnitude2542]

def sharedN02700PlusP024Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP024Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP024Output2556.1‖ ≤ (sharedN02700PlusP024Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP024BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP024Output2556,
    kernelN02700PlusP024Center2555, kernelN02700PlusP024Error2555, embedPair2542]

theorem sharedN02700PlusP024Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP024Output2556.1) + embedPair2542
            sharedN02700PlusP024Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP024Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP024Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP024Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP024Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP024Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP024Output2556, pairMagnitude2542]

def sharedN02700PlusP025Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP025Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP025Output2556.1‖ ≤ (sharedN02700PlusP025Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP025BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP025Output2556,
    kernelN02700PlusP025Center2555, kernelN02700PlusP025Error2555, embedPair2542]

theorem sharedN02700PlusP025Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP025Output2556.1) + embedPair2542
            sharedN02700PlusP025Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP025Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP025Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP025Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP025Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP025Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP025Output2556, pairMagnitude2542]

def sharedN02700PlusP026Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP026Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP026Output2556.1‖ ≤ (sharedN02700PlusP026Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP026BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP026Output2556,
    kernelN02700PlusP026Center2555, kernelN02700PlusP026Error2555, embedPair2542]

theorem sharedN02700PlusP026Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP026Output2556.1) + embedPair2542
            sharedN02700PlusP026Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP026Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP026Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP026Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP026Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP026Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP026Output2556, pairMagnitude2542]

def sharedN02700PlusP027Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP027Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP027Output2556.1‖ ≤ (sharedN02700PlusP027Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP027BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP027Output2556,
    kernelN02700PlusP027Center2555, kernelN02700PlusP027Error2555, embedPair2542]

theorem sharedN02700PlusP027Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP027Output2556.1) + embedPair2542
            sharedN02700PlusP027Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP027Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP027Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP027Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP027Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP027Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP027Output2556, pairMagnitude2542]

def sharedN02700PlusP028Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP028Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP028Output2556.1‖ ≤ (sharedN02700PlusP028Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP028BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP028Output2556,
    kernelN02700PlusP028Center2555, kernelN02700PlusP028Error2555, embedPair2542]

theorem sharedN02700PlusP028Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP028Output2556.1) + embedPair2542
            sharedN02700PlusP028Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP028Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP028Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP028Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP028Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP028Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP028Output2556, pairMagnitude2542]

def sharedN02700PlusP029Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700PlusP029Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP029Output2556.1‖ ≤ (sharedN02700PlusP029Output2556.2 : ℝ) := by
  have h := kernelN02700PlusP029BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700PlusPosition2556, kernelN02700PlusPosition2555,
      sharedN02700PlusP029Output2556,
    kernelN02700PlusP029Center2555, kernelN02700PlusP029Error2555, embedPair2542]

theorem sharedN02700PlusP029Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02700PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02700PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP029Output2556.1) + embedPair2542
            sharedN02700PlusP029Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02700PlusPosition2556 - embedPair2542
            sharedN02700PlusP029Output2556.1‖ + ‖embedPair2542
            sharedN02700PlusP029Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700PlusP029Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700PlusP029Output2556.1 : ℝ) :=
      add_le_add sharedN02700PlusP029Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700PlusP029Output2556, pairMagnitude2542]

noncomputable def sharedN02700PlusValue2556 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 sharedN02700PlusP000Output2556.1
  | 1 => embedPair2542 sharedN02700PlusP001Output2556.1
  | 2 => embedPair2542 sharedN02700PlusP002Output2556.1
  | 3 => embedPair2542 sharedN02700PlusP003Output2556.1
  | 4 => embedPair2542 sharedN02700PlusP004Output2556.1
  | 5 => embedPair2542 sharedN02700PlusP005Output2556.1
  | 6 => embedPair2542 sharedN02700PlusP006Output2556.1
  | 7 => embedPair2542 sharedN02700PlusP007Output2556.1
  | 8 => embedPair2542 sharedN02700PlusP008Output2556.1
  | 9 => embedPair2542 sharedN02700PlusP009Output2556.1
  | 10 => embedPair2542 sharedN02700PlusP010Output2556.1
  | 11 => embedPair2542 sharedN02700PlusP011Output2556.1
  | 12 => embedPair2542 sharedN02700PlusP012Output2556.1
  | 13 => embedPair2542 sharedN02700PlusP013Output2556.1
  | 14 => embedPair2542 sharedN02700PlusP014Output2556.1
  | 15 => embedPair2542 sharedN02700PlusP015Output2556.1
  | 16 => embedPair2542 sharedN02700PlusP016Output2556.1
  | 17 => embedPair2542 sharedN02700PlusP017Output2556.1
  | 18 => embedPair2542 sharedN02700PlusP018Output2556.1
  | 19 => embedPair2542 sharedN02700PlusP019Output2556.1
  | 20 => embedPair2542 sharedN02700PlusP020Output2556.1
  | 21 => embedPair2542 sharedN02700PlusP021Output2556.1
  | 22 => embedPair2542 sharedN02700PlusP022Output2556.1
  | 23 => embedPair2542 sharedN02700PlusP023Output2556.1
  | 24 => embedPair2542 sharedN02700PlusP024Output2556.1
  | 25 => embedPair2542 sharedN02700PlusP025Output2556.1
  | 26 => embedPair2542 sharedN02700PlusP026Output2556.1
  | 27 => embedPair2542 sharedN02700PlusP027Output2556.1
  | 28 => embedPair2542 sharedN02700PlusP028Output2556.1
  | 29 => embedPair2542 sharedN02700PlusP029Output2556.1
  | _ => 0

noncomputable def sharedN02700PlusError2556 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (sharedN02700PlusP000Output2556.2 : ℝ)
  | 1 => (sharedN02700PlusP001Output2556.2 : ℝ)
  | 2 => (sharedN02700PlusP002Output2556.2 : ℝ)
  | 3 => (sharedN02700PlusP003Output2556.2 : ℝ)
  | 4 => (sharedN02700PlusP004Output2556.2 : ℝ)
  | 5 => (sharedN02700PlusP005Output2556.2 : ℝ)
  | 6 => (sharedN02700PlusP006Output2556.2 : ℝ)
  | 7 => (sharedN02700PlusP007Output2556.2 : ℝ)
  | 8 => (sharedN02700PlusP008Output2556.2 : ℝ)
  | 9 => (sharedN02700PlusP009Output2556.2 : ℝ)
  | 10 => (sharedN02700PlusP010Output2556.2 : ℝ)
  | 11 => (sharedN02700PlusP011Output2556.2 : ℝ)
  | 12 => (sharedN02700PlusP012Output2556.2 : ℝ)
  | 13 => (sharedN02700PlusP013Output2556.2 : ℝ)
  | 14 => (sharedN02700PlusP014Output2556.2 : ℝ)
  | 15 => (sharedN02700PlusP015Output2556.2 : ℝ)
  | 16 => (sharedN02700PlusP016Output2556.2 : ℝ)
  | 17 => (sharedN02700PlusP017Output2556.2 : ℝ)
  | 18 => (sharedN02700PlusP018Output2556.2 : ℝ)
  | 19 => (sharedN02700PlusP019Output2556.2 : ℝ)
  | 20 => (sharedN02700PlusP020Output2556.2 : ℝ)
  | 21 => (sharedN02700PlusP021Output2556.2 : ℝ)
  | 22 => (sharedN02700PlusP022Output2556.2 : ℝ)
  | 23 => (sharedN02700PlusP023Output2556.2 : ℝ)
  | 24 => (sharedN02700PlusP024Output2556.2 : ℝ)
  | 25 => (sharedN02700PlusP025Output2556.2 : ℝ)
  | 26 => (sharedN02700PlusP026Output2556.2 : ℝ)
  | 27 => (sharedN02700PlusP027Output2556.2 : ℝ)
  | 28 => (sharedN02700PlusP028Output2556.2 : ℝ)
  | 29 => (sharedN02700PlusP029Output2556.2 : ℝ)
  | _ => 0

theorem sharedN02700PlusExp_error2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN02700PlusPosition2556 - sharedN02700PlusValue2556 i‖ ≤
            sharedN02700PlusError2556 i := by
  fin_cases i
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP000Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP001Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP002Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP003Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP004Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP005Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP006Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP007Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP008Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP009Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP010Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP011Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP012Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP013Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP014Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP015Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP016Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP017Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP018Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP019Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP020Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP021Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP022Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP023Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP024Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP025Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP026Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP027Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP028Error2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP029Error2556

theorem sharedN02700PlusUnit_norm2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN02700PlusPosition2556‖ ≤ 1 := by
  fin_cases i
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP000Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP001Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP002Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP003Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP004Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP005Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP006Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP007Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP008Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP009Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP010Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP011Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP012Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP013Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP014Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP015Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP016Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP017Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP018Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP019Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP020Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP021Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP022Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP023Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP024Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP025Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP026Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP027Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP028Norm2556
  · simpa only [sharedN02700PlusValue2556, sharedN02700PlusError2556] using
      sharedN02700PlusP029Norm2556

noncomputable def sharedN02700PlusSumValue2556 : ℂ := ⟨(((((4180643861073333206 * 10^40
        + 8844754979342903953836086064599189238209) * 10^40
        + 9295887980839229755765643766738097306078) * 10^40
        + 8663676070535544039829373084661564542595) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816)),
    (((((1565216414322702075 * 10^40
        + 2950648998604828704770596954546752376725) * 10^40
        + 9513380151098353215486991662856247196112) * 10^40
        + 6825818751408404956262380374355309026905) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816))⟩

noncomputable def sharedN02700PlusUpper2556 : ℝ := ((179 : ℝ) /
        2000000000)

theorem sharedN02700PlusSum_eq2556 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN02700PlusValue2556 i) =
      sharedN02700PlusSumValue2556 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN02700PlusValue2556,
      sharedN02700PlusSumValue2556, embedPair2542, sharedN02700PlusP000Output2556,
      sharedN02700PlusP001Output2556,
      sharedN02700PlusP002Output2556,
      sharedN02700PlusP003Output2556,
      sharedN02700PlusP004Output2556,
      sharedN02700PlusP005Output2556,
      sharedN02700PlusP006Output2556,
      sharedN02700PlusP007Output2556,
      sharedN02700PlusP008Output2556,
      sharedN02700PlusP009Output2556,
      sharedN02700PlusP010Output2556,
      sharedN02700PlusP011Output2556,
      sharedN02700PlusP012Output2556,
      sharedN02700PlusP013Output2556,
      sharedN02700PlusP014Output2556,
      sharedN02700PlusP015Output2556,
      sharedN02700PlusP016Output2556,
      sharedN02700PlusP017Output2556,
      sharedN02700PlusP018Output2556,
      sharedN02700PlusP019Output2556,
      sharedN02700PlusP020Output2556,
      sharedN02700PlusP021Output2556,
      sharedN02700PlusP022Output2556,
      sharedN02700PlusP023Output2556,
      sharedN02700PlusP024Output2556,
      sharedN02700PlusP025Output2556,
      sharedN02700PlusP026Output2556,
      sharedN02700PlusP027Output2556,
      sharedN02700PlusP028Output2556,
      sharedN02700PlusP029Output2556, Complex.mul_re, Complex.mul_im]

theorem sharedN02700PlusSum_norm2556 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN02700PlusValue2556 i‖ ≤
      ((447 : ℝ) /
        5000000000) := by
  rw [sharedN02700PlusSum_eq2556]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [sharedN02700PlusSumValue2556]

theorem sharedN02700PlusEvaluation_charge2556 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * sharedN02700PlusError2556 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN02700PlusError2556,
      sharedN02700PlusP000Output2556,
      sharedN02700PlusP001Output2556,
      sharedN02700PlusP002Output2556,
      sharedN02700PlusP003Output2556,
      sharedN02700PlusP004Output2556,
      sharedN02700PlusP005Output2556,
      sharedN02700PlusP006Output2556,
      sharedN02700PlusP007Output2556,
      sharedN02700PlusP008Output2556,
      sharedN02700PlusP009Output2556,
      sharedN02700PlusP010Output2556,
      sharedN02700PlusP011Output2556,
      sharedN02700PlusP012Output2556,
      sharedN02700PlusP013Output2556,
      sharedN02700PlusP014Output2556,
      sharedN02700PlusP015Output2556,
      sharedN02700PlusP016Output2556,
      sharedN02700PlusP017Output2556,
      sharedN02700PlusP018Output2556,
      sharedN02700PlusP019Output2556,
      sharedN02700PlusP020Output2556,
      sharedN02700PlusP021Output2556,
      sharedN02700PlusP022Output2556,
      sharedN02700PlusP023Output2556,
      sharedN02700PlusP024Output2556,
      sharedN02700PlusP025Output2556,
      sharedN02700PlusP026Output2556,
      sharedN02700PlusP027Output2556,
      sharedN02700PlusP028Output2556,
      sharedN02700PlusP029Output2556]

theorem sharedN02700PlusSigned_le2556 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 sharedN02700PlusPosition2556 ≤ sharedN02700PlusUpper2556 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN02700PlusPosition2556‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN02700PlusValue2556 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * sharedN02700PlusError2556 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (sharedN02700PlusExp_error2556 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN02700PlusPosition2556‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (sharedN02700PlusUnit_norm2556 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN02700PlusPosition2556‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 sharedN02700PlusUpper2556
  linarith [sharedN02700PlusSum_norm2556, sharedN02700PlusEvaluation_charge2556]

theorem sharedN02700PlusPhysical_le2556 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 sharedN02700PlusPosition2556‖ ≤
      sharedN02700PlusUpper2556 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        sharedN02700PlusPosition2556
  simpa only [iteratedDeriv_zero] using h.trans sharedN02700PlusSigned_le2556

theorem sharedN02700PlusGrid2556 :
    -stripRadius2303 + (2700 : ℝ)*(2*stripRadius2303/10240) = sharedN02700PlusPosition2556 := by
  norm_num [stripRadius2303, sharedN02700PlusPosition2556]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.sharedN02700PlusSigned_le2556
#print axioms ConnesWeilRH.Dev.sharedN02700PlusPhysical_le2556
