import ConnesWeilRH.Dev.C1RouteABatchN05121Plus2559
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchValueN05121PlusPosition2559 : ℝ := ((65536001 : ℝ) /
        51200000000)

def batchValueN05121PlusP000Output2559 : RatState2542 :=
  ((((136675650344030269252347073071421939 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-6872797286010787388910088620076521) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((6448820903775322072938171961219 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05121PlusP000Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP000Output2559.1‖ ≤ (batchValueN05121PlusP000Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP000BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP000Output2559,
    batchN05121PlusP000Center2559, batchN05121PlusP000Error2559, embedPair2542]

theorem batchValueN05121PlusP000Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP000Output2559.1) + embedPair2542
            batchValueN05121PlusP000Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP000Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP000Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP000Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP000Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP000Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP000Output2559, pairMagnitude2542]

def batchValueN05121PlusP001Output2559 : RatState2542 :=
  ((((34169022331674657308501850392852931 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-859102420056758820398799427990755) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))),
    ((6448840969194396923224843774095 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05121PlusP001Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP001Output2559.1‖ ≤ (batchValueN05121PlusP001Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP001BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP001Output2559,
    batchN05121PlusP001Center2559, batchN05121PlusP001Error2559, embedPair2542]

theorem batchValueN05121PlusP001Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP001Output2559.1) + embedPair2542
            batchValueN05121PlusP001Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP001Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP001Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP001Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP001Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP001Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP001Output2559, pairMagnitude2542]

def batchValueN05121PlusP002Output2559 : RatState2542 :=
  ((((68338158254347080611939487125973925 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((6872830784404118670444311461680605 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((3224425676717443754085083480953 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05121PlusP002Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP002Output2559.1‖ ≤ (batchValueN05121PlusP002Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP002BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP002Output2559,
    batchN05121PlusP002Center2559, batchN05121PlusP002Error2559, embedPair2542]

theorem batchValueN05121PlusP002Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP002Output2559.1) + embedPair2542
            batchValueN05121PlusP002Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP002Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP002Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP002Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP002Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP002Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP002Output2559, pairMagnitude2542]

def batchValueN05121PlusP003Output2559 : RatState2542 :=
  ((((68338221762420089606593694935436785 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((6872837171468833084776356793294189 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((6448857159203737902251197562095 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05121PlusP003Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP003Output2559.1‖ ≤ (batchValueN05121PlusP003Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP003BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP003Output2559,
    batchN05121PlusP003Center2559, batchN05121PlusP003Error2559, embedPair2542]

theorem batchValueN05121PlusP003Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP003Output2559.1) + embedPair2542
            batchValueN05121PlusP003Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP003Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP003Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP003Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP003Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP003Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP003Output2559, pairMagnitude2542]

def batchValueN05121PlusP004Output2559 : RatState2542 :=
  ((((68338259500788089704072508966229503 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-3436420483425428194303847513718875) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((3224430304581276660804530147649 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05121PlusP004Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP004Output2559.1‖ ≤ (batchValueN05121PlusP004Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP004BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP004Output2559,
    batchN05121PlusP004Center2559, batchN05121PlusP004Error2559, embedPair2542]

theorem batchValueN05121PlusP004Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP004Output2559.1) + embedPair2542
            batchValueN05121PlusP004Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP004Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP004Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP004Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP004Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP004Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP004Output2559, pairMagnitude2542]

def batchValueN05121PlusP005Output2559 : RatState2542 :=
  ((((68424262043146243304847327298652041 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((3073777350247193428604776321287 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05121PlusP005Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP005Output2559.1‖ ≤ (batchValueN05121PlusP005Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP005BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP005Output2559,
    batchN05121PlusP005Center2559, batchN05121PlusP005Error2559, embedPair2542]

theorem batchValueN05121PlusP005Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP005Output2559.1) + embedPair2542
            batchValueN05121PlusP005Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP005Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP005Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP005Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP005Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP005Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP005Output2559, pairMagnitude2542]

def batchValueN05121PlusP006Output2559 : RatState2542 :=
  ((((17106118510071582424137504584889959 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1)),
    ((12295146304184094802306035054029 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121PlusP006Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP006Output2559.1‖ ≤ (batchValueN05121PlusP006Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP006BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP006Output2559,
    batchN05121PlusP006Center2559, batchN05121PlusP006Error2559, embedPair2542]

theorem batchValueN05121PlusP006Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP006Output2559.1) + embedPair2542
            batchValueN05121PlusP006Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP006Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP006Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP006Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP006Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP006Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP006Output2559, pairMagnitude2542]

def batchValueN05121PlusP007Output2559 : RatState2542 :=
  ((((34212284074386526062500505013302701 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1)),
    ((3073790671506489248495012638049 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05121PlusP007Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP007Output2559.1‖ ≤ (batchValueN05121PlusP007Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP007BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP007Output2559,
    batchN05121PlusP007Center2559, batchN05121PlusP007Error2559, embedPair2542]

theorem batchValueN05121PlusP007Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP007Output2559.1) + embedPair2542
            batchValueN05121PlusP007Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP007Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP007Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP007Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP007Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP007Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP007Output2559, pairMagnitude2542]

def batchValueN05121PlusP008Output2559 : RatState2542 :=
  ((((68413135137079552770706605104777515 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-1237896193845209220366822603002349) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((12511161947040972037249728888013 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121PlusP008Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP008Output2559.1‖ ≤ (batchValueN05121PlusP008Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP008BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP008Output2559,
    batchN05121PlusP008Center2559, batchN05121PlusP008Error2559, embedPair2542]

theorem batchValueN05121PlusP008Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP008Output2559.1) + embedPair2542
            batchValueN05121PlusP008Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP008Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP008Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP008Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP008Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP008Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP008Output2559, pairMagnitude2542]

def batchValueN05121PlusP009Output2559 : RatState2542 :=
  ((((68399563841778805320831794557230777 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-3681908486353679963734542069673773) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12616817366626715925935176043465 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121PlusP009Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP009Output2559.1‖ ≤ (batchValueN05121PlusP009Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP009BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP009Output2559,
    batchN05121PlusP009Center2559, batchN05121PlusP009Error2559, embedPair2542]

theorem batchValueN05121PlusP009Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP009Output2559.1) + embedPair2542
            batchValueN05121PlusP009Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP009Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP009Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP009Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP009Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP009Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP009Output2559, pairMagnitude2542]

def batchValueN05121PlusP010Output2559 : RatState2542 :=
  ((((68389273027037334110125418654915613 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-4380310995529484301465691182839541) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12678122052529378217244052131603 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121PlusP010Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP010Output2559.1‖ ≤ (batchValueN05121PlusP010Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP010BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP010Output2559,
    batchN05121PlusP010Center2559, batchN05121PlusP010Error2559, embedPair2542]

theorem batchValueN05121PlusP010Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP010Output2559.1) + embedPair2542
            batchValueN05121PlusP010Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP010Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP010Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP010Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP010Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP010Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP010Output2559, pairMagnitude2542]

def batchValueN05121PlusP011Output2559 : RatState2542 :=
  ((((136762842509260362310953976544953545 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-1211473634448669590626943653173063) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((12719041660541592984186397425229 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121PlusP011Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP011Output2559.1‖ ≤ (batchValueN05121PlusP011Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP011BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP011Output2559,
    batchN05121PlusP011Center2559, batchN05121PlusP011Error2559, embedPair2542]

theorem batchValueN05121PlusP011Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP011Output2559.1) + embedPair2542
            batchValueN05121PlusP011Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP011Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP011Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP011Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP011Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP011Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP011Output2559, pairMagnitude2542]

def batchValueN05121PlusP012Output2559 : RatState2542 :=
  ((((17093113333274168743473140176742453 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    (((-2664032936088207286472676267953957) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((12761462825337725864745839544313 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121PlusP012Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP012Output2559.1‖ ≤ (batchValueN05121PlusP012Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP012BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP012Output2559,
    batchN05121PlusP012Center2559, batchN05121PlusP012Error2559, embedPair2542]

theorem batchValueN05121PlusP012Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP012Output2559.1) + embedPair2542
            batchValueN05121PlusP012Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP012Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP012Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP012Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP012Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP012Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP012Output2559, pairMagnitude2542]

def batchValueN05121PlusP013Output2559 : RatState2542 :=
  ((((68363540785304809174710801069040455 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-2883702059334717121417477067385601) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((6400077247752853716294087521289 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05121PlusP013Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP013Output2559.1‖ ≤ (batchValueN05121PlusP013Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP013BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP013Output2559,
    batchN05121PlusP013Center2559, batchN05121PlusP013Error2559, embedPair2542]

theorem batchValueN05121PlusP013Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP013Output2559.1) + embedPair2542
            batchValueN05121PlusP013Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP013Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP013Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP013Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP013Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP013Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP013Output2559, pairMagnitude2542]

def batchValueN05121PlusP014Output2559 : RatState2542 :=
  ((((136690322917036379465415611784707965 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-3290646058166263170168716610638361) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((12871930907743310001781199682229 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121PlusP014Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP014Output2559.1‖ ≤ (batchValueN05121PlusP014Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP014BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP014Output2559,
    batchN05121PlusP014Center2559, batchN05121PlusP014Error2559, embedPair2542]

theorem batchValueN05121PlusP014Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP014Output2559.1) + embedPair2542
            batchValueN05121PlusP014Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP014Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP014Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP014Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP014Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP014Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP014Output2559, pairMagnitude2542]

def batchValueN05121PlusP015Output2559 : RatState2542 :=
  ((((136661005905620481834759904936433059 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-1791075967612507525429192615177903) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((403857064041269846621405252083 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168)))

theorem batchValueN05121PlusP015Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP015Output2559.1‖ ≤ (batchValueN05121PlusP015Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP015BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP015Output2559,
    batchN05121PlusP015Center2559, batchN05121PlusP015Error2559, embedPair2542]

theorem batchValueN05121PlusP015Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP015Output2559.1) + embedPair2542
            batchValueN05121PlusP015Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP015Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP015Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP015Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP015Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP015Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP015Output2559, pairMagnitude2542]

def batchValueN05121PlusP016Output2559 : RatState2542 :=
  ((((136638271243340928355018544145654227 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-7585553158166713880790932597287125) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12960675035634320448554100562401 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121PlusP016Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP016Output2559.1‖ ≤ (batchValueN05121PlusP016Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP016BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP016Output2559,
    batchN05121PlusP016Center2559, batchN05121PlusP016Error2559, embedPair2542]

theorem batchValueN05121PlusP016Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP016Output2559.1) + embedPair2542
            batchValueN05121PlusP016Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP016Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP016Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP016Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP016Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP016Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP016Output2559, pairMagnitude2542]

def batchValueN05121PlusP017Output2559 : RatState2542 :=
  ((((8536900004882588456406383771233277 : ℚ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)),
    (((-8403593968232327596358968103838373) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((13033111058234186885931559623125 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121PlusP017Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP017Output2559.1‖ ≤ (batchValueN05121PlusP017Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP017BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP017Output2559,
    batchN05121PlusP017Center2559, batchN05121PlusP017Error2559, embedPair2542]

theorem batchValueN05121PlusP017Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP017Output2559.1) + embedPair2542
            batchValueN05121PlusP017Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP017Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP017Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP017Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP017Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP017Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP017Output2559, pairMagnitude2542]

def batchValueN05121PlusP018Output2559 : RatState2542 :=
  ((((68285512529954108971620731390025879 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-4356400439873010277620403173760417) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((3265131410255233964747771445697 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05121PlusP018Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP018Output2559.1‖ ≤ (batchValueN05121PlusP018Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP018BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP018Output2559,
    batchN05121PlusP018Center2559, batchN05121PlusP018Error2559, embedPair2542]

theorem batchValueN05121PlusP018Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP018Output2559.1) + embedPair2542
            batchValueN05121PlusP018Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP018Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP018Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP018Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP018Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP018Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP018Output2559, pairMagnitude2542]

def batchValueN05121PlusP019Output2559 : RatState2542 :=
  ((((136534233555798974945647184761037397 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-9271507558898859709305576292027189) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((409690937536066655923181125097 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168)))

theorem batchValueN05121PlusP019Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP019Output2559.1‖ ≤ (batchValueN05121PlusP019Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP019BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP019Output2559,
    batchN05121PlusP019Center2559, batchN05121PlusP019Error2559, embedPair2542]

theorem batchValueN05121PlusP019Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP019Output2559.1) + embedPair2542
            batchValueN05121PlusP019Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP019Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP019Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP019Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP019Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP019Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP019Output2559, pairMagnitude2542]

def batchValueN05121PlusP020Output2559 : RatState2542 :=
  ((((136491631671103869188831385599620871 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-4939439969366382832861719874269839) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((13164085247522669006634164507403 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121PlusP020Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP020Output2559.1‖ ≤ (batchValueN05121PlusP020Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP020BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP020Output2559,
    batchN05121PlusP020Center2559, batchN05121PlusP020Error2559, embedPair2542]

theorem batchValueN05121PlusP020Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP020Output2559.1) + embedPair2542
            batchValueN05121PlusP020Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP020Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP020Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP020Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP020Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP020Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP020Output2559, pairMagnitude2542]

def batchValueN05121PlusP021Output2559 : RatState2542 :=
  ((((136454010412523374539035245978191931 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-2596401685784866847514679339887173) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((6604587085869879578309401578647 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05121PlusP021Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP021Output2559.1‖ ≤ (batchValueN05121PlusP021Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP021BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP021Output2559,
    batchN05121PlusP021Center2559, batchN05121PlusP021Error2559, embedPair2542]

theorem batchValueN05121PlusP021Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP021Output2559.1) + embedPair2542
            batchValueN05121PlusP021Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP021Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP021Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP021Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP021Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP021Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP021Output2559, pairMagnitude2542]

def batchValueN05121PlusP022Output2559 : RatState2542 :=
  ((((34108506643302950808937543788515145 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-10644913250201573785885661239050335) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((13232267893962419016699072549841 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121PlusP022Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP022Output2559.1‖ ≤ (batchValueN05121PlusP022Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP022BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP022Output2559,
    batchN05121PlusP022Center2559, batchN05121PlusP022Error2559, embedPair2542]

theorem batchValueN05121PlusP022Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP022Output2559.1) + embedPair2542
            batchValueN05121PlusP022Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP022Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP022Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP022Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP022Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP022Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP022Output2559, pairMagnitude2542]

def batchValueN05121PlusP023Output2559 : RatState2542 :=
  ((((136373651225292125419020342027441741 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-1424040447583044172615839103975485) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))),
    ((13298909874679709891445635516237 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121PlusP023Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP023Output2559.1‖ ≤ (batchValueN05121PlusP023Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP023BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP023Output2559,
    batchN05121PlusP023Center2559, batchN05121PlusP023Error2559, embedPair2542]

theorem batchValueN05121PlusP023Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP023Output2559.1) + embedPair2542
            batchValueN05121PlusP023Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP023Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP023Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP023Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP023Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP023Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP023Output2559, pairMagnitude2542]

def batchValueN05121PlusP024Output2559 : RatState2542 :=
  ((((68172265935803253145831594145190809 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-11735689745245445136949085584649263) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((3332391190051878303674760602877 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05121PlusP024Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP024Output2559.1‖ ≤ (batchValueN05121PlusP024Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP024BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP024Output2559,
    batchN05121PlusP024Center2559, batchN05121PlusP024Error2559, embedPair2542]

theorem batchValueN05121PlusP024Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP024Output2559.1) + embedPair2542
            batchValueN05121PlusP024Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP024Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP024Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP024Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP024Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP024Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP024Output2559, pairMagnitude2542]

def batchValueN05121PlusP025Output2559 : RatState2542 :=
  ((((8519175001980677903851323210829031 : ℚ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)),
    (((-6083051253376584705117455000007425) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((13368025902742731320677342707611 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121PlusP025Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP025Output2559.1‖ ≤ (batchValueN05121PlusP025Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP025BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP025Output2559,
    batchN05121PlusP025Center2559, batchN05121PlusP025Error2559, embedPair2542]

theorem batchValueN05121PlusP025Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP025Output2559.1) + embedPair2542
            batchValueN05121PlusP025Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP025Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP025Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP025Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP025Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP025Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP025Output2559, pairMagnitude2542]

def batchValueN05121PlusP026Output2559 : RatState2542 :=
  ((((34066708954997666427244722471119259 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-3151460382623133289122602883015731) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((3351840201121234744157453580137 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05121PlusP026Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP026Output2559.1‖ ≤ (batchValueN05121PlusP026Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP026BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP026Output2559,
    batchN05121PlusP026Center2559, batchN05121PlusP026Error2559, embedPair2542]

theorem batchValueN05121PlusP026Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP026Output2559.1) + embedPair2542
            batchValueN05121PlusP026Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP026Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP026Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP026Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP026Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP026Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP026Output2559, pairMagnitude2542]

def batchValueN05121PlusP027Output2559 : RatState2542 :=
  ((((68103332828402352451152359566069131 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-13240166756487594975450808456811315) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((841510870720748436607015000339 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336)))

theorem batchValueN05121PlusP027Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP027Output2559.1‖ ≤ (batchValueN05121PlusP027Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP027BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP027Output2559,
    batchN05121PlusP027Center2559, batchN05121PlusP027Error2559, embedPair2542]

theorem batchValueN05121PlusP027Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP027Output2559.1) + embedPair2542
            batchValueN05121PlusP027Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP027Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP027Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP027Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP027Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP027Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP027Output2559, pairMagnitude2542]

def batchValueN05121PlusP028Output2559 : RatState2542 :=
  ((((136182027442187757030512704326884739 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-6745613145211526379369422742946789) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((6743341875678270580910058172461 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05121PlusP028Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP028Output2559.1‖ ≤ (batchValueN05121PlusP028Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP028BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP028Output2559,
    batchN05121PlusP028Center2559, batchN05121PlusP028Error2559, embedPair2542]

theorem batchValueN05121PlusP028Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP028Output2559.1) + embedPair2542
            batchValueN05121PlusP028Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP028Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP028Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP028Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP028Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP028Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP028Output2559, pairMagnitude2542]

def batchValueN05121PlusP029Output2559 : RatState2542 :=
  ((((136143628816801889985754233686278607 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-6936679999773874311481787733388617) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((13520971596804145523611194426485 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121PlusP029Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP029Output2559.1‖ ≤ (batchValueN05121PlusP029Output2559.2 : ℝ) :=
                by
  have h := batchN05121PlusP029BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05121PlusP029Output2559,
    batchN05121PlusP029Center2559, batchN05121PlusP029Error2559, embedPair2542]

theorem batchValueN05121PlusP029Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05121PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05121PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP029Output2559.1) + embedPair2542
            batchValueN05121PlusP029Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05121PlusPosition2559 - embedPair2542
            batchValueN05121PlusP029Output2559.1‖ + ‖embedPair2542
            batchValueN05121PlusP029Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121PlusP029Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121PlusP029Output2559.1 : ℝ) :=
      add_le_add batchValueN05121PlusP029Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121PlusP029Output2559, pairMagnitude2542]

noncomputable def batchValueN05121PlusValue2559 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchValueN05121PlusP000Output2559.1
  | 1 => embedPair2542 batchValueN05121PlusP001Output2559.1
  | 2 => embedPair2542 batchValueN05121PlusP002Output2559.1
  | 3 => embedPair2542 batchValueN05121PlusP003Output2559.1
  | 4 => embedPair2542 batchValueN05121PlusP004Output2559.1
  | 5 => embedPair2542 batchValueN05121PlusP005Output2559.1
  | 6 => embedPair2542 batchValueN05121PlusP006Output2559.1
  | 7 => embedPair2542 batchValueN05121PlusP007Output2559.1
  | 8 => embedPair2542 batchValueN05121PlusP008Output2559.1
  | 9 => embedPair2542 batchValueN05121PlusP009Output2559.1
  | 10 => embedPair2542 batchValueN05121PlusP010Output2559.1
  | 11 => embedPair2542 batchValueN05121PlusP011Output2559.1
  | 12 => embedPair2542 batchValueN05121PlusP012Output2559.1
  | 13 => embedPair2542 batchValueN05121PlusP013Output2559.1
  | 14 => embedPair2542 batchValueN05121PlusP014Output2559.1
  | 15 => embedPair2542 batchValueN05121PlusP015Output2559.1
  | 16 => embedPair2542 batchValueN05121PlusP016Output2559.1
  | 17 => embedPair2542 batchValueN05121PlusP017Output2559.1
  | 18 => embedPair2542 batchValueN05121PlusP018Output2559.1
  | 19 => embedPair2542 batchValueN05121PlusP019Output2559.1
  | 20 => embedPair2542 batchValueN05121PlusP020Output2559.1
  | 21 => embedPair2542 batchValueN05121PlusP021Output2559.1
  | 22 => embedPair2542 batchValueN05121PlusP022Output2559.1
  | 23 => embedPair2542 batchValueN05121PlusP023Output2559.1
  | 24 => embedPair2542 batchValueN05121PlusP024Output2559.1
  | 25 => embedPair2542 batchValueN05121PlusP025Output2559.1
  | 26 => embedPair2542 batchValueN05121PlusP026Output2559.1
  | 27 => embedPair2542 batchValueN05121PlusP027Output2559.1
  | 28 => embedPair2542 batchValueN05121PlusP028Output2559.1
  | 29 => embedPair2542 batchValueN05121PlusP029Output2559.1
  | _ => 0

noncomputable def batchValueN05121PlusError2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (batchValueN05121PlusP000Output2559.2 : ℝ)
  | 1 => (batchValueN05121PlusP001Output2559.2 : ℝ)
  | 2 => (batchValueN05121PlusP002Output2559.2 : ℝ)
  | 3 => (batchValueN05121PlusP003Output2559.2 : ℝ)
  | 4 => (batchValueN05121PlusP004Output2559.2 : ℝ)
  | 5 => (batchValueN05121PlusP005Output2559.2 : ℝ)
  | 6 => (batchValueN05121PlusP006Output2559.2 : ℝ)
  | 7 => (batchValueN05121PlusP007Output2559.2 : ℝ)
  | 8 => (batchValueN05121PlusP008Output2559.2 : ℝ)
  | 9 => (batchValueN05121PlusP009Output2559.2 : ℝ)
  | 10 => (batchValueN05121PlusP010Output2559.2 : ℝ)
  | 11 => (batchValueN05121PlusP011Output2559.2 : ℝ)
  | 12 => (batchValueN05121PlusP012Output2559.2 : ℝ)
  | 13 => (batchValueN05121PlusP013Output2559.2 : ℝ)
  | 14 => (batchValueN05121PlusP014Output2559.2 : ℝ)
  | 15 => (batchValueN05121PlusP015Output2559.2 : ℝ)
  | 16 => (batchValueN05121PlusP016Output2559.2 : ℝ)
  | 17 => (batchValueN05121PlusP017Output2559.2 : ℝ)
  | 18 => (batchValueN05121PlusP018Output2559.2 : ℝ)
  | 19 => (batchValueN05121PlusP019Output2559.2 : ℝ)
  | 20 => (batchValueN05121PlusP020Output2559.2 : ℝ)
  | 21 => (batchValueN05121PlusP021Output2559.2 : ℝ)
  | 22 => (batchValueN05121PlusP022Output2559.2 : ℝ)
  | 23 => (batchValueN05121PlusP023Output2559.2 : ℝ)
  | 24 => (batchValueN05121PlusP024Output2559.2 : ℝ)
  | 25 => (batchValueN05121PlusP025Output2559.2 : ℝ)
  | 26 => (batchValueN05121PlusP026Output2559.2 : ℝ)
  | 27 => (batchValueN05121PlusP027Output2559.2 : ℝ)
  | 28 => (batchValueN05121PlusP028Output2559.2 : ℝ)
  | 29 => (batchValueN05121PlusP029Output2559.2 : ℝ)
  | _ => 0

theorem batchValueN05121PlusExp_error2559 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05121PlusPosition2559 - batchValueN05121PlusValue2559
            i‖ ≤
            batchValueN05121PlusError2559 i := by
  fin_cases i
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP000Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP001Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP002Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP003Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP004Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP005Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP006Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP007Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP008Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP009Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP010Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP011Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP012Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP013Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP014Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP015Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP016Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP017Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP018Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP019Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP020Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP021Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP022Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP023Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP024Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP025Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP026Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP027Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP028Error2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP029Error2559

theorem batchValueN05121PlusUnit_norm2559 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05121PlusPosition2559‖ ≤ 1 := by
  fin_cases i
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP000Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP001Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP002Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP003Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP004Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP005Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP006Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP007Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP008Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP009Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP010Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP011Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP012Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP013Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP014Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP015Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP016Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP017Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP018Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP019Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP020Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP021Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP022Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP023Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP024Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP025Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP026Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP027Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP028Norm2559
  · simpa only [batchValueN05121PlusValue2559, batchValueN05121PlusError2559] using
      batchValueN05121PlusP029Norm2559

noncomputable def batchValueN05121PlusSumValue2559 : ℂ := ⟨(((((688066044066042545854016389 *
    10^40
        + 5273416299292058046059442955092812716869) * 10^40
        + 6900047579863372577096024231989540137233) * 10^40
        + 1458950605656082146752263170745648975893) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816)),
    (((-(((15705822415319337823972426 * 10^40
        + 9766214567710266064064870988379053864612) * 10^40
        + 7911049333640285180611107048205895103405) * 10^40
        + 9553889550696822690845216280548785412109)) : ℝ) /
        (((24973988402527937851052777 * 10^40
        + 8383453304459887851413197692068732556770) * 10^40
        + 297391055812496096244882450793576927861) * 10^40
        + 5448971252983163583805434306282450321408))⟩

noncomputable def batchValueN05121PlusUpper2559 : ℝ := ((2758000297 : ℝ) /
        200000000)

theorem batchValueN05121PlusSum_eq2559 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05121PlusValue2559 i) =
      batchValueN05121PlusSumValue2559 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN05121PlusValue2559,
      batchValueN05121PlusSumValue2559, embedPair2542, batchValueN05121PlusP000Output2559,
      batchValueN05121PlusP001Output2559,
      batchValueN05121PlusP002Output2559,
      batchValueN05121PlusP003Output2559,
      batchValueN05121PlusP004Output2559,
      batchValueN05121PlusP005Output2559,
      batchValueN05121PlusP006Output2559,
      batchValueN05121PlusP007Output2559,
      batchValueN05121PlusP008Output2559,
      batchValueN05121PlusP009Output2559,
      batchValueN05121PlusP010Output2559,
      batchValueN05121PlusP011Output2559,
      batchValueN05121PlusP012Output2559,
      batchValueN05121PlusP013Output2559,
      batchValueN05121PlusP014Output2559,
      batchValueN05121PlusP015Output2559,
      batchValueN05121PlusP016Output2559,
      batchValueN05121PlusP017Output2559,
      batchValueN05121PlusP018Output2559,
      batchValueN05121PlusP019Output2559,
      batchValueN05121PlusP020Output2559,
      batchValueN05121PlusP021Output2559,
      batchValueN05121PlusP022Output2559,
      batchValueN05121PlusP023Output2559,
      batchValueN05121PlusP024Output2559,
      batchValueN05121PlusP025Output2559,
      batchValueN05121PlusP026Output2559,
      batchValueN05121PlusP027Output2559,
      batchValueN05121PlusP028Output2559,
      batchValueN05121PlusP029Output2559, Complex.mul_re, Complex.mul_im]

theorem batchValueN05121PlusSum_norm2559 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05121PlusValue2559 i‖ ≤
      ((137900014849 : ℝ) /
        10000000000) := by
  rw [batchValueN05121PlusSum_eq2559]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchValueN05121PlusSumValue2559]

theorem batchValueN05121PlusEvaluation_charge2559 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchValueN05121PlusError2559 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN05121PlusError2559,
      batchValueN05121PlusP000Output2559,
      batchValueN05121PlusP001Output2559,
      batchValueN05121PlusP002Output2559,
      batchValueN05121PlusP003Output2559,
      batchValueN05121PlusP004Output2559,
      batchValueN05121PlusP005Output2559,
      batchValueN05121PlusP006Output2559,
      batchValueN05121PlusP007Output2559,
      batchValueN05121PlusP008Output2559,
      batchValueN05121PlusP009Output2559,
      batchValueN05121PlusP010Output2559,
      batchValueN05121PlusP011Output2559,
      batchValueN05121PlusP012Output2559,
      batchValueN05121PlusP013Output2559,
      batchValueN05121PlusP014Output2559,
      batchValueN05121PlusP015Output2559,
      batchValueN05121PlusP016Output2559,
      batchValueN05121PlusP017Output2559,
      batchValueN05121PlusP018Output2559,
      batchValueN05121PlusP019Output2559,
      batchValueN05121PlusP020Output2559,
      batchValueN05121PlusP021Output2559,
      batchValueN05121PlusP022Output2559,
      batchValueN05121PlusP023Output2559,
      batchValueN05121PlusP024Output2559,
      batchValueN05121PlusP025Output2559,
      batchValueN05121PlusP026Output2559,
      batchValueN05121PlusP027Output2559,
      batchValueN05121PlusP028Output2559,
      batchValueN05121PlusP029Output2559]

theorem batchValueN05121PlusSigned_le2559 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchValueN05121PlusPosition2559 ≤ batchValueN05121PlusUpper2559 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05121PlusPosition2559‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05121PlusValue2559 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchValueN05121PlusError2559 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (batchValueN05121PlusExp_error2559 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05121PlusPosition2559‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchValueN05121PlusUnit_norm2559 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05121PlusPosition2559‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchValueN05121PlusUpper2559
  linarith [batchValueN05121PlusSum_norm2559, batchValueN05121PlusEvaluation_charge2559]

theorem batchValueN05121PlusPhysical_le2559 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 batchValueN05121PlusPosition2559‖ ≤
      batchValueN05121PlusUpper2559 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchValueN05121PlusPosition2559
  simpa only [iteratedDeriv_zero] using h.trans batchValueN05121PlusSigned_le2559

theorem batchValueN05121PlusGrid2559 :
    -stripRadius2303 + (5121 : ℝ)*(2*stripRadius2303/10240) = batchValueN05121PlusPosition2559 :=
        by
  norm_num [stripRadius2303, batchValueN05121PlusPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchValueN05121PlusSigned_le2559
#print axioms ConnesWeilRH.Dev.batchValueN05121PlusPhysical_le2559
