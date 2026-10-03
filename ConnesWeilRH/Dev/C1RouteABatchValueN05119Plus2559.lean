import ConnesWeilRH.Dev.C1RouteABatchN05119Plus2559
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchValueN05119PlusPosition2559 : ℝ := (((-65536001) : ℝ) /
        51200000000)

def batchValueN05119PlusP000Output2559 : RatState2542 :=
  ((((136500817425860321500904602802190359 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((3432002866572359709692667475568657 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((12881658643075348419056961036223 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP000Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP000Output2559.1‖ ≤ (batchValueN05119PlusP000Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP000BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP000Output2559,
    batchN05119PlusP000Center2559, batchN05119PlusP000Error2559, embedPair2542]

theorem batchValueN05119PlusP000Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP000Output2559.1) + embedPair2542
            batchValueN05119PlusP000Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP000Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP000Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP000Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP000Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP000Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP000Output2559, pairMagnitude2542]

def batchValueN05119PlusP001Output2559 : RatState2542 :=
  ((((136501255846990318634319534033465733 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((6864027779350790431441383050582143 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((6440849362091048947774802736935 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05119PlusP001Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP001Output2559.1‖ ≤ (batchValueN05119PlusP001Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP001BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP001Output2559,
    batchN05119PlusP001Center2559, batchN05119PlusP001Error2559, embedPair2542]

theorem batchValueN05119PlusP001Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP001Output2559.1) + embedPair2542
            batchValueN05119PlusP001Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP001Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP001Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP001Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP001Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP001Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP001Output2559, pairMagnitude2542]

def batchValueN05119PlusP002Output2559 : RatState2542 :=
  ((((68250741369189460011026049908270463 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-3432019594343768381238143401513287) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((12881719466926122466927883876781 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP002Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP002Output2559.1‖ ≤ (batchValueN05119PlusP002Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP002BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP002Output2559,
    batchN05119PlusP002Center2559, batchN05119PlusP002Error2559, embedPair2542]

theorem batchValueN05119PlusP002Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP002Output2559.1) + embedPair2542
            batchValueN05119PlusP002Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP002Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP002Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP002Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP002Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP002Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP002Output2559, pairMagnitude2542]

def batchValueN05119PlusP003Output2559 : RatState2542 :=
  ((((68250804796024137938191755620644039 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-3432022783791019134728763512362665) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((3220432766018609887051501160593 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05119PlusP003Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP003Output2559.1‖ ≤ (batchValueN05119PlusP003Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP003BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP003Output2559,
    batchN05119PlusP003Center2559, batchN05119PlusP003Error2559, embedPair2542]

theorem batchValueN05119PlusP003Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP003Output2559.1) + embedPair2542
            batchValueN05119PlusP003Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP003Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP003Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP003Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP003Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP003Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP003Output2559, pairMagnitude2542]

def batchValueN05119PlusP004Output2559 : RatState2542 :=
  ((((17062710621529482086045265539037215 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((6864049358109080360221951170609823 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12881737955441474859053564950183 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP004Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP004Output2559.1‖ ≤ (batchValueN05119PlusP004Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP004BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP004Output2559,
    batchN05119PlusP004Center2559, batchN05119PlusP004Error2559, embedPair2542]

theorem batchValueN05119PlusP004Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP004Output2559.1) + embedPair2542
            batchValueN05119PlusP004Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP004Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP004Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP004Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP004Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP004Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP004Output2559, pairMagnitude2542]

def batchValueN05119PlusP005Output2559 : RatState2542 :=
  ((((136673470031286836338306468367739617 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((6139936456836747326633114671249 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05119PlusP005Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP005Output2559.1‖ ≤ (batchValueN05119PlusP005Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP005BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP005Output2559,
    batchN05119PlusP005Center2559, batchN05119PlusP005Error2559, embedPair2542]

theorem batchValueN05119PlusP005Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP005Output2559.1) + embedPair2542
            batchValueN05119PlusP005Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP005Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP005Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP005Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP005Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP005Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP005Output2559, pairMagnitude2542]

def batchValueN05119PlusP006Output2559 : RatState2542 :=
  ((((17084236685400188774373767127530255 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1)),
    ((6139954885568606149536058363403 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05119PlusP006Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP006Output2559.1‖ ≤ (batchValueN05119PlusP006Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP006BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP006Output2559,
    batchN05119PlusP006Center2559, batchN05119PlusP006Error2559, embedPair2542]

theorem batchValueN05119PlusP006Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP006Output2559.1) + embedPair2542
            batchValueN05119PlusP006Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP006Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP006Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP006Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP006Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP006Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP006Output2559, pairMagnitude2542]

def batchValueN05119PlusP007Output2559 : RatState2542 :=
  ((((68337040729705673475078452725726093 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((12279926132678179428021601892955 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP007Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP007Output2559.1‖ ≤ (batchValueN05119PlusP007Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP007BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP007Output2559,
    batchN05119PlusP007Center2559, batchN05119PlusP007Error2559, embedPair2542]

theorem batchValueN05119PlusP007Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP007Output2559.1) + embedPair2542
            batchValueN05119PlusP007Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP007Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP007Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP007Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP007Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP007Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP007Output2559, pairMagnitude2542]

def batchValueN05119PlusP008Output2559 : RatState2542 :=
  ((((68325622342905436484799832349822655 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((618156350172482479625242240996801 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((12495657720597068928919179654881 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP008Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP008Output2559.1‖ ≤ (batchValueN05119PlusP008Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP008BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP008Output2559,
    batchN05119PlusP008Center2559, batchN05119PlusP008Error2559, embedPair2542]

theorem batchValueN05119PlusP008Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP008Output2559.1) + embedPair2542
            batchValueN05119PlusP008Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP008Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP008Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP008Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP008Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP008Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP008Output2559, pairMagnitude2542]

def batchValueN05119PlusP009Output2559 : RatState2542 :=
  ((((17078017101937518900140786536420235 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((459649832294031300763089470419493 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))),
    ((3150295552163713166720439407129 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05119PlusP009Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP009Output2559.1‖ ≤ (batchValueN05119PlusP009Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP009BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP009Output2559,
    batchN05119PlusP009Center2559, batchN05119PlusP009Error2559, embedPair2542]

theorem batchValueN05119PlusP009Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP009Output2559.1) + embedPair2542
            batchValueN05119PlusP009Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP009Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP009Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP009Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP009Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP009Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP009Output2559, pairMagnitude2542]

def batchValueN05119PlusP010Output2559 : RatState2542 :=
  ((((34150895378412517260951066159778865 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((4374707784189990731171144820701449 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((6331205461928702441632722340293 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05119PlusP010Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP010Output2559.1‖ ≤ (batchValueN05119PlusP010Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP010BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP010Output2559,
    batchN05119PlusP010Center2559, batchN05119PlusP010Error2559, embedPair2542]

theorem batchValueN05119PlusP010Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP010Output2559.1) + embedPair2542
            batchValueN05119PlusP010Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP010Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP010Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP010Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP010Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP010Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP010Output2559, pairMagnitude2542]

def batchValueN05119PlusP011Output2559 : RatState2542 :=
  ((((136587898056514574882487620153157195 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((4839695760755360189548135580818693 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((3175819955750226711556527560723 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05119PlusP011Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP011Output2559.1‖ ≤ (batchValueN05119PlusP011Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP011BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP011Output2559,
    batchN05119PlusP011Center2559, batchN05119PlusP011Error2559, embedPair2542]

theorem batchValueN05119PlusP011Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP011Output2559.1) + embedPair2542
            batchValueN05119PlusP011Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP011Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP011Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP011Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP011Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP011Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP011Output2559, pairMagnitude2542]

def batchValueN05119PlusP012Output2559 : RatState2542 :=
  ((((136569985156640262541922752597216529 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((332578144415372647539056407421451 : ℚ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))),
    ((12745648418151806341403167315331 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP012Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP012Output2559.1‖ ≤ (batchValueN05119PlusP012Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP012BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP012Output2559,
    batchN05119PlusP012Center2559, batchN05119PlusP012Error2559, embedPair2542]

theorem batchValueN05119PlusP012Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP012Output2559.1) + embedPair2542
            batchValueN05119PlusP012Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP012Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP012Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP012Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP012Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP012Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP012Output2559, pairMagnitude2542]

def batchValueN05119PlusP013Output2559 : RatState2542 :=
  ((((68276091431291567924075361002274879 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((5760026563927281923243175505227791 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12784292140381913196007361187239 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP013Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP013Output2559.1‖ ≤ (batchValueN05119PlusP013Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP013BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP013Output2559,
    batchN05119PlusP013Center2559, batchN05119PlusP013Error2559, embedPair2542]

theorem batchValueN05119PlusP013Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP013Output2559.1) + embedPair2542
            batchValueN05119PlusP013Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP013Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP013Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP013Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP013Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP013Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP013Output2559, pairMagnitude2542]

def batchValueN05119PlusP014Output2559 : RatState2542 :=
  ((((136515471229987342697102690921951069 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((1643218362847538391886509892120143 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((6427989802512944552770335821299 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05119PlusP014Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP014Output2559.1‖ ≤ (batchValueN05119PlusP014Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP014BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP014Output2559,
    batchN05119PlusP014Center2559, batchN05119PlusP014Error2559, embedPair2542]

theorem batchValueN05119PlusP014Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP014Output2559.1) + embedPair2542
            batchValueN05119PlusP014Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP014Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP014Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP014Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP014Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP014Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP014Output2559, pairMagnitude2542]

def batchValueN05119PlusP015Output2559 : RatState2542 :=
  ((((136486191720340377288908220414040657 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((7155139427850531329191306651274829 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12907410932199791456265434005263 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP015Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP015Output2559.1‖ ≤ (batchValueN05119PlusP015Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP015BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP015Output2559,
    batchN05119PlusP015Center2559, batchN05119PlusP015Error2559, embedPair2542]

theorem batchValueN05119PlusP015Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP015Output2559.1) + embedPair2542
            batchValueN05119PlusP015Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP015Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP015Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP015Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP015Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP015Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP015Output2559, pairMagnitude2542]

def batchValueN05119PlusP016Output2559 : RatState2542 :=
  ((((136463486139812693564813795357287141 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((1893962465352736764012372614639977 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((12944613758394931643391090394651 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP016Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP016Output2559.1‖ ≤ (batchValueN05119PlusP016Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP016BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP016Output2559,
    batchN05119PlusP016Center2559, batchN05119PlusP016Error2559, embedPair2542]

theorem batchValueN05119PlusP016Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP016Output2559.1) + embedPair2542
            batchValueN05119PlusP016Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP016Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP016Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP016Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP016Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP016Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP016Output2559, pairMagnitude2542]

def batchValueN05119PlusP017Output2559 : RatState2542 :=
  ((((136415676210486263560913340223322917 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((2098211062269229239063800347812243 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((6508480007995604327801519311485 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05119PlusP017Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP017Output2559.1‖ ≤ (batchValueN05119PlusP017Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP017BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP017Output2559,
    batchN05119PlusP017Center2559, batchN05119PlusP017Error2559, embedPair2542]

theorem batchValueN05119PlusP017Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP017Output2559.1) + embedPair2542
            batchValueN05119PlusP017Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP017Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP017Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP017Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP017Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP017Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP017Output2559, pairMagnitude2542]

def batchValueN05119PlusP018Output2559 : RatState2542 :=
  ((((34099081494107878000368747841990865 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((8701655628932101754443427486953391 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((13044340625762406390314361543371 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP018Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP018Output2559.1‖ ≤ (batchValueN05119PlusP018Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP018BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP018Output2559,
    batchN05119PlusP018Center2559, batchN05119PlusP018Error2559, embedPair2542]

theorem batchValueN05119PlusP018Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP018Output2559.1) + embedPair2542
            batchValueN05119PlusP018Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP018Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP018Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP018Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP018Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP018Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP018Output2559, pairMagnitude2542]

def batchValueN05119PlusP019Output2559 : RatState2542 :=
  ((((136359581535321501782222006292740117 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((2314911905255504722830856807450735 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((3273465884848201459230052508107 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05119PlusP019Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP019Output2559.1‖ ≤ (batchValueN05119PlusP019Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP019BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP019Output2559,
    batchN05119PlusP019Center2559, batchN05119PlusP019Error2559, embedPair2542]

theorem batchValueN05119PlusP019Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP019Output2559.1) + embedPair2542
            batchValueN05119PlusP019Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP019Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP019Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP019Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP019Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP019Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP019Output2559, pairMagnitude2542]

def batchValueN05119PlusP020Output2559 : RatState2542 :=
  ((((68158517073077529248233548624970471 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((4933121530772559661698980588528081 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((13147771897933847848607074750115 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP020Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP020Output2559.1‖ ≤ (batchValueN05119PlusP020Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP020BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP020Output2559,
    batchN05119PlusP020Center2559, batchN05119PlusP020Error2559, embedPair2542]

theorem batchValueN05119PlusP020Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP020Output2559.1) + embedPair2542
            batchValueN05119PlusP020Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP020Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP020Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP020Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP020Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP020Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP020Output2559, pairMagnitude2542]

def batchValueN05119PlusP021Output2559 : RatState2542 :=
  ((((136279461011980091077114577015383379 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((10372321670565837098370678678115289 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((13192804946534098182217288829769 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP021Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP021Output2559.1‖ ≤ (batchValueN05119PlusP021Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP021BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP021Output2559,
    batchN05119PlusP021Center2559, batchN05119PlusP021Error2559, embedPair2542]

theorem batchValueN05119PlusP021Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP021Output2559.1) + embedPair2542
            batchValueN05119PlusP021Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP021Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP021Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP021Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP021Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP021Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP021Output2559, pairMagnitude2542]

def batchValueN05119PlusP022Output2559 : RatState2542 :=
  ((((136259502735619449854657829734465215 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((10631296477627131283789678185309895 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((825991878142992683952069869231 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336)))

theorem batchValueN05119PlusP022Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP022Output2559.1‖ ≤ (batchValueN05119PlusP022Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP022BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP022Output2559,
    batchN05119PlusP022Center2559, batchN05119PlusP022Error2559, embedPair2542]

theorem batchValueN05119PlusP022Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP022Output2559.1) + embedPair2542
            batchValueN05119PlusP022Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP022Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP022Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP022Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP022Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP022Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP022Output2559, pairMagnitude2542]

def batchValueN05119PlusP023Output2559 : RatState2542 :=
  ((((136199204618707897869796079847515455 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((11377750734869726781486693679313987 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((13282429446161009485739197185313 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP023Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP023Output2559.1‖ ≤ (batchValueN05119PlusP023Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP023BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP023Output2559,
    batchN05119PlusP023Center2559, batchN05119PlusP023Error2559, embedPair2542]

theorem batchValueN05119PlusP023Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP023Output2559.1) + embedPair2542
            batchValueN05119PlusP023Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP023Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP023Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP023Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP023Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP023Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP023Output2559, pairMagnitude2542]

def batchValueN05119PlusP024Output2559 : RatState2542 :=
  ((((136170122513951164501213750743429735 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((5860338835959521097523383063763275 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((416032698224622400720861711269 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168)))

theorem batchValueN05119PlusP024Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP024Output2559.1‖ ≤ (batchValueN05119PlusP024Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP024BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP024Output2559,
    batchN05119PlusP024Center2559, batchN05119PlusP024Error2559, embedPair2542]

theorem batchValueN05119PlusP024Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP024Output2559.1) + embedPair2542
            batchValueN05119PlusP024Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP024Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP024Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP024Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP024Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP024Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP024Output2559, pairMagnitude2542]

def batchValueN05119PlusP025Output2559 : RatState2542 :=
  ((((34033109734973648369730144164083891 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((6075269928763691513585373015931861 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((13351459823462372787032717524695 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP025Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP025Output2559.1‖ ≤ (batchValueN05119PlusP025Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP025BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP025Output2559,
    batchN05119PlusP025Center2559, batchN05119PlusP025Error2559, embedPair2542]

theorem batchValueN05119PlusP025Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP025Output2559.1) + embedPair2542
            batchValueN05119PlusP025Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP025Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP025Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP025Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP025Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP025Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP025Output2559, pairMagnitude2542]

def batchValueN05119PlusP026Output2559 : RatState2542 :=
  ((((34023131462415362580258952376753619 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((3147429093847085052822186108505965 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((13390745980153853631447785687381 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP026Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP026Output2559.1‖ ≤ (batchValueN05119PlusP026Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP026BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP026Output2559,
    batchN05119PlusP026Center2559, batchN05119PlusP026Error2559, embedPair2542]

theorem batchValueN05119PlusP026Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP026Output2559.1) + embedPair2542
            batchValueN05119PlusP026Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP026Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP026Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP026Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP026Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP026Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP026Output2559, pairMagnitude2542]

def batchValueN05119PlusP027Output2559 : RatState2542 :=
  ((((136032432655015167825611034479563907 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((3305807546124834590887137723935529 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((6723744351291080908153136387505 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05119PlusP027Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP027Output2559.1‖ ≤ (batchValueN05119PlusP027Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP027BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP027Output2559,
    batchN05119PlusP027Center2559, batchN05119PlusP027Error2559, embedPair2542]

theorem batchValueN05119PlusP027Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP027Output2559.1) + embedPair2542
            batchValueN05119PlusP027Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP027Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP027Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP027Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP027Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP027Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP027Output2559, pairMagnitude2542]

def batchValueN05119PlusP028Output2559 : RatState2542 :=
  ((((136007825957138393757603533801864003 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((13473968567806708132812455163415457 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((13469970627528118889679392474365 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP028Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP028Output2559.1‖ ≤ (batchValueN05119PlusP028Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP028BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP028Output2559,
    batchN05119PlusP028Center2559, batchN05119PlusP028Error2559, embedPair2542]

theorem batchValueN05119PlusP028Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP028Output2559.1) + embedPair2542
            batchValueN05119PlusP028Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP028Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP028Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP028Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP028Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP028Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP028Output2559, pairMagnitude2542]

def batchValueN05119PlusP029Output2559 : RatState2542 :=
  ((((33992369112637758179745966761293041 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((3463903364671670554359636283511105 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((13504215982396323554612879049929 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119PlusP029Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP029Output2559.1‖ ≤ (batchValueN05119PlusP029Output2559.2 : ℝ) :=
                by
  have h := batchN05119PlusP029BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559,
      batchValueN05119PlusP029Output2559,
    batchN05119PlusP029Center2559, batchN05119PlusP029Error2559, embedPair2542]

theorem batchValueN05119PlusP029Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05119PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05119PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP029Output2559.1) + embedPair2542
            batchValueN05119PlusP029Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05119PlusPosition2559 - embedPair2542
            batchValueN05119PlusP029Output2559.1‖ + ‖embedPair2542
            batchValueN05119PlusP029Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119PlusP029Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119PlusP029Output2559.1 : ℝ) :=
      add_le_add batchValueN05119PlusP029Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119PlusP029Output2559, pairMagnitude2542]

noncomputable def batchValueN05119PlusValue2559 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchValueN05119PlusP000Output2559.1
  | 1 => embedPair2542 batchValueN05119PlusP001Output2559.1
  | 2 => embedPair2542 batchValueN05119PlusP002Output2559.1
  | 3 => embedPair2542 batchValueN05119PlusP003Output2559.1
  | 4 => embedPair2542 batchValueN05119PlusP004Output2559.1
  | 5 => embedPair2542 batchValueN05119PlusP005Output2559.1
  | 6 => embedPair2542 batchValueN05119PlusP006Output2559.1
  | 7 => embedPair2542 batchValueN05119PlusP007Output2559.1
  | 8 => embedPair2542 batchValueN05119PlusP008Output2559.1
  | 9 => embedPair2542 batchValueN05119PlusP009Output2559.1
  | 10 => embedPair2542 batchValueN05119PlusP010Output2559.1
  | 11 => embedPair2542 batchValueN05119PlusP011Output2559.1
  | 12 => embedPair2542 batchValueN05119PlusP012Output2559.1
  | 13 => embedPair2542 batchValueN05119PlusP013Output2559.1
  | 14 => embedPair2542 batchValueN05119PlusP014Output2559.1
  | 15 => embedPair2542 batchValueN05119PlusP015Output2559.1
  | 16 => embedPair2542 batchValueN05119PlusP016Output2559.1
  | 17 => embedPair2542 batchValueN05119PlusP017Output2559.1
  | 18 => embedPair2542 batchValueN05119PlusP018Output2559.1
  | 19 => embedPair2542 batchValueN05119PlusP019Output2559.1
  | 20 => embedPair2542 batchValueN05119PlusP020Output2559.1
  | 21 => embedPair2542 batchValueN05119PlusP021Output2559.1
  | 22 => embedPair2542 batchValueN05119PlusP022Output2559.1
  | 23 => embedPair2542 batchValueN05119PlusP023Output2559.1
  | 24 => embedPair2542 batchValueN05119PlusP024Output2559.1
  | 25 => embedPair2542 batchValueN05119PlusP025Output2559.1
  | 26 => embedPair2542 batchValueN05119PlusP026Output2559.1
  | 27 => embedPair2542 batchValueN05119PlusP027Output2559.1
  | 28 => embedPair2542 batchValueN05119PlusP028Output2559.1
  | 29 => embedPair2542 batchValueN05119PlusP029Output2559.1
  | _ => 0

noncomputable def batchValueN05119PlusError2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (batchValueN05119PlusP000Output2559.2 : ℝ)
  | 1 => (batchValueN05119PlusP001Output2559.2 : ℝ)
  | 2 => (batchValueN05119PlusP002Output2559.2 : ℝ)
  | 3 => (batchValueN05119PlusP003Output2559.2 : ℝ)
  | 4 => (batchValueN05119PlusP004Output2559.2 : ℝ)
  | 5 => (batchValueN05119PlusP005Output2559.2 : ℝ)
  | 6 => (batchValueN05119PlusP006Output2559.2 : ℝ)
  | 7 => (batchValueN05119PlusP007Output2559.2 : ℝ)
  | 8 => (batchValueN05119PlusP008Output2559.2 : ℝ)
  | 9 => (batchValueN05119PlusP009Output2559.2 : ℝ)
  | 10 => (batchValueN05119PlusP010Output2559.2 : ℝ)
  | 11 => (batchValueN05119PlusP011Output2559.2 : ℝ)
  | 12 => (batchValueN05119PlusP012Output2559.2 : ℝ)
  | 13 => (batchValueN05119PlusP013Output2559.2 : ℝ)
  | 14 => (batchValueN05119PlusP014Output2559.2 : ℝ)
  | 15 => (batchValueN05119PlusP015Output2559.2 : ℝ)
  | 16 => (batchValueN05119PlusP016Output2559.2 : ℝ)
  | 17 => (batchValueN05119PlusP017Output2559.2 : ℝ)
  | 18 => (batchValueN05119PlusP018Output2559.2 : ℝ)
  | 19 => (batchValueN05119PlusP019Output2559.2 : ℝ)
  | 20 => (batchValueN05119PlusP020Output2559.2 : ℝ)
  | 21 => (batchValueN05119PlusP021Output2559.2 : ℝ)
  | 22 => (batchValueN05119PlusP022Output2559.2 : ℝ)
  | 23 => (batchValueN05119PlusP023Output2559.2 : ℝ)
  | 24 => (batchValueN05119PlusP024Output2559.2 : ℝ)
  | 25 => (batchValueN05119PlusP025Output2559.2 : ℝ)
  | 26 => (batchValueN05119PlusP026Output2559.2 : ℝ)
  | 27 => (batchValueN05119PlusP027Output2559.2 : ℝ)
  | 28 => (batchValueN05119PlusP028Output2559.2 : ℝ)
  | 29 => (batchValueN05119PlusP029Output2559.2 : ℝ)
  | _ => 0

theorem batchValueN05119PlusExp_error2559 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05119PlusPosition2559 - batchValueN05119PlusValue2559
            i‖ ≤
            batchValueN05119PlusError2559 i := by
  fin_cases i
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP000Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP001Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP002Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP003Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP004Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP005Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP006Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP007Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP008Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP009Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP010Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP011Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP012Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP013Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP014Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP015Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP016Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP017Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP018Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP019Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP020Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP021Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP022Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP023Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP024Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP025Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP026Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP027Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP028Error2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP029Error2559

theorem batchValueN05119PlusUnit_norm2559 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05119PlusPosition2559‖ ≤ 1 := by
  fin_cases i
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP000Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP001Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP002Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP003Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP004Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP005Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP006Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP007Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP008Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP009Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP010Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP011Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP012Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP013Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP014Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP015Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP016Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP017Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP018Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP019Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP020Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP021Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP022Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP023Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP024Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP025Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP026Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP027Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP028Norm2559
  · simpa only [batchValueN05119PlusValue2559, batchValueN05119PlusError2559] using
      batchValueN05119PlusP029Norm2559

noncomputable def batchValueN05119PlusSumValue2559 : ℂ := ⟨(((((343748391664697999515070489 *
    10^40
        + 8166621312259024305758389939174744959436) * 10^40
        + 3398069016497549473880877869237545502650) * 10^40
        + 2567786342329108058941457566617184741385) : ℝ) /
        (((24973988402527937851052777 * 10^40
        + 8383453304459887851413197692068732556770) * 10^40
        + 297391055812496096244882450793576927861) * 10^40
        + 5448971252983163583805434306282450321408)),
    (((((15783718004084168021992884 * 10^40
        + 7209173129949140541752747386686729119176) * 10^40
        + 6338390740048179639637957303268136273017) * 10^40
        + 8748318147168279066337498548927064187065) : ℝ) /
        (((24973988402527937851052777 * 10^40
        + 8383453304459887851413197692068732556770) * 10^40
        + 297391055812496096244882450793576927861) * 10^40
        + 5448971252983163583805434306282450321408))⟩

noncomputable def batchValueN05119PlusUpper2559 : ℝ := ((68893794967 : ℝ) /
        5000000000)

theorem batchValueN05119PlusSum_eq2559 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05119PlusValue2559 i) =
      batchValueN05119PlusSumValue2559 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN05119PlusValue2559,
      batchValueN05119PlusSumValue2559, embedPair2542, batchValueN05119PlusP000Output2559,
      batchValueN05119PlusP001Output2559,
      batchValueN05119PlusP002Output2559,
      batchValueN05119PlusP003Output2559,
      batchValueN05119PlusP004Output2559,
      batchValueN05119PlusP005Output2559,
      batchValueN05119PlusP006Output2559,
      batchValueN05119PlusP007Output2559,
      batchValueN05119PlusP008Output2559,
      batchValueN05119PlusP009Output2559,
      batchValueN05119PlusP010Output2559,
      batchValueN05119PlusP011Output2559,
      batchValueN05119PlusP012Output2559,
      batchValueN05119PlusP013Output2559,
      batchValueN05119PlusP014Output2559,
      batchValueN05119PlusP015Output2559,
      batchValueN05119PlusP016Output2559,
      batchValueN05119PlusP017Output2559,
      batchValueN05119PlusP018Output2559,
      batchValueN05119PlusP019Output2559,
      batchValueN05119PlusP020Output2559,
      batchValueN05119PlusP021Output2559,
      batchValueN05119PlusP022Output2559,
      batchValueN05119PlusP023Output2559,
      batchValueN05119PlusP024Output2559,
      batchValueN05119PlusP025Output2559,
      batchValueN05119PlusP026Output2559,
      batchValueN05119PlusP027Output2559,
      batchValueN05119PlusP028Output2559,
      batchValueN05119PlusP029Output2559, Complex.mul_re, Complex.mul_im]

theorem batchValueN05119PlusSum_norm2559 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05119PlusValue2559 i‖ ≤
      ((137787589933 : ℝ) /
        10000000000) := by
  rw [batchValueN05119PlusSum_eq2559]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchValueN05119PlusSumValue2559]

theorem batchValueN05119PlusEvaluation_charge2559 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchValueN05119PlusError2559 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN05119PlusError2559,
      batchValueN05119PlusP000Output2559,
      batchValueN05119PlusP001Output2559,
      batchValueN05119PlusP002Output2559,
      batchValueN05119PlusP003Output2559,
      batchValueN05119PlusP004Output2559,
      batchValueN05119PlusP005Output2559,
      batchValueN05119PlusP006Output2559,
      batchValueN05119PlusP007Output2559,
      batchValueN05119PlusP008Output2559,
      batchValueN05119PlusP009Output2559,
      batchValueN05119PlusP010Output2559,
      batchValueN05119PlusP011Output2559,
      batchValueN05119PlusP012Output2559,
      batchValueN05119PlusP013Output2559,
      batchValueN05119PlusP014Output2559,
      batchValueN05119PlusP015Output2559,
      batchValueN05119PlusP016Output2559,
      batchValueN05119PlusP017Output2559,
      batchValueN05119PlusP018Output2559,
      batchValueN05119PlusP019Output2559,
      batchValueN05119PlusP020Output2559,
      batchValueN05119PlusP021Output2559,
      batchValueN05119PlusP022Output2559,
      batchValueN05119PlusP023Output2559,
      batchValueN05119PlusP024Output2559,
      batchValueN05119PlusP025Output2559,
      batchValueN05119PlusP026Output2559,
      batchValueN05119PlusP027Output2559,
      batchValueN05119PlusP028Output2559,
      batchValueN05119PlusP029Output2559]

theorem batchValueN05119PlusSigned_le2559 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchValueN05119PlusPosition2559 ≤ batchValueN05119PlusUpper2559 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05119PlusPosition2559‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05119PlusValue2559 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchValueN05119PlusError2559 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (batchValueN05119PlusExp_error2559 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05119PlusPosition2559‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchValueN05119PlusUnit_norm2559 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05119PlusPosition2559‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchValueN05119PlusUpper2559
  linarith [batchValueN05119PlusSum_norm2559, batchValueN05119PlusEvaluation_charge2559]

theorem batchValueN05119PlusPhysical_le2559 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 batchValueN05119PlusPosition2559‖ ≤
      batchValueN05119PlusUpper2559 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchValueN05119PlusPosition2559
  simpa only [iteratedDeriv_zero] using h.trans batchValueN05119PlusSigned_le2559

theorem batchValueN05119PlusGrid2559 :
    -stripRadius2303 + (5119 : ℝ)*(2*stripRadius2303/10240) = batchValueN05119PlusPosition2559 :=
        by
  norm_num [stripRadius2303, batchValueN05119PlusPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchValueN05119PlusSigned_le2559
#print axioms ConnesWeilRH.Dev.batchValueN05119PlusPhysical_le2559
