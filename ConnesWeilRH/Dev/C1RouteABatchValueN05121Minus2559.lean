import ConnesWeilRH.Dev.C1RouteABatchN05121Minus2559
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchValueN05121MinusPosition2559 : ℝ := ((65536001 : ℝ) /
        51200000000)

def batchValueN05121MinusP000Output2559 : RatState2542 :=
  ((((136500817425860321500904602802190359 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-6864005733144719419385334951137315) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12881658643075348419056961036223 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP000Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP000Output2559.1‖ ≤ (batchValueN05121MinusP000Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP000BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP000Output2559,
    batchN05121MinusP000Center2559, batchN05121MinusP000Error2559, embedPair2542]

theorem batchValueN05121MinusP000Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP000Output2559.1) + embedPair2542
            batchValueN05121MinusP000Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP000Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP000Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP000Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP000Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP000Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP000Output2559, pairMagnitude2542]

def batchValueN05121MinusP001Output2559 : RatState2542 :=
  ((((136501255846990318634319534033465733 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-53625217026178050245635805082673) : ℚ) /
        (1141798 * 10^40
        + 1541647679048466287755595961091061972992))),
    ((6440849362091048947774802736935 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05121MinusP001Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP001Output2559.1‖ ≤ (batchValueN05121MinusP001Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP001BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP001Output2559,
    batchN05121MinusP001Center2559, batchN05121MinusP001Error2559, embedPair2542]

theorem batchValueN05121MinusP001Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP001Output2559.1) + embedPair2542
            batchValueN05121MinusP001Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP001Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP001Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP001Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP001Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP001Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP001Output2559, pairMagnitude2542]

def batchValueN05121MinusP002Output2559 : RatState2542 :=
  ((((68250741369189460011026049908270463 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((6864039188687536762476286803026573 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12881719466926122466927883876781 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP002Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP002Output2559.1‖ ≤ (batchValueN05121MinusP002Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP002BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP002Output2559,
    batchN05121MinusP002Center2559, batchN05121MinusP002Error2559, embedPair2542]

theorem batchValueN05121MinusP002Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP002Output2559.1) + embedPair2542
            batchValueN05121MinusP002Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP002Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP002Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP002Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP002Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP002Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP002Output2559, pairMagnitude2542]

def batchValueN05121MinusP003Output2559 : RatState2542 :=
  ((((68250804796024137938191755620644039 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((6864045567582038269457527024725329 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((3220432766018609887051501160593 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05121MinusP003Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP003Output2559.1‖ ≤ (batchValueN05121MinusP003Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP003BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP003Output2559,
    batchN05121MinusP003Center2559, batchN05121MinusP003Error2559, embedPair2542]

theorem batchValueN05121MinusP003Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP003Output2559.1) + embedPair2542
            batchValueN05121MinusP003Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP003Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP003Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP003Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP003Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP003Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP003Output2559, pairMagnitude2542]

def batchValueN05121MinusP004Output2559 : RatState2542 :=
  ((((17062710621529482086045265539037215 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    (((-214501542440908761256935974081557) : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968))),
    ((12881737955441474859053564950183 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP004Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP004Output2559.1‖ ≤ (batchValueN05121MinusP004Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP004BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP004Output2559,
    batchN05121MinusP004Center2559, batchN05121MinusP004Error2559, embedPair2542]

theorem batchValueN05121MinusP004Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP004Output2559.1) + embedPair2542
            batchValueN05121MinusP004Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP004Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP004Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP004Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP004Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP004Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP004Output2559, pairMagnitude2542]

def batchValueN05121MinusP005Output2559 : RatState2542 :=
  ((((136673470031286836338306468367739617 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((6139936456836747326633114671249 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05121MinusP005Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP005Output2559.1‖ ≤ (batchValueN05121MinusP005Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP005BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP005Output2559,
    batchN05121MinusP005Center2559, batchN05121MinusP005Error2559, embedPair2542]

theorem batchValueN05121MinusP005Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP005Output2559.1) + embedPair2542
            batchValueN05121MinusP005Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP005Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP005Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP005Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP005Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP005Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP005Output2559, pairMagnitude2542]

def batchValueN05121MinusP006Output2559 : RatState2542 :=
  ((((17084236685400188774373767127530255 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1)),
    ((6139954885568606149536058363403 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05121MinusP006Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP006Output2559.1‖ ≤ (batchValueN05121MinusP006Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP006BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP006Output2559,
    batchN05121MinusP006Center2559, batchN05121MinusP006Error2559, embedPair2542]

theorem batchValueN05121MinusP006Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP006Output2559.1) + embedPair2542
            batchValueN05121MinusP006Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP006Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP006Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP006Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP006Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP006Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP006Output2559, pairMagnitude2542]

def batchValueN05121MinusP007Output2559 : RatState2542 :=
  ((((68337040729705673475078452725726093 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((12279926132678179428021601892955 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP007Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP007Output2559.1‖ ≤ (batchValueN05121MinusP007Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP007BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP007Output2559,
    batchN05121MinusP007Center2559, batchN05121MinusP007Error2559, embedPair2542]

theorem batchValueN05121MinusP007Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP007Output2559.1) + embedPair2542
            batchValueN05121MinusP007Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP007Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP007Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP007Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP007Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP007Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP007Output2559, pairMagnitude2542]

def batchValueN05121MinusP008Output2559 : RatState2542 :=
  ((((68325622342905436484799832349822655 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-2472625400689929918500968963987205) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12495657720597068928919179654881 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP008Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP008Output2559.1‖ ≤ (batchValueN05121MinusP008Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP008BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP008Output2559,
    batchN05121MinusP008Center2559, batchN05121MinusP008Error2559, embedPair2542]

theorem batchValueN05121MinusP008Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP008Output2559.1) + embedPair2542
            batchValueN05121MinusP008Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP008Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP008Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP008Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP008Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP008Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP008Output2559, pairMagnitude2542]

def batchValueN05121MinusP009Output2559 : RatState2542 :=
  ((((17078017101937518900140786536420235 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    (((-3677198658352250406104715763355945) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((3150295552163713166720439407129 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05121MinusP009Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP009Output2559.1‖ ≤ (batchValueN05121MinusP009Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP009BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP009Output2559,
    batchN05121MinusP009Center2559, batchN05121MinusP009Error2559, embedPair2542]

theorem batchValueN05121MinusP009Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP009Output2559.1) + embedPair2542
            batchValueN05121MinusP009Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP009Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP009Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP009Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP009Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP009Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP009Output2559, pairMagnitude2542]

def batchValueN05121MinusP010Output2559 : RatState2542 :=
  ((((34150895378412517260951066159778865 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-2187353892094995365585572410350725) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((6331205461928702441632722340293 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05121MinusP010Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP010Output2559.1‖ ≤ (batchValueN05121MinusP010Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP010BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP010Output2559,
    batchN05121MinusP010Center2559, batchN05121MinusP010Error2559, embedPair2542]

theorem batchValueN05121MinusP010Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP010Output2559.1) + embedPair2542
            batchValueN05121MinusP010Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP010Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP010Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP010Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP010Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP010Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP010Output2559, pairMagnitude2542]

def batchValueN05121MinusP011Output2559 : RatState2542 :=
  ((((136587898056514574882487620153157195 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-2419847880377680094774067790409347) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((3175819955750226711556527560723 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05121MinusP011Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP011Output2559.1‖ ≤ (batchValueN05121MinusP011Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP011BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP011Output2559,
    batchN05121MinusP011Center2559, batchN05121MinusP011Error2559, embedPair2542]

theorem batchValueN05121MinusP011Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP011Output2559.1) + embedPair2542
            batchValueN05121MinusP011Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP011Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP011Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP011Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP011Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP011Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP011Output2559, pairMagnitude2542]

def batchValueN05121MinusP012Output2559 : RatState2542 :=
  ((((136569985156640262541922752597216529 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-5321250310645962360624902518743217) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12745648418151806341403167315331 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP012Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP012Output2559.1‖ ≤ (batchValueN05121MinusP012Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP012BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP012Output2559,
    batchN05121MinusP012Center2559, batchN05121MinusP012Error2559, embedPair2542]

theorem batchValueN05121MinusP012Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP012Output2559.1) + embedPair2542
            batchValueN05121MinusP012Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP012Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP012Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP012Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP012Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP012Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP012Output2559, pairMagnitude2542]

def batchValueN05121MinusP013Output2559 : RatState2542 :=
  ((((68276091431291567924075361002274879 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-360001660245455120202698469076737) : ℚ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))),
    ((12784292140381913196007361187239 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP013Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP013Output2559.1‖ ≤ (batchValueN05121MinusP013Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP013BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP013Output2559,
    batchN05121MinusP013Center2559, batchN05121MinusP013Error2559, embedPair2542]

theorem batchValueN05121MinusP013Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP013Output2559.1) + embedPair2542
            batchValueN05121MinusP013Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP013Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP013Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP013Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP013Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP013Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP013Output2559, pairMagnitude2542]

def batchValueN05121MinusP014Output2559 : RatState2542 :=
  ((((136515471229987342697102690921951069 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-6572873451390153567546039568480573) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((6427989802512944552770335821299 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05121MinusP014Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP014Output2559.1‖ ≤ (batchValueN05121MinusP014Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP014BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP014Output2559,
    batchN05121MinusP014Center2559, batchN05121MinusP014Error2559, embedPair2542]

theorem batchValueN05121MinusP014Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP014Output2559.1) + embedPair2542
            batchValueN05121MinusP014Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP014Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP014Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP014Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP014Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP014Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP014Output2559, pairMagnitude2542]

def batchValueN05121MinusP015Output2559 : RatState2542 :=
  ((((136486191720340377288908220414040657 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-3577569713925265664595653325637415) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((12907410932199791456265434005263 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP015Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP015Output2559.1‖ ≤ (batchValueN05121MinusP015Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP015BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP015Output2559,
    batchN05121MinusP015Center2559, batchN05121MinusP015Error2559, embedPair2542]

theorem batchValueN05121MinusP015Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP015Output2559.1) + embedPair2542
            batchValueN05121MinusP015Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP015Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP015Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP015Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP015Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP015Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP015Output2559, pairMagnitude2542]

def batchValueN05121MinusP016Output2559 : RatState2542 :=
  ((((136463486139812693564813795357287141 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-7575849861410947056049490458559909) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12944613758394931643391090394651 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP016Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP016Output2559.1‖ ≤ (batchValueN05121MinusP016Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP016BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP016Output2559,
    batchN05121MinusP016Center2559, batchN05121MinusP016Error2559, embedPair2542]

theorem batchValueN05121MinusP016Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP016Output2559.1) + embedPair2542
            batchValueN05121MinusP016Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP016Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP016Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP016Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP016Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP016Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP016Output2559, pairMagnitude2542]

def batchValueN05121MinusP017Output2559 : RatState2542 :=
  ((((136415676210486263560913340223322917 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-8392844249076916956255201391248973) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((6508480007995604327801519311485 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05121MinusP017Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP017Output2559.1‖ ≤ (batchValueN05121MinusP017Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP017BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP017Output2559,
    batchN05121MinusP017Center2559, batchN05121MinusP017Error2559, embedPair2542]

theorem batchValueN05121MinusP017Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP017Output2559.1) + embedPair2542
            batchValueN05121MinusP017Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP017Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP017Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP017Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP017Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP017Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP017Output2559, pairMagnitude2542]

def batchValueN05121MinusP018Output2559 : RatState2542 :=
  ((((34099081494107878000368747841990865 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-543853476808256359652714217934587) : ℚ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))),
    ((13044340625762406390314361543371 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP018Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP018Output2559.1‖ ≤ (batchValueN05121MinusP018Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP018BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP018Output2559,
    batchN05121MinusP018Center2559, batchN05121MinusP018Error2559, embedPair2542]

theorem batchValueN05121MinusP018Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP018Output2559.1) + embedPair2542
            batchValueN05121MinusP018Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP018Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP018Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP018Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP018Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP018Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP018Output2559, pairMagnitude2542]

def batchValueN05121MinusP019Output2559 : RatState2542 :=
  ((((136359581535321501782222006292740117 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-9259647621022018891323427229802941) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((3273465884848201459230052508107 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05121MinusP019Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP019Output2559.1‖ ≤ (batchValueN05121MinusP019Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP019BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP019Output2559,
    batchN05121MinusP019Center2559, batchN05121MinusP019Error2559, embedPair2542]

theorem batchValueN05121MinusP019Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP019Output2559.1) + embedPair2542
            batchValueN05121MinusP019Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP019Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP019Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP019Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP019Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP019Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP019Output2559, pairMagnitude2542]

def batchValueN05121MinusP020Output2559 : RatState2542 :=
  ((((68158517073077529248233548624970471 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-9866243061545119323397961177056163) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((13147771897933847848607074750115 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP020Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP020Output2559.1‖ ≤ (batchValueN05121MinusP020Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP020BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP020Output2559,
    batchN05121MinusP020Center2559, batchN05121MinusP020Error2559, embedPair2542]

theorem batchValueN05121MinusP020Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP020Output2559.1) + embedPair2542
            batchValueN05121MinusP020Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP020Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP020Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP020Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP020Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP020Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP020Output2559, pairMagnitude2542]

def batchValueN05121MinusP021Output2559 : RatState2542 :=
  ((((136279461011980091077114577015383379 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-5186160835282918549185339339057645) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((13192804946534098182217288829769 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP021Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP021Output2559.1‖ ≤ (batchValueN05121MinusP021Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP021BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP021Output2559,
    batchN05121MinusP021Center2559, batchN05121MinusP021Error2559, embedPair2542]

theorem batchValueN05121MinusP021Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP021Output2559.1) + embedPair2542
            batchValueN05121MinusP021Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP021Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP021Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP021Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP021Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP021Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP021Output2559, pairMagnitude2542]

def batchValueN05121MinusP022Output2559 : RatState2542 :=
  ((((136259502735619449854657829734465215 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-1328912059703391410473709773163737) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))),
    ((825991878142992683952069869231 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336)))

theorem batchValueN05121MinusP022Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP022Output2559.1‖ ≤ (batchValueN05121MinusP022Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP022BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP022Output2559,
    batchN05121MinusP022Center2559, batchN05121MinusP022Error2559, embedPair2542]

theorem batchValueN05121MinusP022Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP022Output2559.1) + embedPair2542
            batchValueN05121MinusP022Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP022Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP022Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP022Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP022Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP022Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP022Output2559, pairMagnitude2542]

def batchValueN05121MinusP023Output2559 : RatState2542 :=
  ((((136199204618707897869796079847515455 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-2844437683717431695371673419828497) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((13282429446161009485739197185313 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP023Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP023Output2559.1‖ ≤ (batchValueN05121MinusP023Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP023BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP023Output2559,
    batchN05121MinusP023Center2559, batchN05121MinusP023Error2559, embedPair2542]

theorem batchValueN05121MinusP023Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP023Output2559.1) + embedPair2542
            batchValueN05121MinusP023Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP023Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP023Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP023Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP023Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP023Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP023Output2559, pairMagnitude2542]

def batchValueN05121MinusP024Output2559 : RatState2542 :=
  ((((136170122513951164501213750743429735 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-11720677671919042195046766127526551) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((416032698224622400720861711269 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168)))

theorem batchValueN05121MinusP024Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP024Output2559.1‖ ≤ (batchValueN05121MinusP024Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP024BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP024Output2559,
    batchN05121MinusP024Center2559, batchN05121MinusP024Error2559, embedPair2542]

theorem batchValueN05121MinusP024Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP024Output2559.1) + embedPair2542
            batchValueN05121MinusP024Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP024Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP024Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP024Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP024Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP024Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP024Output2559, pairMagnitude2542]

def batchValueN05121MinusP025Output2559 : RatState2542 :=
  ((((34033109734973648369730144164083891 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-12150539857527383027170746031863723) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((13351459823462372787032717524695 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP025Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP025Output2559.1‖ ≤ (batchValueN05121MinusP025Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP025BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP025Output2559,
    batchN05121MinusP025Center2559, batchN05121MinusP025Error2559, embedPair2542]

theorem batchValueN05121MinusP025Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP025Output2559.1) + embedPair2542
            batchValueN05121MinusP025Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP025Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP025Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP025Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP025Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP025Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP025Output2559, pairMagnitude2542]

def batchValueN05121MinusP026Output2559 : RatState2542 :=
  ((((34023131462415362580258952376753619 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-12589716375388340211288744434023861) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((13390745980153853631447785687381 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP026Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP026Output2559.1‖ ≤ (batchValueN05121MinusP026Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP026BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP026Output2559,
    batchN05121MinusP026Center2559, batchN05121MinusP026Error2559, embedPair2542]

theorem batchValueN05121MinusP026Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP026Output2559.1) + embedPair2542
            batchValueN05121MinusP026Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP026Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP026Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP026Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP026Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP026Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP026Output2559, pairMagnitude2542]

def batchValueN05121MinusP027Output2559 : RatState2542 :=
  ((((136032432655015167825611034479563907 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-13223230184499338363548550895742117) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((6723744351291080908153136387505 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05121MinusP027Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP027Output2559.1‖ ≤ (batchValueN05121MinusP027Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP027BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP027Output2559,
    batchN05121MinusP027Center2559, batchN05121MinusP027Error2559, embedPair2542]

theorem batchValueN05121MinusP027Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP027Output2559.1) + embedPair2542
            batchValueN05121MinusP027Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP027Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP027Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP027Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP027Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP027Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP027Output2559, pairMagnitude2542]

def batchValueN05121MinusP028Output2559 : RatState2542 :=
  ((((136007825957138393757603533801864003 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-6736984283903354066406227581707729) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((13469970627528118889679392474365 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP028Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP028Output2559.1‖ ≤ (batchValueN05121MinusP028Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP028BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP028Output2559,
    batchN05121MinusP028Center2559, batchN05121MinusP028Error2559, embedPair2542]

theorem batchValueN05121MinusP028Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP028Output2559.1) + embedPair2542
            batchValueN05121MinusP028Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP028Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP028Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP028Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP028Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP028Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP028Output2559, pairMagnitude2542]

def batchValueN05121MinusP029Output2559 : RatState2542 :=
  ((((33992369112637758179745966761293041 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-13855613458686682217438545134044421) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((13504215982396323554612879049929 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05121MinusP029Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP029Output2559.1‖ ≤ (batchValueN05121MinusP029Output2559.2 : ℝ)
                := by
  have h := batchN05121MinusP029BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05121MinusPosition2559, batchN05121MinusPosition2559,
      batchValueN05121MinusP029Output2559,
    batchN05121MinusP029Center2559, batchN05121MinusP029Error2559, embedPair2542]

theorem batchValueN05121MinusP029Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05121MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05121MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP029Output2559.1) + embedPair2542
            batchValueN05121MinusP029Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05121MinusPosition2559 - embedPair2542
            batchValueN05121MinusP029Output2559.1‖ + ‖embedPair2542
            batchValueN05121MinusP029Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05121MinusP029Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05121MinusP029Output2559.1 : ℝ) :=
      add_le_add batchValueN05121MinusP029Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05121MinusP029Output2559, pairMagnitude2542]

noncomputable def batchValueN05121MinusValue2559 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchValueN05121MinusP000Output2559.1
  | 1 => embedPair2542 batchValueN05121MinusP001Output2559.1
  | 2 => embedPair2542 batchValueN05121MinusP002Output2559.1
  | 3 => embedPair2542 batchValueN05121MinusP003Output2559.1
  | 4 => embedPair2542 batchValueN05121MinusP004Output2559.1
  | 5 => embedPair2542 batchValueN05121MinusP005Output2559.1
  | 6 => embedPair2542 batchValueN05121MinusP006Output2559.1
  | 7 => embedPair2542 batchValueN05121MinusP007Output2559.1
  | 8 => embedPair2542 batchValueN05121MinusP008Output2559.1
  | 9 => embedPair2542 batchValueN05121MinusP009Output2559.1
  | 10 => embedPair2542 batchValueN05121MinusP010Output2559.1
  | 11 => embedPair2542 batchValueN05121MinusP011Output2559.1
  | 12 => embedPair2542 batchValueN05121MinusP012Output2559.1
  | 13 => embedPair2542 batchValueN05121MinusP013Output2559.1
  | 14 => embedPair2542 batchValueN05121MinusP014Output2559.1
  | 15 => embedPair2542 batchValueN05121MinusP015Output2559.1
  | 16 => embedPair2542 batchValueN05121MinusP016Output2559.1
  | 17 => embedPair2542 batchValueN05121MinusP017Output2559.1
  | 18 => embedPair2542 batchValueN05121MinusP018Output2559.1
  | 19 => embedPair2542 batchValueN05121MinusP019Output2559.1
  | 20 => embedPair2542 batchValueN05121MinusP020Output2559.1
  | 21 => embedPair2542 batchValueN05121MinusP021Output2559.1
  | 22 => embedPair2542 batchValueN05121MinusP022Output2559.1
  | 23 => embedPair2542 batchValueN05121MinusP023Output2559.1
  | 24 => embedPair2542 batchValueN05121MinusP024Output2559.1
  | 25 => embedPair2542 batchValueN05121MinusP025Output2559.1
  | 26 => embedPair2542 batchValueN05121MinusP026Output2559.1
  | 27 => embedPair2542 batchValueN05121MinusP027Output2559.1
  | 28 => embedPair2542 batchValueN05121MinusP028Output2559.1
  | 29 => embedPair2542 batchValueN05121MinusP029Output2559.1
  | _ => 0

noncomputable def batchValueN05121MinusError2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (batchValueN05121MinusP000Output2559.2 : ℝ)
  | 1 => (batchValueN05121MinusP001Output2559.2 : ℝ)
  | 2 => (batchValueN05121MinusP002Output2559.2 : ℝ)
  | 3 => (batchValueN05121MinusP003Output2559.2 : ℝ)
  | 4 => (batchValueN05121MinusP004Output2559.2 : ℝ)
  | 5 => (batchValueN05121MinusP005Output2559.2 : ℝ)
  | 6 => (batchValueN05121MinusP006Output2559.2 : ℝ)
  | 7 => (batchValueN05121MinusP007Output2559.2 : ℝ)
  | 8 => (batchValueN05121MinusP008Output2559.2 : ℝ)
  | 9 => (batchValueN05121MinusP009Output2559.2 : ℝ)
  | 10 => (batchValueN05121MinusP010Output2559.2 : ℝ)
  | 11 => (batchValueN05121MinusP011Output2559.2 : ℝ)
  | 12 => (batchValueN05121MinusP012Output2559.2 : ℝ)
  | 13 => (batchValueN05121MinusP013Output2559.2 : ℝ)
  | 14 => (batchValueN05121MinusP014Output2559.2 : ℝ)
  | 15 => (batchValueN05121MinusP015Output2559.2 : ℝ)
  | 16 => (batchValueN05121MinusP016Output2559.2 : ℝ)
  | 17 => (batchValueN05121MinusP017Output2559.2 : ℝ)
  | 18 => (batchValueN05121MinusP018Output2559.2 : ℝ)
  | 19 => (batchValueN05121MinusP019Output2559.2 : ℝ)
  | 20 => (batchValueN05121MinusP020Output2559.2 : ℝ)
  | 21 => (batchValueN05121MinusP021Output2559.2 : ℝ)
  | 22 => (batchValueN05121MinusP022Output2559.2 : ℝ)
  | 23 => (batchValueN05121MinusP023Output2559.2 : ℝ)
  | 24 => (batchValueN05121MinusP024Output2559.2 : ℝ)
  | 25 => (batchValueN05121MinusP025Output2559.2 : ℝ)
  | 26 => (batchValueN05121MinusP026Output2559.2 : ℝ)
  | 27 => (batchValueN05121MinusP027Output2559.2 : ℝ)
  | 28 => (batchValueN05121MinusP028Output2559.2 : ℝ)
  | 29 => (batchValueN05121MinusP029Output2559.2 : ℝ)
  | _ => 0

theorem batchValueN05121MinusExp_error2559 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05121MinusPosition2559 -
            batchValueN05121MinusValue2559 i‖
            ≤ batchValueN05121MinusError2559 i := by
  fin_cases i
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP000Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP001Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP002Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP003Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP004Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP005Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP006Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP007Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP008Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP009Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP010Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP011Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP012Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP013Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP014Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP015Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP016Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP017Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP018Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP019Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP020Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP021Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP022Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP023Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP024Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP025Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP026Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP027Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP028Error2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP029Error2559

theorem batchValueN05121MinusUnit_norm2559 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05121MinusPosition2559‖ ≤ 1 := by
  fin_cases i
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP000Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP001Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP002Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP003Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP004Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP005Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP006Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP007Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP008Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP009Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP010Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP011Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP012Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP013Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP014Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP015Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP016Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP017Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP018Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP019Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP020Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP021Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP022Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP023Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP024Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP025Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP026Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP027Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP028Norm2559
  · simpa only [batchValueN05121MinusValue2559, batchValueN05121MinusError2559] using
      batchValueN05121MinusP029Norm2559

noncomputable def batchValueN05121MinusSumValue2559 : ℂ := ⟨(((((687185882939500136795142902 *
    10^40
        + 8874555212866997100465360503419245225015) * 10^40
        + 670740474537917365595200141545054867149) * 10^40
        + 6701058451746379048920645692119471682965) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816)),
    (((-(((15685731823043263153347648 * 10^40
        + 9084882557510344509760067845234112041451) * 10^40
        + 2478062674866361234718615334083016153926) * 10^40
        + 9802149888230009304564487213152773857095)) : ℝ) /
        (((24973988402527937851052777 * 10^40
        + 8383453304459887851413197692068732556770) * 10^40
        + 297391055812496096244882450793576927861) * 10^40
        + 5448971252983163583805434306282450321408))⟩

noncomputable def batchValueN05121MinusUpper2559 : ℝ := ((34430903937 : ℝ) /
        2500000000)

theorem batchValueN05121MinusSum_eq2559 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05121MinusValue2559 i) =
      batchValueN05121MinusSumValue2559 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN05121MinusValue2559,
      batchValueN05121MinusSumValue2559, embedPair2542, batchValueN05121MinusP000Output2559,
      batchValueN05121MinusP001Output2559,
      batchValueN05121MinusP002Output2559,
      batchValueN05121MinusP003Output2559,
      batchValueN05121MinusP004Output2559,
      batchValueN05121MinusP005Output2559,
      batchValueN05121MinusP006Output2559,
      batchValueN05121MinusP007Output2559,
      batchValueN05121MinusP008Output2559,
      batchValueN05121MinusP009Output2559,
      batchValueN05121MinusP010Output2559,
      batchValueN05121MinusP011Output2559,
      batchValueN05121MinusP012Output2559,
      batchValueN05121MinusP013Output2559,
      batchValueN05121MinusP014Output2559,
      batchValueN05121MinusP015Output2559,
      batchValueN05121MinusP016Output2559,
      batchValueN05121MinusP017Output2559,
      batchValueN05121MinusP018Output2559,
      batchValueN05121MinusP019Output2559,
      batchValueN05121MinusP020Output2559,
      batchValueN05121MinusP021Output2559,
      batchValueN05121MinusP022Output2559,
      batchValueN05121MinusP023Output2559,
      batchValueN05121MinusP024Output2559,
      batchValueN05121MinusP025Output2559,
      batchValueN05121MinusP026Output2559,
      batchValueN05121MinusP027Output2559,
      batchValueN05121MinusP028Output2559,
      batchValueN05121MinusP029Output2559, Complex.mul_re, Complex.mul_im]

theorem batchValueN05121MinusSum_norm2559 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05121MinusValue2559 i‖ ≤
      ((137723615747 : ℝ) /
        10000000000) := by
  rw [batchValueN05121MinusSum_eq2559]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchValueN05121MinusSumValue2559]

theorem batchValueN05121MinusEvaluation_charge2559 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchValueN05121MinusError2559 i) ≤ (1 : ℝ)/10^12 :=
          by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN05121MinusError2559,
      batchValueN05121MinusP000Output2559,
      batchValueN05121MinusP001Output2559,
      batchValueN05121MinusP002Output2559,
      batchValueN05121MinusP003Output2559,
      batchValueN05121MinusP004Output2559,
      batchValueN05121MinusP005Output2559,
      batchValueN05121MinusP006Output2559,
      batchValueN05121MinusP007Output2559,
      batchValueN05121MinusP008Output2559,
      batchValueN05121MinusP009Output2559,
      batchValueN05121MinusP010Output2559,
      batchValueN05121MinusP011Output2559,
      batchValueN05121MinusP012Output2559,
      batchValueN05121MinusP013Output2559,
      batchValueN05121MinusP014Output2559,
      batchValueN05121MinusP015Output2559,
      batchValueN05121MinusP016Output2559,
      batchValueN05121MinusP017Output2559,
      batchValueN05121MinusP018Output2559,
      batchValueN05121MinusP019Output2559,
      batchValueN05121MinusP020Output2559,
      batchValueN05121MinusP021Output2559,
      batchValueN05121MinusP022Output2559,
      batchValueN05121MinusP023Output2559,
      batchValueN05121MinusP024Output2559,
      batchValueN05121MinusP025Output2559,
      batchValueN05121MinusP026Output2559,
      batchValueN05121MinusP027Output2559,
      batchValueN05121MinusP028Output2559,
      batchValueN05121MinusP029Output2559]

theorem batchValueN05121MinusSigned_le2559 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchValueN05121MinusPosition2559 ≤ batchValueN05121MinusUpper2559 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05121MinusPosition2559‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05121MinusValue2559 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchValueN05121MinusError2559 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (batchValueN05121MinusExp_error2559 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05121MinusPosition2559‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchValueN05121MinusUnit_norm2559 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05121MinusPosition2559‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchValueN05121MinusUpper2559
  linarith [batchValueN05121MinusSum_norm2559, batchValueN05121MinusEvaluation_charge2559]

theorem batchValueN05121MinusPhysical_le2559 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 batchValueN05121MinusPosition2559‖ ≤
      batchValueN05121MinusUpper2559 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchValueN05121MinusPosition2559
  simpa only [iteratedDeriv_zero] using h.trans batchValueN05121MinusSigned_le2559

theorem batchValueN05121MinusGrid2559 :
    -stripRadius2303 + (5121 : ℝ)*(2*stripRadius2303/10240) = batchValueN05121MinusPosition2559 :=
        by
  norm_num [stripRadius2303, batchValueN05121MinusPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchValueN05121MinusSigned_le2559
#print axioms ConnesWeilRH.Dev.batchValueN05121MinusPhysical_le2559
