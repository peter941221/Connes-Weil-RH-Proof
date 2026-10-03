import ConnesWeilRH.Dev.C1RouteANeighborRight2557
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def neighborValueRightPosition2557 : ℝ := (((-79233025209) : ℝ) /
        25600000000)

def neighborValueRightP000Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem neighborValueRightP000Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP000Output2557.1‖ ≤ (neighborValueRightP000Output2557.2 : ℝ) := by
  have h := neighborRightP000BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP000Output2557,
    neighborRightP000Center2557, neighborRightP000Error2557, embedPair2542]

theorem neighborValueRightP000Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP000Output2557.1) + embedPair2542
            neighborValueRightP000Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP000Output2557.1‖ + ‖embedPair2542
            neighborValueRightP000Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP000Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP000Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP000Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP000Output2557, pairMagnitude2542]

def neighborValueRightP001Output2557 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP001Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP001Output2557.1‖ ≤ (neighborValueRightP001Output2557.2 : ℝ) := by
  have h := neighborRightP001BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP001Output2557,
    neighborRightP001Center2557, neighborRightP001Error2557, embedPair2542]

theorem neighborValueRightP001Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP001Output2557.1) + embedPair2542
            neighborValueRightP001Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP001Output2557.1‖ + ‖embedPair2542
            neighborValueRightP001Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP001Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP001Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP001Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP001Output2557, pairMagnitude2542]

def neighborValueRightP002Output2557 : RatState2542 :=
  (((((-327473819977610762985) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-137641572432642977529) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((2401498195160185481 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP002Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP002Output2557.1‖ ≤ (neighborValueRightP002Output2557.2 : ℝ) := by
  have h := neighborRightP002BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP002Output2557,
    neighborRightP002Center2557, neighborRightP002Error2557, embedPair2542]

theorem neighborValueRightP002Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP002Output2557.1) + embedPair2542
            neighborValueRightP002Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP002Output2557.1‖ + ‖embedPair2542
            neighborValueRightP002Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP002Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP002Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP002Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP002Output2557, pairMagnitude2542]

def neighborValueRightP003Output2557 : RatState2542 :=
  (((((-170211882877148968493082023) : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    (((-2289353691360944363304748813) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((37431587606157667393148409 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP003Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP003Output2557.1‖ ≤ (neighborValueRightP003Output2557.2 : ℝ) := by
  have h := neighborRightP003BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP003Output2557,
    neighborRightP003Center2557, neighborRightP003Error2557, embedPair2542]

theorem neighborValueRightP003Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP003Output2557.1) + embedPair2542
            neighborValueRightP003Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP003Output2557.1‖ + ‖embedPair2542
            neighborValueRightP003Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP003Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP003Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP003Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP003Output2557, pairMagnitude2542]

def neighborValueRightP004Output2557 : RatState2542 :=
  (((((-676666070280422645745488920633) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((2275293504233894188352239524669 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((9077586350185816146255924959 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem neighborValueRightP004Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP004Output2557.1‖ ≤ (neighborValueRightP004Output2557.2 : ℝ) := by
  have h := neighborRightP004BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP004Output2557,
    neighborRightP004Center2557, neighborRightP004Error2557, embedPair2542]

theorem neighborValueRightP004Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP004Output2557.1) + embedPair2542
            neighborValueRightP004Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP004Output2557.1‖ + ‖embedPair2542
            neighborValueRightP004Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP004Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP004Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP004Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP004Output2557, pairMagnitude2542]

def neighborValueRightP005Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem neighborValueRightP005Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP005Output2557.1‖ ≤ (neighborValueRightP005Output2557.2 : ℝ) := by
  have h := neighborRightP005BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP005Output2557,
    neighborRightP005Center2557, neighborRightP005Error2557, embedPair2542]

theorem neighborValueRightP005Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP005Output2557.1) + embedPair2542
            neighborValueRightP005Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP005Output2557.1‖ + ‖embedPair2542
            neighborValueRightP005Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP005Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP005Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP005Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP005Output2557, pairMagnitude2542]

def neighborValueRightP006Output2557 : RatState2542 :=
  ((((1061161581669737 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((308762315073 : ℚ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672)))

theorem neighborValueRightP006Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP006Output2557.1‖ ≤ (neighborValueRightP006Output2557.2 : ℝ) := by
  have h := neighborRightP006BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP006Output2557,
    neighborRightP006Center2557, neighborRightP006Error2557, embedPair2542]

theorem neighborValueRightP006Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP006Output2557.1) + embedPair2542
            neighborValueRightP006Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP006Output2557.1‖ + ‖embedPair2542
            neighborValueRightP006Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP006Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP006Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP006Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP006Output2557, pairMagnitude2542]

def neighborValueRightP007Output2557 : RatState2542 :=
  ((((5327421052927345222380711195 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((1547288813920703326910549 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP007Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP007Output2557.1‖ ≤ (neighborValueRightP007Output2557.2 : ℝ) := by
  have h := neighborRightP007BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP007Output2557,
    neighborRightP007Center2557, neighborRightP007Error2557, embedPair2542]

theorem neighborValueRightP007Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP007Output2557.1) + embedPair2542
            neighborValueRightP007Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP007Output2557.1‖ + ‖embedPair2542
            neighborValueRightP007Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP007Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP007Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP007Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP007Output2557, pairMagnitude2542]

def neighborValueRightP008Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP008Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP008Output2557.1‖ ≤ (neighborValueRightP008Output2557.2 : ℝ) := by
  have h := neighborRightP008BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP008Output2557,
    neighborRightP008Center2557, neighborRightP008Error2557, embedPair2542]

theorem neighborValueRightP008Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP008Output2557.1) + embedPair2542
            neighborValueRightP008Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP008Output2557.1‖ + ‖embedPair2542
            neighborValueRightP008Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP008Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP008Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP008Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP008Output2557, pairMagnitude2542]

def neighborValueRightP009Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP009Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP009Output2557.1‖ ≤ (neighborValueRightP009Output2557.2 : ℝ) := by
  have h := neighborRightP009BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP009Output2557,
    neighborRightP009Center2557, neighborRightP009Error2557, embedPair2542]

theorem neighborValueRightP009Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP009Output2557.1) + embedPair2542
            neighborValueRightP009Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP009Output2557.1‖ + ‖embedPair2542
            neighborValueRightP009Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP009Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP009Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP009Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP009Output2557, pairMagnitude2542]

def neighborValueRightP010Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP010Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP010Output2557.1‖ ≤ (neighborValueRightP010Output2557.2 : ℝ) := by
  have h := neighborRightP010BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP010Output2557,
    neighborRightP010Center2557, neighborRightP010Error2557, embedPair2542]

theorem neighborValueRightP010Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP010Output2557.1) + embedPair2542
            neighborValueRightP010Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP010Output2557.1‖ + ‖embedPair2542
            neighborValueRightP010Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP010Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP010Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP010Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP010Output2557, pairMagnitude2542]

def neighborValueRightP011Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP011Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP011Output2557.1‖ ≤ (neighborValueRightP011Output2557.2 : ℝ) := by
  have h := neighborRightP011BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP011Output2557,
    neighborRightP011Center2557, neighborRightP011Error2557, embedPair2542]

theorem neighborValueRightP011Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP011Output2557.1) + embedPair2542
            neighborValueRightP011Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP011Output2557.1‖ + ‖embedPair2542
            neighborValueRightP011Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP011Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP011Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP011Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP011Output2557, pairMagnitude2542]

def neighborValueRightP012Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP012Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP012Output2557.1‖ ≤ (neighborValueRightP012Output2557.2 : ℝ) := by
  have h := neighborRightP012BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP012Output2557,
    neighborRightP012Center2557, neighborRightP012Error2557, embedPair2542]

theorem neighborValueRightP012Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP012Output2557.1) + embedPair2542
            neighborValueRightP012Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP012Output2557.1‖ + ‖embedPair2542
            neighborValueRightP012Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP012Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP012Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP012Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP012Output2557, pairMagnitude2542]

def neighborValueRightP013Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP013Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP013Output2557.1‖ ≤ (neighborValueRightP013Output2557.2 : ℝ) := by
  have h := neighborRightP013BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP013Output2557,
    neighborRightP013Center2557, neighborRightP013Error2557, embedPair2542]

theorem neighborValueRightP013Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP013Output2557.1) + embedPair2542
            neighborValueRightP013Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP013Output2557.1‖ + ‖embedPair2542
            neighborValueRightP013Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP013Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP013Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP013Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP013Output2557, pairMagnitude2542]

def neighborValueRightP014Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP014Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP014Output2557.1‖ ≤ (neighborValueRightP014Output2557.2 : ℝ) := by
  have h := neighborRightP014BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP014Output2557,
    neighborRightP014Center2557, neighborRightP014Error2557, embedPair2542]

theorem neighborValueRightP014Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP014Output2557.1) + embedPair2542
            neighborValueRightP014Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP014Output2557.1‖ + ‖embedPair2542
            neighborValueRightP014Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP014Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP014Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP014Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP014Output2557, pairMagnitude2542]

def neighborValueRightP015Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP015Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP015Output2557.1‖ ≤ (neighborValueRightP015Output2557.2 : ℝ) := by
  have h := neighborRightP015BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP015Output2557,
    neighborRightP015Center2557, neighborRightP015Error2557, embedPair2542]

theorem neighborValueRightP015Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP015Output2557.1) + embedPair2542
            neighborValueRightP015Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP015Output2557.1‖ + ‖embedPair2542
            neighborValueRightP015Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP015Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP015Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP015Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP015Output2557, pairMagnitude2542]

def neighborValueRightP016Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP016Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP016Output2557.1‖ ≤ (neighborValueRightP016Output2557.2 : ℝ) := by
  have h := neighborRightP016BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP016Output2557,
    neighborRightP016Center2557, neighborRightP016Error2557, embedPair2542]

theorem neighborValueRightP016Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP016Output2557.1) + embedPair2542
            neighborValueRightP016Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP016Output2557.1‖ + ‖embedPair2542
            neighborValueRightP016Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP016Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP016Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP016Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP016Output2557, pairMagnitude2542]

def neighborValueRightP017Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP017Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP017Output2557.1‖ ≤ (neighborValueRightP017Output2557.2 : ℝ) := by
  have h := neighborRightP017BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP017Output2557,
    neighborRightP017Center2557, neighborRightP017Error2557, embedPair2542]

theorem neighborValueRightP017Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP017Output2557.1) + embedPair2542
            neighborValueRightP017Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP017Output2557.1‖ + ‖embedPair2542
            neighborValueRightP017Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP017Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP017Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP017Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP017Output2557, pairMagnitude2542]

def neighborValueRightP018Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP018Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP018Output2557.1‖ ≤ (neighborValueRightP018Output2557.2 : ℝ) := by
  have h := neighborRightP018BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP018Output2557,
    neighborRightP018Center2557, neighborRightP018Error2557, embedPair2542]

theorem neighborValueRightP018Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP018Output2557.1) + embedPair2542
            neighborValueRightP018Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP018Output2557.1‖ + ‖embedPair2542
            neighborValueRightP018Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP018Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP018Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP018Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP018Output2557, pairMagnitude2542]

def neighborValueRightP019Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP019Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP019Output2557.1‖ ≤ (neighborValueRightP019Output2557.2 : ℝ) := by
  have h := neighborRightP019BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP019Output2557,
    neighborRightP019Center2557, neighborRightP019Error2557, embedPair2542]

theorem neighborValueRightP019Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP019Output2557.1) + embedPair2542
            neighborValueRightP019Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP019Output2557.1‖ + ‖embedPair2542
            neighborValueRightP019Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP019Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP019Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP019Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP019Output2557, pairMagnitude2542]

def neighborValueRightP020Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP020Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP020Output2557.1‖ ≤ (neighborValueRightP020Output2557.2 : ℝ) := by
  have h := neighborRightP020BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP020Output2557,
    neighborRightP020Center2557, neighborRightP020Error2557, embedPair2542]

theorem neighborValueRightP020Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP020Output2557.1) + embedPair2542
            neighborValueRightP020Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP020Output2557.1‖ + ‖embedPair2542
            neighborValueRightP020Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP020Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP020Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP020Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP020Output2557, pairMagnitude2542]

def neighborValueRightP021Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP021Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP021Output2557.1‖ ≤ (neighborValueRightP021Output2557.2 : ℝ) := by
  have h := neighborRightP021BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP021Output2557,
    neighborRightP021Center2557, neighborRightP021Error2557, embedPair2542]

theorem neighborValueRightP021Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP021Output2557.1) + embedPair2542
            neighborValueRightP021Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP021Output2557.1‖ + ‖embedPair2542
            neighborValueRightP021Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP021Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP021Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP021Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP021Output2557, pairMagnitude2542]

def neighborValueRightP022Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP022Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP022Output2557.1‖ ≤ (neighborValueRightP022Output2557.2 : ℝ) := by
  have h := neighborRightP022BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP022Output2557,
    neighborRightP022Center2557, neighborRightP022Error2557, embedPair2542]

theorem neighborValueRightP022Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP022Output2557.1) + embedPair2542
            neighborValueRightP022Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP022Output2557.1‖ + ‖embedPair2542
            neighborValueRightP022Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP022Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP022Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP022Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP022Output2557, pairMagnitude2542]

def neighborValueRightP023Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP023Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP023Output2557.1‖ ≤ (neighborValueRightP023Output2557.2 : ℝ) := by
  have h := neighborRightP023BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP023Output2557,
    neighborRightP023Center2557, neighborRightP023Error2557, embedPair2542]

theorem neighborValueRightP023Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP023Output2557.1) + embedPair2542
            neighborValueRightP023Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP023Output2557.1‖ + ‖embedPair2542
            neighborValueRightP023Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP023Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP023Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP023Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP023Output2557, pairMagnitude2542]

def neighborValueRightP024Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP024Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP024Output2557.1‖ ≤ (neighborValueRightP024Output2557.2 : ℝ) := by
  have h := neighborRightP024BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP024Output2557,
    neighborRightP024Center2557, neighborRightP024Error2557, embedPair2542]

theorem neighborValueRightP024Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP024Output2557.1) + embedPair2542
            neighborValueRightP024Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP024Output2557.1‖ + ‖embedPair2542
            neighborValueRightP024Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP024Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP024Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP024Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP024Output2557, pairMagnitude2542]

def neighborValueRightP025Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP025Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP025Output2557.1‖ ≤ (neighborValueRightP025Output2557.2 : ℝ) := by
  have h := neighborRightP025BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP025Output2557,
    neighborRightP025Center2557, neighborRightP025Error2557, embedPair2542]

theorem neighborValueRightP025Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP025Output2557.1) + embedPair2542
            neighborValueRightP025Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP025Output2557.1‖ + ‖embedPair2542
            neighborValueRightP025Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP025Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP025Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP025Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP025Output2557, pairMagnitude2542]

def neighborValueRightP026Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP026Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP026Output2557.1‖ ≤ (neighborValueRightP026Output2557.2 : ℝ) := by
  have h := neighborRightP026BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP026Output2557,
    neighborRightP026Center2557, neighborRightP026Error2557, embedPair2542]

theorem neighborValueRightP026Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP026Output2557.1) + embedPair2542
            neighborValueRightP026Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP026Output2557.1‖ + ‖embedPair2542
            neighborValueRightP026Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP026Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP026Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP026Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP026Output2557, pairMagnitude2542]

def neighborValueRightP027Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP027Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP027Output2557.1‖ ≤ (neighborValueRightP027Output2557.2 : ℝ) := by
  have h := neighborRightP027BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP027Output2557,
    neighborRightP027Center2557, neighborRightP027Error2557, embedPair2542]

theorem neighborValueRightP027Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP027Output2557.1) + embedPair2542
            neighborValueRightP027Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP027Output2557.1‖ + ‖embedPair2542
            neighborValueRightP027Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP027Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP027Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP027Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP027Output2557, pairMagnitude2542]

def neighborValueRightP028Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP028Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP028Output2557.1‖ ≤ (neighborValueRightP028Output2557.2 : ℝ) := by
  have h := neighborRightP028BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP028Output2557,
    neighborRightP028Center2557, neighborRightP028Error2557, embedPair2542]

theorem neighborValueRightP028Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP028Output2557.1) + embedPair2542
            neighborValueRightP028Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP028Output2557.1‖ + ‖embedPair2542
            neighborValueRightP028Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP028Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP028Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP028Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP028Output2557, pairMagnitude2542]

def neighborValueRightP029Output2557 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem neighborValueRightP029Error2557 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP029Output2557.1‖ ≤ (neighborValueRightP029Output2557.2 : ℝ) := by
  have h := neighborRightP029BaseError2557
  convert h using 1
  all_goals norm_num [neighborValueRightPosition2557, neighborRightPosition2557,
      neighborValueRightP029Output2557,
    neighborRightP029Center2557, neighborRightP029Error2557, embedPair2542]

theorem neighborValueRightP029Norm2557 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ neighborValueRightPosition2557‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ neighborValueRightPosition2557‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP029Output2557.1) + embedPair2542
            neighborValueRightP029Output2557.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ neighborValueRightPosition2557 - embedPair2542
            neighborValueRightP029Output2557.1‖ + ‖embedPair2542
            neighborValueRightP029Output2557.1‖ := norm_add_le _ _
    _ ≤ (neighborValueRightP029Output2557.2 : ℝ) + (pairMagnitude2542
        neighborValueRightP029Output2557.1 : ℝ) :=
      add_le_add neighborValueRightP029Error2557 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [neighborValueRightP029Output2557, pairMagnitude2542]

noncomputable def neighborValueRightValue2557 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 neighborValueRightP000Output2557.1
  | 1 => embedPair2542 neighborValueRightP001Output2557.1
  | 2 => embedPair2542 neighborValueRightP002Output2557.1
  | 3 => embedPair2542 neighborValueRightP003Output2557.1
  | 4 => embedPair2542 neighborValueRightP004Output2557.1
  | 5 => embedPair2542 neighborValueRightP005Output2557.1
  | 6 => embedPair2542 neighborValueRightP006Output2557.1
  | 7 => embedPair2542 neighborValueRightP007Output2557.1
  | 8 => embedPair2542 neighborValueRightP008Output2557.1
  | 9 => embedPair2542 neighborValueRightP009Output2557.1
  | 10 => embedPair2542 neighborValueRightP010Output2557.1
  | 11 => embedPair2542 neighborValueRightP011Output2557.1
  | 12 => embedPair2542 neighborValueRightP012Output2557.1
  | 13 => embedPair2542 neighborValueRightP013Output2557.1
  | 14 => embedPair2542 neighborValueRightP014Output2557.1
  | 15 => embedPair2542 neighborValueRightP015Output2557.1
  | 16 => embedPair2542 neighborValueRightP016Output2557.1
  | 17 => embedPair2542 neighborValueRightP017Output2557.1
  | 18 => embedPair2542 neighborValueRightP018Output2557.1
  | 19 => embedPair2542 neighborValueRightP019Output2557.1
  | 20 => embedPair2542 neighborValueRightP020Output2557.1
  | 21 => embedPair2542 neighborValueRightP021Output2557.1
  | 22 => embedPair2542 neighborValueRightP022Output2557.1
  | 23 => embedPair2542 neighborValueRightP023Output2557.1
  | 24 => embedPair2542 neighborValueRightP024Output2557.1
  | 25 => embedPair2542 neighborValueRightP025Output2557.1
  | 26 => embedPair2542 neighborValueRightP026Output2557.1
  | 27 => embedPair2542 neighborValueRightP027Output2557.1
  | 28 => embedPair2542 neighborValueRightP028Output2557.1
  | 29 => embedPair2542 neighborValueRightP029Output2557.1
  | _ => 0

noncomputable def neighborValueRightError2557 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (neighborValueRightP000Output2557.2 : ℝ)
  | 1 => (neighborValueRightP001Output2557.2 : ℝ)
  | 2 => (neighborValueRightP002Output2557.2 : ℝ)
  | 3 => (neighborValueRightP003Output2557.2 : ℝ)
  | 4 => (neighborValueRightP004Output2557.2 : ℝ)
  | 5 => (neighborValueRightP005Output2557.2 : ℝ)
  | 6 => (neighborValueRightP006Output2557.2 : ℝ)
  | 7 => (neighborValueRightP007Output2557.2 : ℝ)
  | 8 => (neighborValueRightP008Output2557.2 : ℝ)
  | 9 => (neighborValueRightP009Output2557.2 : ℝ)
  | 10 => (neighborValueRightP010Output2557.2 : ℝ)
  | 11 => (neighborValueRightP011Output2557.2 : ℝ)
  | 12 => (neighborValueRightP012Output2557.2 : ℝ)
  | 13 => (neighborValueRightP013Output2557.2 : ℝ)
  | 14 => (neighborValueRightP014Output2557.2 : ℝ)
  | 15 => (neighborValueRightP015Output2557.2 : ℝ)
  | 16 => (neighborValueRightP016Output2557.2 : ℝ)
  | 17 => (neighborValueRightP017Output2557.2 : ℝ)
  | 18 => (neighborValueRightP018Output2557.2 : ℝ)
  | 19 => (neighborValueRightP019Output2557.2 : ℝ)
  | 20 => (neighborValueRightP020Output2557.2 : ℝ)
  | 21 => (neighborValueRightP021Output2557.2 : ℝ)
  | 22 => (neighborValueRightP022Output2557.2 : ℝ)
  | 23 => (neighborValueRightP023Output2557.2 : ℝ)
  | 24 => (neighborValueRightP024Output2557.2 : ℝ)
  | 25 => (neighborValueRightP025Output2557.2 : ℝ)
  | 26 => (neighborValueRightP026Output2557.2 : ℝ)
  | 27 => (neighborValueRightP027Output2557.2 : ℝ)
  | 28 => (neighborValueRightP028Output2557.2 : ℝ)
  | 29 => (neighborValueRightP029Output2557.2 : ℝ)
  | _ => 0

theorem neighborValueRightExp_error2557 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i neighborValueRightPosition2557 - neighborValueRightValue2557 i‖ ≤
            neighborValueRightError2557 i := by
  fin_cases i
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP000Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP001Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP002Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP003Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP004Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP005Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP006Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP007Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP008Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP009Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP010Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP011Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP012Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP013Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP014Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP015Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP016Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP017Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP018Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP019Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP020Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP021Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP022Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP023Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP024Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP025Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP026Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP027Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP028Error2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP029Error2557

theorem neighborValueRightUnit_norm2557 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i neighborValueRightPosition2557‖ ≤ 1 := by
  fin_cases i
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP000Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP001Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP002Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP003Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP004Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP005Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP006Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP007Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP008Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP009Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP010Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP011Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP012Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP013Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP014Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP015Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP016Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP017Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP018Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP019Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP020Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP021Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP022Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP023Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP024Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP025Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP026Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP027Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP028Norm2557
  · simpa only [neighborValueRightValue2557, neighborValueRightError2557] using
      neighborValueRightP029Norm2557

noncomputable def neighborValueRightSumValue2557 : ℂ := ⟨(((((963524700313238341 * 10^40
        + 376251433849029869525587875780083208272) * 10^40
        + 8833411403432844202019134549577359018710) * 10^40
        + 3292304219148475803406185657403198250399) : ℝ) /
        (((12486994201263968925526388 * 10^40
        + 9191726652229943925706598846034366278385) * 10^40
        + 148695527906248048122441225396788463930) * 10^40
        + 7724485626491581791902717153141225160704)),
    (((((1749953519566059378 * 10^40
        + 1813627893069254570213119571169005234580) * 10^40
        + 8073558905589864818744852842544976099692) * 10^40
        + 4741990810320683195592629000720479211133) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816))⟩

noncomputable def neighborValueRightUpper2557 : ℝ := ((849 : ℝ) /
        10000000000)

theorem neighborValueRightSum_eq2557 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * neighborValueRightValue2557 i) =
      neighborValueRightSumValue2557 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, neighborValueRightValue2557,
      neighborValueRightSumValue2557, embedPair2542, neighborValueRightP000Output2557,
      neighborValueRightP001Output2557,
      neighborValueRightP002Output2557,
      neighborValueRightP003Output2557,
      neighborValueRightP004Output2557,
      neighborValueRightP005Output2557,
      neighborValueRightP006Output2557,
      neighborValueRightP007Output2557,
      neighborValueRightP008Output2557,
      neighborValueRightP009Output2557,
      neighborValueRightP010Output2557,
      neighborValueRightP011Output2557,
      neighborValueRightP012Output2557,
      neighborValueRightP013Output2557,
      neighborValueRightP014Output2557,
      neighborValueRightP015Output2557,
      neighborValueRightP016Output2557,
      neighborValueRightP017Output2557,
      neighborValueRightP018Output2557,
      neighborValueRightP019Output2557,
      neighborValueRightP020Output2557,
      neighborValueRightP021Output2557,
      neighborValueRightP022Output2557,
      neighborValueRightP023Output2557,
      neighborValueRightP024Output2557,
      neighborValueRightP025Output2557,
      neighborValueRightP026Output2557,
      neighborValueRightP027Output2557,
      neighborValueRightP028Output2557,
      neighborValueRightP029Output2557, Complex.mul_re, Complex.mul_im]

theorem neighborValueRightSum_norm2557 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * neighborValueRightValue2557 i‖ ≤
      ((53 : ℝ) /
        625000000) := by
  rw [neighborValueRightSum_eq2557]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [neighborValueRightSumValue2557]

theorem neighborValueRightEvaluation_charge2557 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * neighborValueRightError2557 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, neighborValueRightError2557,
      neighborValueRightP000Output2557,
      neighborValueRightP001Output2557,
      neighborValueRightP002Output2557,
      neighborValueRightP003Output2557,
      neighborValueRightP004Output2557,
      neighborValueRightP005Output2557,
      neighborValueRightP006Output2557,
      neighborValueRightP007Output2557,
      neighborValueRightP008Output2557,
      neighborValueRightP009Output2557,
      neighborValueRightP010Output2557,
      neighborValueRightP011Output2557,
      neighborValueRightP012Output2557,
      neighborValueRightP013Output2557,
      neighborValueRightP014Output2557,
      neighborValueRightP015Output2557,
      neighborValueRightP016Output2557,
      neighborValueRightP017Output2557,
      neighborValueRightP018Output2557,
      neighborValueRightP019Output2557,
      neighborValueRightP020Output2557,
      neighborValueRightP021Output2557,
      neighborValueRightP022Output2557,
      neighborValueRightP023Output2557,
      neighborValueRightP024Output2557,
      neighborValueRightP025Output2557,
      neighborValueRightP026Output2557,
      neighborValueRightP027Output2557,
      neighborValueRightP028Output2557,
      neighborValueRightP029Output2557]

theorem neighborValueRightSigned_le2557 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 neighborValueRightPosition2557 ≤ neighborValueRightUpper2557 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i neighborValueRightPosition2557‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * neighborValueRightValue2557 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * neighborValueRightError2557 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (neighborValueRightExp_error2557 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i neighborValueRightPosition2557‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (neighborValueRightUnit_norm2557 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i neighborValueRightPosition2557‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 neighborValueRightUpper2557
  linarith [neighborValueRightSum_norm2557, neighborValueRightEvaluation_charge2557]

theorem neighborValueRightPhysical_le2557 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 neighborValueRightPosition2557‖ ≤
      neighborValueRightUpper2557 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        neighborValueRightPosition2557
  simpa only [iteratedDeriv_zero] using h.trans neighborValueRightSigned_le2557

theorem neighborValueRightGrid2557 :
    -stripRadius2303 + (2702 : ℝ)*(2*stripRadius2303/10240) = neighborValueRightPosition2557 := by
  norm_num [stripRadius2303, neighborValueRightPosition2557]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.neighborValueRightSigned_le2557
#print axioms ConnesWeilRH.Dev.neighborValueRightPhysical_le2557
