import ConnesWeilRH.Dev.C1RouteAKernelN05440Plus2555
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def sharedN05440PlusPosition2556 : ℝ := ((65536001 : ℝ) /
        160000000)

def sharedN05440PlusP000Output2556 : RatState2542 :=
  (((((-35577273784430258977834287950324407) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((27585124465461220130700261259143915 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((21591442788678157781153728193489 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440PlusP000Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP000Output2556.1‖ ≤ (sharedN05440PlusP000Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP000BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP000Output2556,
    kernelN05440PlusP000Center2555, kernelN05440PlusP000Error2555, embedPair2542]

theorem sharedN05440PlusP000Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP000Output2556.1) + embedPair2542
            sharedN05440PlusP000Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP000Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP000Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP000Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP000Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP000Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP000Output2556, pairMagnitude2542]

def sharedN05440PlusP001Output2556 : RatState2542 :=
  (((((-100223478208003658749924307957107195) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((38854538679396106244911782740630351 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((30249903359130704771307903799783 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440PlusP001Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP001Output2556.1‖ ≤ (sharedN05440PlusP001Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP001BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP001Output2556,
    kernelN05440PlusP001Center2555, kernelN05440PlusP001Error2555, embedPair2542]

theorem sharedN05440PlusP001Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP001Output2556.1) + embedPair2542
            sharedN05440PlusP001Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP001Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP001Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP001Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP001Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP001Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP001Output2556, pairMagnitude2542]

def sharedN05440PlusP002Output2556 : RatState2542 :=
  (((((-119307171478278770070381966790107431) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-5781610746076080205622958637732385) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))),
    ((4488986679061519301646540499963 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336)))

theorem sharedN05440PlusP002Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP002Output2556.1‖ ≤ (sharedN05440PlusP002Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP002BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP002Output2556,
    kernelN05440PlusP002Center2555, kernelN05440PlusP002Error2555, embedPair2542]

theorem sharedN05440PlusP002Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP002Output2556.1) + embedPair2542
            sharedN05440PlusP002Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP002Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP002Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP002Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP002Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP002Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP002Output2556, pairMagnitude2542]

def sharedN05440PlusP003Output2556 : RatState2542 :=
  (((((-131404958609320469409897501373826153) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-50942944090944117853320381328908141) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((78987452944080129834645088170227 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP003Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP003Output2556.1‖ ≤ (sharedN05440PlusP003Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP003BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP003Output2556,
    kernelN05440PlusP003Center2555, kernelN05440PlusP003Error2555, embedPair2542]

theorem sharedN05440PlusP003Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP003Output2556.1) + embedPair2542
            sharedN05440PlusP003Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP003Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP003Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP003Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP003Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP003Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP003Output2556, pairMagnitude2542]

def sharedN05440PlusP004Output2556 : RatState2542 :=
  (((((-139126631986152634762006987828015457) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((26968237385560950973259700478546621 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((83554366496452852487249796712517 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP004Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP004Output2556.1‖ ≤ (sharedN05440PlusP004Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP004BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP004Output2556,
    kernelN05440PlusP004Center2555, kernelN05440PlusP004Error2555, embedPair2542]

theorem sharedN05440PlusP004Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP004Output2556.1) + embedPair2542
            sharedN05440PlusP004Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP004Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP004Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP004Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP004Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP004Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP004Output2556, pairMagnitude2542]

def sharedN05440PlusP005Output2556 : RatState2542 :=
  ((((88024202463451811579290491849026191 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((8018314131182277279174115104813 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP005Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP005Output2556.1‖ ≤ (sharedN05440PlusP005Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP005BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP005Output2556,
    kernelN05440PlusP005Center2555, kernelN05440PlusP005Error2555, embedPair2542]

theorem sharedN05440PlusP005Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP005Output2556.1) + embedPair2542
            sharedN05440PlusP005Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP005Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP005Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP005Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP005Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP005Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP005Output2556, pairMagnitude2542]

def sharedN05440PlusP006Output2556 : RatState2542 :=
  ((((122135920257932299145836494112328433 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((5506166502893540963943760553037 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440PlusP006Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP006Output2556.1‖ ≤ (sharedN05440PlusP006Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP006BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP006Output2556,
    kernelN05440PlusP006Center2555, kernelN05440PlusP006Error2555, embedPair2542]

theorem sharedN05440PlusP006Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP006Output2556.1) + embedPair2542
            sharedN05440PlusP006Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP006Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP006Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP006Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP006Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP006Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP006Output2556, pairMagnitude2542]

def sharedN05440PlusP007Output2556 : RatState2542 :=
  ((((17616774099814945450948742471691895 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1)),
    ((6325274803267772159288019999043 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440PlusP007Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP007Output2556.1‖ ≤ (sharedN05440PlusP007Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP007BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP007Output2556,
    kernelN05440PlusP007Center2555, kernelN05440PlusP007Error2555, embedPair2542]

theorem sharedN05440PlusP007Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP007Output2556.1) + embedPair2542
            sharedN05440PlusP007Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP007Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP007Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP007Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP007Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP007Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP007Output2556, pairMagnitude2542]

def sharedN05440PlusP008Output2556 : RatState2542 :=
  ((((21665942857700134959056820455623597 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((46627153923570018025502619493804977 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((34647994978639851494364527374771 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP008Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP008Output2556.1‖ ≤ (sharedN05440PlusP008Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP008BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP008Output2556,
    kernelN05440PlusP008Center2555, kernelN05440PlusP008Error2555, embedPair2542]

theorem sharedN05440PlusP008Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP008Output2556.1) + embedPair2542
            sharedN05440PlusP008Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP008Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP008Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP008Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP008Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP008Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP008Output2556, pairMagnitude2542]

def sharedN05440PlusP009Output2556 : RatState2542 :=
  (((((-67557731439713117752235351162245179) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-71558742892409230249858881030119155) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((26022182861955578856600207167389 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440PlusP009Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP009Output2556.1‖ ≤ (sharedN05440PlusP009Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP009BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP009Output2556,
    kernelN05440PlusP009Center2555, kernelN05440PlusP009Error2555, embedPair2542]

theorem sharedN05440PlusP009Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP009Output2556.1) + embedPair2542
            sharedN05440PlusP009Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP009Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP009Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP009Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP009Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP009Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP009Output2556, pairMagnitude2542]

def sharedN05440PlusP010Output2556 : RatState2542 :=
  (((((-16790441760161563520583303596773581) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((71930506807614620616858758908913531 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((25566174571979940809867359746299 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440PlusP010Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP010Output2556.1‖ ≤ (sharedN05440PlusP010Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP010BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP010Output2556,
    kernelN05440PlusP010Center2555, kernelN05440PlusP010Error2555, embedPair2542]

theorem sharedN05440PlusP010Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP010Output2556.1) + embedPair2542
            sharedN05440PlusP010Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP010Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP010Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP010Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP010Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP010Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP010Output2556, pairMagnitude2542]

def sharedN05440PlusP011Output2556 : RatState2542 :=
  ((((16325376647483959497674638767719317 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((92836571839407514579241851319393643 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((23375227307250611408630699795287 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440PlusP011Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP011Output2556.1‖ ≤ (sharedN05440PlusP011Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP011BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP011Output2556,
    kernelN05440PlusP011Center2555, kernelN05440PlusP011Error2555, embedPair2542]

theorem sharedN05440PlusP011Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP011Output2556.1) + embedPair2542
            sharedN05440PlusP011Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP011Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP011Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP011Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP011Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP011Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP011Output2556, pairMagnitude2542]

def sharedN05440PlusP012Output2556 : RatState2542 :=
  ((((48937829816622908525057437236621445 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((10249683555083350351811199877059451 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((26321436908181966234087787661845 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP012Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP012Output2556.1‖ ≤ (sharedN05440PlusP012Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP012BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP012Output2556,
    kernelN05440PlusP012Center2555, kernelN05440PlusP012Error2555, embedPair2542]

theorem sharedN05440PlusP012Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP012Output2556.1) + embedPair2542
            sharedN05440PlusP012Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP012Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP012Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP012Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP012Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP012Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP012Output2556, pairMagnitude2542]

def sharedN05440PlusP013Output2556 : RatState2542 :=
  ((((59318919194673357484601614755683289 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-78523668961645847741083832100795227) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((44035117497752003892283821979791 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP013Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP013Output2556.1‖ ≤ (sharedN05440PlusP013Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP013BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP013Output2556,
    kernelN05440PlusP013Center2555, kernelN05440PlusP013Error2555, embedPair2542]

theorem sharedN05440PlusP013Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP013Output2556.1) + embedPair2542
            sharedN05440PlusP013Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP013Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP013Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP013Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP013Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP013Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP013Output2556, pairMagnitude2542]

def sharedN05440PlusP014Output2556 : RatState2542 :=
  (((((-46819829752822826572681271189343895) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-15135347116015182818333811010901523) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((13081845426110353777454500267019 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem sharedN05440PlusP014Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP014Output2556.1‖ ≤ (sharedN05440PlusP014Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP014BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP014Output2556,
    kernelN05440PlusP014Center2555, kernelN05440PlusP014Error2555, embedPair2542]

theorem sharedN05440PlusP014Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP014Output2556.1) + embedPair2542
            sharedN05440PlusP014Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP014Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP014Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP014Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP014Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP014Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP014Output2556, pairMagnitude2542]

def sharedN05440PlusP015Output2556 : RatState2542 :=
  (((((-24383075408116702160511401368428587) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((42739218804836351522892539497718419 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((64832846880555079729111443469351 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP015Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP015Output2556.1‖ ≤ (sharedN05440PlusP015Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP015BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP015Output2556,
    kernelN05440PlusP015Center2555, kernelN05440PlusP015Error2555, embedPair2542]

theorem sharedN05440PlusP015Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP015Output2556.1) + embedPair2542
            sharedN05440PlusP015Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP015Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP015Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP015Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP015Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP015Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP015Output2556, pairMagnitude2542]

def sharedN05440PlusP016Output2556 : RatState2542 :=
  ((((44394236378681238027530272921925105 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((87828540566128651407614002215369269 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((60345128106114300904004092682185 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP016Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP016Output2556.1‖ ≤ (sharedN05440PlusP016Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP016BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP016Output2556,
    kernelN05440PlusP016Center2555, kernelN05440PlusP016Error2555, embedPair2542]

theorem sharedN05440PlusP016Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP016Output2556.1) + embedPair2542
            sharedN05440PlusP016Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP016Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP016Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP016Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP016Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP016Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP016Output2556, pairMagnitude2542]

def sharedN05440PlusP017Output2556 : RatState2542 :=
  ((((67614686086640697364470844343141827 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-35752464904630588533891561749453593) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((54296970082982745716018626205897 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP017Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP017Output2556.1‖ ≤ (sharedN05440PlusP017Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP017BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP017Output2556,
    kernelN05440PlusP017Center2555, kernelN05440PlusP017Error2555, embedPair2542]

theorem sharedN05440PlusP017Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP017Output2556.1) + embedPair2542
            sharedN05440PlusP017Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP017Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP017Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP017Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP017Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP017Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP017Output2556, pairMagnitude2542]

def sharedN05440PlusP018Output2556 : RatState2542 :=
  ((((3246001161989988868326186180486983 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-98357329356172996977223173565065057) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((62699685640841155952709644343163 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP018Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP018Output2556.1‖ ≤ (sharedN05440PlusP018Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP018BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP018Output2556,
    kernelN05440PlusP018Center2555, kernelN05440PlusP018Error2555, embedPair2542]

theorem sharedN05440PlusP018Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP018Output2556.1) + embedPair2542
            sharedN05440PlusP018Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP018Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP018Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP018Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP018Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP018Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP018Output2556, pairMagnitude2542]

def sharedN05440PlusP019Output2556 : RatState2542 :=
  (((((-11771737742924087739197068708303289) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    (((-28565310332264676024232304250655491) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((50425515150840369890207928907935 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP019Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP019Output2556.1‖ ≤ (sharedN05440PlusP019Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP019BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP019Output2556,
    kernelN05440PlusP019Center2555, kernelN05440PlusP019Error2555, embedPair2542]

theorem sharedN05440PlusP019Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP019Output2556.1) + embedPair2542
            sharedN05440PlusP019Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP019Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP019Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP019Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP019Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP019Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP019Output2556, pairMagnitude2542]

def sharedN05440PlusP020Output2556 : RatState2542 :=
  (((((-5257007060921934586855803392879355) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((88971843154747636455742641761082459 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((51597935465081270325624549189955 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP020Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP020Output2556.1‖ ≤ (sharedN05440PlusP020Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP020BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP020Output2556,
    kernelN05440PlusP020Center2555, kernelN05440PlusP020Error2555, embedPair2542]

theorem sharedN05440PlusP020Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP020Output2556.1) + embedPair2542
            sharedN05440PlusP020Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP020Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP020Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP020Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP020Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP020Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP020Output2556, pairMagnitude2542]

def sharedN05440PlusP021Output2556 : RatState2542 :=
  ((((33417899577440043973836393193487545 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((72233487476037462161264396294590133 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((1147021130947558090145725872227 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168)))

theorem sharedN05440PlusP021Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP021Output2556.1‖ ≤ (sharedN05440PlusP021Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP021BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP021Output2556,
    kernelN05440PlusP021Center2555, kernelN05440PlusP021Error2555, embedPair2542]

theorem sharedN05440PlusP021Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP021Output2556.1) + embedPair2542
            sharedN05440PlusP021Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP021Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP021Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP021Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP021Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP021Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP021Output2556, pairMagnitude2542]

def sharedN05440PlusP022Output2556 : RatState2542 :=
  ((((48061562200770627105801967763922557 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((21096106676544728579027448234754819 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((24766687814248759731754299914821 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP022Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP022Output2556.1‖ ≤ (sharedN05440PlusP022Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP022BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP022Output2556,
    kernelN05440PlusP022Center2555, kernelN05440PlusP022Error2555, embedPair2542]

theorem sharedN05440PlusP022Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP022Output2556.1) + embedPair2542
            sharedN05440PlusP022Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP022Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP022Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP022Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP022Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP022Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP022Output2556, pairMagnitude2542]

def sharedN05440PlusP023Output2556 : RatState2542 :=
  ((((3290158560286033619077326629244875 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-98355862144920001247922263980107153) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((48832694683640395176275568138131 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP023Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP023Output2556.1‖ ≤ (sharedN05440PlusP023Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP023BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP023Output2556,
    kernelN05440PlusP023Center2555, kernelN05440PlusP023Error2555, embedPair2542]

theorem sharedN05440PlusP023Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP023Output2556.1) + embedPair2542
            sharedN05440PlusP023Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP023Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP023Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP023Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP023Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP023Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP023Output2556, pairMagnitude2542]

def sharedN05440PlusP024Output2556 : RatState2542 :=
  (((((-34336673885407981779343733141501113) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-35244404050752854596609246941527945) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((53419918243498909775520187177795 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP024Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP024Output2556.1‖ ≤ (sharedN05440PlusP024Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP024BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP024Output2556,
    kernelN05440PlusP024Center2555, kernelN05440PlusP024Error2555, embedPair2542]

theorem sharedN05440PlusP024Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP024Output2556.1) + embedPair2542
            sharedN05440PlusP024Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP024Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP024Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP024Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP024Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP024Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP024Output2556, pairMagnitude2542]

def sharedN05440PlusP025Output2556 : RatState2542 :=
  (((((-96210293768428439580286909366580673) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((20694930166952256246227311233841497 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((50750691126993309972243247648933 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP025Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP025Output2556.1‖ ≤ (sharedN05440PlusP025Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP025BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP025Output2556,
    kernelN05440PlusP025Center2555, kernelN05440PlusP025Error2555, embedPair2542]

theorem sharedN05440PlusP025Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP025Output2556.1) + embedPair2542
            sharedN05440PlusP025Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP025Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP025Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP025Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP025Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP025Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP025Output2556, pairMagnitude2542]

def sharedN05440PlusP026Output2556 : RatState2542 :=
  (((((-15778019050678471489829295122729631) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((46607180833451082260657893516014729 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((66538619787509997641399451215149 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP026Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP026Output2556.1‖ ≤ (sharedN05440PlusP026Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP026BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP026Output2556,
    kernelN05440PlusP026Center2555, kernelN05440PlusP026Error2555, embedPair2542]

theorem sharedN05440PlusP026Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP026Output2556.1) + embedPair2542
            sharedN05440PlusP026Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP026Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP026Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP026Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP026Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP026Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP026Output2556, pairMagnitude2542]

def sharedN05440PlusP027Output2556 : RatState2542 :=
  ((((90360844242947602800699785302263939 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((38982285583635214058671140692525473 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((24700096793526974441231268753449 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440PlusP027Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP027Output2556.1‖ ≤ (sharedN05440PlusP027Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP027BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP027Output2556,
    kernelN05440PlusP027Center2555, kernelN05440PlusP027Error2555, embedPair2542]

theorem sharedN05440PlusP027Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP027Output2556.1) + embedPair2542
            sharedN05440PlusP027Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP027Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP027Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP027Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP027Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP027Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP027Output2556, pairMagnitude2542]

def sharedN05440PlusP028Output2556 : RatState2542 :=
  ((((96774777859105655036102150596352395 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-17870174368010085679125699083300799) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((43987170784013522687795268919859 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP028Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP028Output2556.1‖ ≤ (sharedN05440PlusP028Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP028BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP028Output2556,
    kernelN05440PlusP028Center2555, kernelN05440PlusP028Error2555, embedPair2542]

theorem sharedN05440PlusP028Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP028Output2556.1) + embedPair2542
            sharedN05440PlusP028Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP028Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP028Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP028Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP028Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP028Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP028Output2556, pairMagnitude2542]

def sharedN05440PlusP029Output2556 : RatState2542 :=
  ((((46326303141300305738226819377296101 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-43412482072794110740542386705311453) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((66045985204110563638613112875439 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440PlusP029Error2556 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP029Output2556.1‖ ≤ (sharedN05440PlusP029Output2556.2 : ℝ) := by
  have h := kernelN05440PlusP029BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440PlusPosition2556, kernelN05440PlusPosition2555,
      sharedN05440PlusP029Output2556,
    kernelN05440PlusP029Center2555, kernelN05440PlusP029Error2555, embedPair2542]

theorem sharedN05440PlusP029Norm2556 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN05440PlusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN05440PlusPosition2556‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP029Output2556.1) + embedPair2542
            sharedN05440PlusP029Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN05440PlusPosition2556 - embedPair2542
            sharedN05440PlusP029Output2556.1‖ + ‖embedPair2542
            sharedN05440PlusP029Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440PlusP029Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440PlusP029Output2556.1 : ℝ) :=
      add_le_add sharedN05440PlusP029Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440PlusP029Output2556, pairMagnitude2542]

noncomputable def sharedN05440PlusValue2556 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 sharedN05440PlusP000Output2556.1
  | 1 => embedPair2542 sharedN05440PlusP001Output2556.1
  | 2 => embedPair2542 sharedN05440PlusP002Output2556.1
  | 3 => embedPair2542 sharedN05440PlusP003Output2556.1
  | 4 => embedPair2542 sharedN05440PlusP004Output2556.1
  | 5 => embedPair2542 sharedN05440PlusP005Output2556.1
  | 6 => embedPair2542 sharedN05440PlusP006Output2556.1
  | 7 => embedPair2542 sharedN05440PlusP007Output2556.1
  | 8 => embedPair2542 sharedN05440PlusP008Output2556.1
  | 9 => embedPair2542 sharedN05440PlusP009Output2556.1
  | 10 => embedPair2542 sharedN05440PlusP010Output2556.1
  | 11 => embedPair2542 sharedN05440PlusP011Output2556.1
  | 12 => embedPair2542 sharedN05440PlusP012Output2556.1
  | 13 => embedPair2542 sharedN05440PlusP013Output2556.1
  | 14 => embedPair2542 sharedN05440PlusP014Output2556.1
  | 15 => embedPair2542 sharedN05440PlusP015Output2556.1
  | 16 => embedPair2542 sharedN05440PlusP016Output2556.1
  | 17 => embedPair2542 sharedN05440PlusP017Output2556.1
  | 18 => embedPair2542 sharedN05440PlusP018Output2556.1
  | 19 => embedPair2542 sharedN05440PlusP019Output2556.1
  | 20 => embedPair2542 sharedN05440PlusP020Output2556.1
  | 21 => embedPair2542 sharedN05440PlusP021Output2556.1
  | 22 => embedPair2542 sharedN05440PlusP022Output2556.1
  | 23 => embedPair2542 sharedN05440PlusP023Output2556.1
  | 24 => embedPair2542 sharedN05440PlusP024Output2556.1
  | 25 => embedPair2542 sharedN05440PlusP025Output2556.1
  | 26 => embedPair2542 sharedN05440PlusP026Output2556.1
  | 27 => embedPair2542 sharedN05440PlusP027Output2556.1
  | 28 => embedPair2542 sharedN05440PlusP028Output2556.1
  | 29 => embedPair2542 sharedN05440PlusP029Output2556.1
  | _ => 0

noncomputable def sharedN05440PlusError2556 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (sharedN05440PlusP000Output2556.2 : ℝ)
  | 1 => (sharedN05440PlusP001Output2556.2 : ℝ)
  | 2 => (sharedN05440PlusP002Output2556.2 : ℝ)
  | 3 => (sharedN05440PlusP003Output2556.2 : ℝ)
  | 4 => (sharedN05440PlusP004Output2556.2 : ℝ)
  | 5 => (sharedN05440PlusP005Output2556.2 : ℝ)
  | 6 => (sharedN05440PlusP006Output2556.2 : ℝ)
  | 7 => (sharedN05440PlusP007Output2556.2 : ℝ)
  | 8 => (sharedN05440PlusP008Output2556.2 : ℝ)
  | 9 => (sharedN05440PlusP009Output2556.2 : ℝ)
  | 10 => (sharedN05440PlusP010Output2556.2 : ℝ)
  | 11 => (sharedN05440PlusP011Output2556.2 : ℝ)
  | 12 => (sharedN05440PlusP012Output2556.2 : ℝ)
  | 13 => (sharedN05440PlusP013Output2556.2 : ℝ)
  | 14 => (sharedN05440PlusP014Output2556.2 : ℝ)
  | 15 => (sharedN05440PlusP015Output2556.2 : ℝ)
  | 16 => (sharedN05440PlusP016Output2556.2 : ℝ)
  | 17 => (sharedN05440PlusP017Output2556.2 : ℝ)
  | 18 => (sharedN05440PlusP018Output2556.2 : ℝ)
  | 19 => (sharedN05440PlusP019Output2556.2 : ℝ)
  | 20 => (sharedN05440PlusP020Output2556.2 : ℝ)
  | 21 => (sharedN05440PlusP021Output2556.2 : ℝ)
  | 22 => (sharedN05440PlusP022Output2556.2 : ℝ)
  | 23 => (sharedN05440PlusP023Output2556.2 : ℝ)
  | 24 => (sharedN05440PlusP024Output2556.2 : ℝ)
  | 25 => (sharedN05440PlusP025Output2556.2 : ℝ)
  | 26 => (sharedN05440PlusP026Output2556.2 : ℝ)
  | 27 => (sharedN05440PlusP027Output2556.2 : ℝ)
  | 28 => (sharedN05440PlusP028Output2556.2 : ℝ)
  | 29 => (sharedN05440PlusP029Output2556.2 : ℝ)
  | _ => 0

theorem sharedN05440PlusExp_error2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN05440PlusPosition2556 - sharedN05440PlusValue2556 i‖ ≤
            sharedN05440PlusError2556 i := by
  fin_cases i
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP000Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP001Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP002Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP003Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP004Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP005Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP006Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP007Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP008Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP009Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP010Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP011Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP012Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP013Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP014Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP015Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP016Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP017Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP018Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP019Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP020Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP021Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP022Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP023Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP024Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP025Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP026Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP027Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP028Error2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP029Error2556

theorem sharedN05440PlusUnit_norm2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN05440PlusPosition2556‖ ≤ 1 := by
  fin_cases i
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP000Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP001Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP002Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP003Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP004Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP005Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP006Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP007Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP008Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP009Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP010Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP011Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP012Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP013Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP014Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP015Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP016Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP017Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP018Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP019Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP020Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP021Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP022Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP023Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP024Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP025Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP026Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP027Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP028Norm2556
  · simpa only [sharedN05440PlusValue2556, sharedN05440PlusError2556] using
      sharedN05440PlusP029Norm2556

noncomputable def sharedN05440PlusSumValue2556 : ℂ := ⟨(((((5745999283427915719426018 * 10^40
        + 5672537964073494645500075450773538429030) * 10^40
        + 2881422477459322196753762220744492170645) * 10^40
        + 9368732422992873180478707980756557587825) : ℝ) /
        (((12486994201263968925526388 * 10^40
        + 9191726652229943925706598846034366278385) * 10^40
        + 148695527906248048122441225396788463930) * 10^40
        + 7724485626491581791902717153141225160704)),
    (((-(((17411077239449284950374378 * 10^40
        + 8953505167768654647726616892868082213242) * 10^40
        + 27445588484685932988171203541537014760) * 10^40
        + 4751026114585608845340282274066674669481)) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816))⟩

noncomputable def sharedN05440PlusUpper2556 : ℝ := ((721605217 : ℝ) /
        1250000000)

theorem sharedN05440PlusSum_eq2556 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN05440PlusValue2556 i) =
      sharedN05440PlusSumValue2556 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN05440PlusValue2556,
      sharedN05440PlusSumValue2556, embedPair2542, sharedN05440PlusP000Output2556,
      sharedN05440PlusP001Output2556,
      sharedN05440PlusP002Output2556,
      sharedN05440PlusP003Output2556,
      sharedN05440PlusP004Output2556,
      sharedN05440PlusP005Output2556,
      sharedN05440PlusP006Output2556,
      sharedN05440PlusP007Output2556,
      sharedN05440PlusP008Output2556,
      sharedN05440PlusP009Output2556,
      sharedN05440PlusP010Output2556,
      sharedN05440PlusP011Output2556,
      sharedN05440PlusP012Output2556,
      sharedN05440PlusP013Output2556,
      sharedN05440PlusP014Output2556,
      sharedN05440PlusP015Output2556,
      sharedN05440PlusP016Output2556,
      sharedN05440PlusP017Output2556,
      sharedN05440PlusP018Output2556,
      sharedN05440PlusP019Output2556,
      sharedN05440PlusP020Output2556,
      sharedN05440PlusP021Output2556,
      sharedN05440PlusP022Output2556,
      sharedN05440PlusP023Output2556,
      sharedN05440PlusP024Output2556,
      sharedN05440PlusP025Output2556,
      sharedN05440PlusP026Output2556,
      sharedN05440PlusP027Output2556,
      sharedN05440PlusP028Output2556,
      sharedN05440PlusP029Output2556, Complex.mul_re, Complex.mul_im]

theorem sharedN05440PlusSum_norm2556 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN05440PlusValue2556 i‖ ≤
      ((1154568347 : ℝ) /
        2000000000) := by
  rw [sharedN05440PlusSum_eq2556]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [sharedN05440PlusSumValue2556]

theorem sharedN05440PlusEvaluation_charge2556 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * sharedN05440PlusError2556 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN05440PlusError2556,
      sharedN05440PlusP000Output2556,
      sharedN05440PlusP001Output2556,
      sharedN05440PlusP002Output2556,
      sharedN05440PlusP003Output2556,
      sharedN05440PlusP004Output2556,
      sharedN05440PlusP005Output2556,
      sharedN05440PlusP006Output2556,
      sharedN05440PlusP007Output2556,
      sharedN05440PlusP008Output2556,
      sharedN05440PlusP009Output2556,
      sharedN05440PlusP010Output2556,
      sharedN05440PlusP011Output2556,
      sharedN05440PlusP012Output2556,
      sharedN05440PlusP013Output2556,
      sharedN05440PlusP014Output2556,
      sharedN05440PlusP015Output2556,
      sharedN05440PlusP016Output2556,
      sharedN05440PlusP017Output2556,
      sharedN05440PlusP018Output2556,
      sharedN05440PlusP019Output2556,
      sharedN05440PlusP020Output2556,
      sharedN05440PlusP021Output2556,
      sharedN05440PlusP022Output2556,
      sharedN05440PlusP023Output2556,
      sharedN05440PlusP024Output2556,
      sharedN05440PlusP025Output2556,
      sharedN05440PlusP026Output2556,
      sharedN05440PlusP027Output2556,
      sharedN05440PlusP028Output2556,
      sharedN05440PlusP029Output2556]

theorem sharedN05440PlusSigned_le2556 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 sharedN05440PlusPosition2556 ≤ sharedN05440PlusUpper2556 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN05440PlusPosition2556‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN05440PlusValue2556 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * sharedN05440PlusError2556 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (sharedN05440PlusExp_error2556 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN05440PlusPosition2556‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (sharedN05440PlusUnit_norm2556 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i sharedN05440PlusPosition2556‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 sharedN05440PlusUpper2556
  linarith [sharedN05440PlusSum_norm2556, sharedN05440PlusEvaluation_charge2556]

theorem sharedN05440PlusPhysical_le2556 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 sharedN05440PlusPosition2556‖ ≤
      sharedN05440PlusUpper2556 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        sharedN05440PlusPosition2556
  simpa only [iteratedDeriv_zero] using h.trans sharedN05440PlusSigned_le2556

theorem sharedN05440PlusGrid2556 :
    -stripRadius2303 + (5440 : ℝ)*(2*stripRadius2303/10240) = sharedN05440PlusPosition2556 := by
  norm_num [stripRadius2303, sharedN05440PlusPosition2556]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.sharedN05440PlusSigned_le2556
#print axioms ConnesWeilRH.Dev.sharedN05440PlusPhysical_le2556
