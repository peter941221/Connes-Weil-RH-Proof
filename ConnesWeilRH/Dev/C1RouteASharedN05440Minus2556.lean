import ConnesWeilRH.Dev.C1RouteAKernelN05440Minus2555
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def sharedN05440MinusPosition2556 : ℝ := ((65536001 : ℝ) /
        160000000)

def sharedN05440MinusP000Output2556 : RatState2542 :=
  (((((-47240625468716384282800085644730723) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((18314198851726989519620350327925883 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((28853873385704556118854613093727 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440MinusP000Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP000Output2556.1‖ ≤ (sharedN05440MinusP000Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP000BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP000Output2556,
    kernelN05440MinusP000Center2555, kernelN05440MinusP000Error2555, embedPair2542]

theorem sharedN05440MinusP000Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP000Output2556.1) + embedPair2542
            sharedN05440MinusP000Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP000Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP000Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP000Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP000Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP000Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP000Output2556, pairMagnitude2542]

def sharedN05440MinusP001Output2556 : RatState2542 :=
  (((((-8317493327841034999117566362833513) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((12898070272576534656216409493599237 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((20212333422939156095014085369811 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440MinusP001Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP001Output2556.1‖ ≤ (sharedN05440MinusP001Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP001BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP001Output2556,
    kernelN05440MinusP001Center2555, kernelN05440MinusP001Error2555, embedPair2542]

theorem sharedN05440MinusP001Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP001Output2556.1) + embedPair2542
            sharedN05440MinusP001Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP001Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP001Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP001Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP001Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP001Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP001Output2556, pairMagnitude2542]

def sharedN05440MinusP002Output2556 : RatState2542 :=
  (((((-19802477832083935096949159204845913) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-30708019902392295161306432703451507) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((47991106304641732704040200024805 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440MinusP002Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP002Output2556.1‖ ≤ (sharedN05440MinusP002Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP002BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP002Output2556,
    kernelN05440MinusP002Center2555, kernelN05440MinusP002Error2555, embedPair2542]

theorem sharedN05440MinusP002Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP002Output2556.1) + embedPair2542
            sharedN05440MinusP002Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP002Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP002Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP002Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP002Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP002Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP002Output2556, pairMagnitude2542]

def sharedN05440MinusP003Output2556 : RatState2542 :=
  (((((-87241822855911911563400556314471745) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-33821823401309118702122571323232333) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((52777713574168061994876877403937 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440MinusP003Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP003Output2556.1‖ ≤ (sharedN05440MinusP003Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP003BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP003Output2556,
    kernelN05440MinusP003Center2555, kernelN05440MinusP003Error2555, embedPair2542]

theorem sharedN05440MinusP003Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP003Output2556.1) + embedPair2542
            sharedN05440MinusP003Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP003Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP003Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP003Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP003Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP003Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP003Output2556, pairMagnitude2542]

def sharedN05440MinusP004Output2556 : RatState2542 :=
  (((((-92368363498077763200615907375097755) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((35809275595485935311450143559984851 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((1744663336729100491513849203247 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168)))

theorem sharedN05440MinusP004Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP004Output2556.1‖ ≤ (sharedN05440MinusP004Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP004BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP004Output2556,
    kernelN05440MinusP004Center2555, kernelN05440MinusP004Error2555, embedPair2542]

theorem sharedN05440MinusP004Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP004Output2556.1) + embedPair2542
            sharedN05440MinusP004Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP004Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP004Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP004Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP004Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP004Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP004Output2556, pairMagnitude2542]

def sharedN05440MinusP005Output2556 : RatState2542 :=
  ((((58440655205264784253542505258651371 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((5392063690868360224307101704391 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440MinusP005Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP005Output2556.1‖ ≤ (sharedN05440MinusP005Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP005BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP005Output2556,
    kernelN05440MinusP005Center2555, kernelN05440MinusP005Error2555, embedPair2542]

theorem sharedN05440MinusP005Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP005Output2556.1) + embedPair2542
            sharedN05440MinusP005Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP005Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP005Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP005Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP005Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP005Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP005Output2556, pairMagnitude2542]

def sharedN05440MinusP006Output2556 : RatState2542 :=
  ((((81087962221925884035765162278375503 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((3702723538938007690129329773821 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440MinusP006Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP006Output2556.1‖ ≤ (sharedN05440MinusP006Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP006BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP006Output2556,
    kernelN05440MinusP006Center2555, kernelN05440MinusP006Error2555, embedPair2542]

theorem sharedN05440MinusP006Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP006Output2556.1) + embedPair2542
            sharedN05440MinusP006Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP006Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP006Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP006Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP006Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP006Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP006Output2556, pairMagnitude2542]

def sharedN05440MinusP007Output2556 : RatState2542 :=
  ((((23392107901773803867593395997467051 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1)),
    ((2126774035256946926737326396049 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem sharedN05440MinusP007Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP007Output2556.1‖ ≤ (sharedN05440MinusP007Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP007BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP007Output2556,
    kernelN05440MinusP007Center2555, kernelN05440MinusP007Error2555, embedPair2542]

theorem sharedN05440MinusP007Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP007Output2556.1) + embedPair2542
            sharedN05440MinusP007Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP007Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP007Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP007Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP007Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP007Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP007Output2556, pairMagnitude2542]

def sharedN05440MinusP008Output2556 : RatState2542 :=
  ((((57537443603401921390633830479701233 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((15478251147924734515746882554607549 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((11575521723662052280025085548421 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440MinusP008Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP008Output2556.1‖ ≤ (sharedN05440MinusP008Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP008BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP008Output2556,
    kernelN05440MinusP008Center2555, kernelN05440MinusP008Error2555, embedPair2542]

theorem sharedN05440MinusP008Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP008Output2556.1) + embedPair2542
            sharedN05440MinusP008Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP008Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP008Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP008Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP008Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP008Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP008Output2556, pairMagnitude2542]

def sharedN05440MinusP009Output2556 : RatState2542 :=
  (((((-44852642557681038107682380285967765) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-23754488556904829262836055396081811) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((34774923420691158720098641791685 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440MinusP009Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP009Output2556.1‖ ≤ (sharedN05440MinusP009Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP009BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP009Output2556,
    kernelN05440MinusP009Center2555, kernelN05440MinusP009Error2555, embedPair2542]

theorem sharedN05440MinusP009Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP009Output2556.1) + embedPair2542
            sharedN05440MinusP009Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP009Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP009Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP009Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP009Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP009Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP009Output2556, pairMagnitude2542]

def sharedN05440MinusP010Output2556 : RatState2542 :=
  (((((-1393429861033247907131675594061061) : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    ((23877898517905602507702050279895391 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((2135345849964300921452249795461 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336)))

theorem sharedN05440MinusP010Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP010Output2556.1‖ ≤ (sharedN05440MinusP010Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP010BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP010Output2556,
    kernelN05440MinusP010Center2555, kernelN05440MinusP010Error2555, embedPair2542]

theorem sharedN05440MinusP010Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP010Output2556.1) + embedPair2542
            sharedN05440MinusP010Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP010Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP010Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP010Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP010Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP010Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP010Output2556, pairMagnitude2542]

def sharedN05440MinusP011Output2556 : RatState2542 :=
  ((((21677349661823418260054337967759011 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((15408915768246468071665926197435201 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((976176441297065170493648203653 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168)))

theorem sharedN05440MinusP011Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP011Output2556.1‖ ≤ (sharedN05440MinusP011Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP011BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP011Output2556,
    kernelN05440MinusP011Center2555, kernelN05440MinusP011Error2555, embedPair2542]

theorem sharedN05440MinusP011Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP011Output2556.1) + embedPair2542
            sharedN05440MinusP011Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP011Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP011Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP011Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP011Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP011Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP011Output2556, pairMagnitude2542]

def sharedN05440MinusP012Output2556 : RatState2542 :=
  ((((64981192871236934929299603481569641 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((6804926438889422414819218834034259 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((4396854203489918989623838475413 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem sharedN05440MinusP012Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP012Output2556.1‖ ≤ (sharedN05440MinusP012Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP012BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP012Output2556,
    kernelN05440MinusP012Center2555, kernelN05440MinusP012Error2555, embedPair2542]

theorem sharedN05440MinusP012Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP012Output2556.1) + embedPair2542
            sharedN05440MinusP012Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP012Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP012Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP012Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP012Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP012Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP012Output2556, pairMagnitude2542]

def sharedN05440MinusP013Output2556 : RatState2542 :=
  ((((39382765271224552272061736665356415 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-26066550646370625254922894967874555) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((7355829096510237871649470901867 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem sharedN05440MinusP013Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP013Output2556.1‖ ≤ (sharedN05440MinusP013Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP013BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP013Output2556,
    kernelN05440MinusP013Center2555, kernelN05440MinusP013Error2555, embedPair2542]

theorem sharedN05440MinusP013Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP013Output2556.1) + embedPair2542
            sharedN05440MinusP013Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP013Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP013Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP013Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP013Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP013Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP013Output2556, pairMagnitude2542]

def sharedN05440MinusP014Output2556 : RatState2542 :=
  (((((-62168845630609279066093426989327931) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-10048595471072856334951689568819431) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((17482014299399900349848528141407 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440MinusP014Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP014Output2556.1‖ ≤ (sharedN05440MinusP014Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP014BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP014Output2556,
    kernelN05440MinusP014Center2555, kernelN05440MinusP014Error2555, embedPair2542]

theorem sharedN05440MinusP014Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP014Output2556.1) + embedPair2542
            sharedN05440MinusP014Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP014Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP014Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP014Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP014Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP014Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP014Output2556, pairMagnitude2542]

def sharedN05440MinusP015Output2556 : RatState2542 :=
  (((((-1011769251304330505760896803558561) : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    ((56750481799658991252986141589092645 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((43319910888660698020942386707399 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440MinusP015Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP015Output2556.1‖ ≤ (sharedN05440MinusP015Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP015BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP015Output2556,
    kernelN05440MinusP015Center2555, kernelN05440MinusP015Error2555, embedPair2542]

theorem sharedN05440MinusP015Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP015Output2556.1) + embedPair2542
            sharedN05440MinusP015Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP015Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP015Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP015Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP015Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP015Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP015Output2556, pairMagnitude2542]

def sharedN05440MinusP016Output2556 : RatState2542 :=
  ((((7368508287208723833617869710274807 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((58310752188159705405092269008552461 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((20160656965579976439248333390805 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440MinusP016Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP016Output2556.1‖ ≤ (sharedN05440MinusP016Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP016BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP016Output2556,
    kernelN05440MinusP016Center2555, kernelN05440MinusP016Error2555, embedPair2542]

theorem sharedN05440MinusP016Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP016Output2556.1) + embedPair2542
            sharedN05440MinusP016Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP016Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP016Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP016Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP016Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP016Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP016Output2556, pairMagnitude2542]

def sharedN05440MinusP017Output2556 : RatState2542 :=
  ((((5611306955666891588827560422351355 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    (((-11868312439964319863065903548417661) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((36280065101144762218000893027007 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440MinusP017Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP017Output2556.1‖ ≤ (sharedN05440MinusP017Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP017BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP017Output2556,
    kernelN05440MinusP017Center2555, kernelN05440MinusP017Error2555, embedPair2542]

theorem sharedN05440MinusP017Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP017Output2556.1) + embedPair2542
            sharedN05440MinusP017Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP017Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP017Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP017Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP017Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP017Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP017Output2556, pairMagnitude2542]

def sharedN05440MinusP018Output2556 : RatState2542 :=
  ((((1077535662890610878976762588306111 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-8162622623876380485045945234927505) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))),
    ((20947289263051892501081730537617 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440MinusP018Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP018Output2556.1‖ ≤ (sharedN05440MinusP018Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP018BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP018Output2556,
    kernelN05440MinusP018Center2555, kernelN05440MinusP018Error2555, embedPair2542]

theorem sharedN05440MinusP018Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP018Output2556.1) + embedPair2542
            sharedN05440MinusP018Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP018Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP018Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP018Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP018Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP018Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP018Output2556, pairMagnitude2542]

def sharedN05440MinusP019Output2556 : RatState2542 :=
  (((((-7815442200531936289270772578682233) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    (((-9482479847814596727027007597998467) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((8423310590053608888693934210313 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem sharedN05440MinusP019Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP019Output2556.1‖ ≤ (sharedN05440MinusP019Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP019BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP019Output2556,
    kernelN05440MinusP019Center2555, kernelN05440MinusP019Error2555, embedPair2542]

theorem sharedN05440MinusP019Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP019Output2556.1) + embedPair2542
            sharedN05440MinusP019Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP019Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP019Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP019Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP019Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP019Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP019Output2556, pairMagnitude2542]

def sharedN05440MinusP020Output2556 : RatState2542 :=
  (((((-6980419667796297935851867826465579) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((59069808794261997953049105203250151 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((34476628344028209087924675364365 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440MinusP020Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP020Output2556.1‖ ≤ (sharedN05440MinusP020Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP020BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP020Output2556,
    kernelN05440MinusP020Center2555, kernelN05440MinusP020Error2555, embedPair2542]

theorem sharedN05440MinusP020Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP020Output2556.1) + embedPair2542
            sharedN05440MinusP020Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP020Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP020Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP020Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP020Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP020Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP020Output2556, pairMagnitude2542]

def sharedN05440MinusP021Output2556 : RatState2542 :=
  ((((5546667542089404187799787667176599 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((11989237669076459402226118305731901 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((3065659187948564675395851116657 : ℚ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672)))

theorem sharedN05440MinusP021Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP021Output2556.1‖ ≤ (sharedN05440MinusP021Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP021BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP021Output2556,
    kernelN05440MinusP021Center2555, kernelN05440MinusP021Error2555, embedPair2542]

theorem sharedN05440MinusP021Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP021Output2556.1) + embedPair2542
            sharedN05440MinusP021Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP021Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP021Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP021Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP021Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP021Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP021Output2556, pairMagnitude2542]

def sharedN05440MinusP022Output2556 : RatState2542 :=
  ((((63817657112379587604278607655993249 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((14006037680027037671027376792218359 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((16548566980209543060734829991673 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440MinusP022Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP022Output2556.1‖ ≤ (sharedN05440MinusP022Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP022BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP022Output2556,
    kernelN05440MinusP022Center2555, kernelN05440MinusP022Error2555, embedPair2542]

theorem sharedN05440MinusP022Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP022Output2556.1) + embedPair2542
            sharedN05440MinusP022Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP022Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP022Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP022Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP022Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP022Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP022Output2556, pairMagnitude2542]

def sharedN05440MinusP023Output2556 : RatState2542 :=
  ((((546097029598654723288844450884957 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-32650003443169062489187091249533325) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((32628954055431805277938626737177 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440MinusP023Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP023Output2556.1‖ ≤ (sharedN05440MinusP023Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP023BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP023Output2556,
    kernelN05440MinusP023Center2555, kernelN05440MinusP023Error2555, embedPair2542]

theorem sharedN05440MinusP023Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP023Output2556.1) + embedPair2542
            sharedN05440MinusP023Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP023Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP023Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP023Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP023Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP023Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP023Output2556, pairMagnitude2542]

def sharedN05440MinusP024Output2556 : RatState2542 :=
  (((((-45593317821105483971316900705359595) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-23399315272413716566477367365491267) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((17847018982919138271653029957335 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440MinusP024Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP024Output2556.1‖ ≤ (sharedN05440MinusP024Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP024BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP024Output2556,
    kernelN05440MinusP024Center2555, kernelN05440MinusP024Error2555, embedPair2542]

theorem sharedN05440MinusP024Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP024Output2556.1) + embedPair2542
            sharedN05440MinusP024Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP024Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP024Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP024Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP024Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP024Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP024Output2556, pairMagnitude2542]

def sharedN05440MinusP025Output2556 : RatState2542 :=
  (((((-63875530228774256251539673558941199) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((13739690273093361774554214402741597 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((33910517938688277445528691085679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440MinusP025Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP025Output2556.1‖ ≤ (sharedN05440MinusP025Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP025BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP025Output2556,
    kernelN05440MinusP025Center2555, kernelN05440MinusP025Error2555, embedPair2542]

theorem sharedN05440MinusP025Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP025Output2556.1) + embedPair2542
            sharedN05440MinusP025Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP025Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP025Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP025Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP025Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP025Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP025Output2556, pairMagnitude2542]

def sharedN05440MinusP026Output2556 : RatState2542 :=
  (((((-20950550992964738097325173016083277) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((61886483693119730794800201012074801 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((44459671579128562018930784651135 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440MinusP026Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP026Output2556.1‖ ≤ (sharedN05440MinusP026Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP026BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP026Output2556,
    kernelN05440MinusP026Center2555, kernelN05440MinusP026Error2555, embedPair2542]

theorem sharedN05440MinusP026Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP026Output2556.1) + embedPair2542
            sharedN05440MinusP026Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP026Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP026Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP026Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP026Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP026Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP026Output2556, pairMagnitude2542]

def sharedN05440MinusP027Output2556 : RatState2542 :=
  ((((59991988506244458811825167593834681 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((6470238432016159455881033226313381 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((33008144590911146402814644922329 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN05440MinusP027Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP027Output2556.1‖ ≤ (sharedN05440MinusP027Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP027BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP027Output2556,
    kernelN05440MinusP027Center2555, kernelN05440MinusP027Error2555, embedPair2542]

theorem sharedN05440MinusP027Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP027Output2556.1) + embedPair2542
            sharedN05440MinusP027Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP027Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP027Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP027Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP027Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP027Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP027Output2556, pairMagnitude2542]

def sharedN05440MinusP028Output2556 : RatState2542 :=
  ((((32125150056192319319468236911328825 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-5932145191161807255973200262839383) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((14695639712678390958218844296803 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440MinusP028Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP028Output2556.1‖ ≤ (sharedN05440MinusP028Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP028BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP028Output2556,
    kernelN05440MinusP028Center2555, kernelN05440MinusP028Error2555, embedPair2542]

theorem sharedN05440MinusP028Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP028Output2556.1) + embedPair2542
            sharedN05440MinusP028Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP028Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP028Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP028Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP028Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP028Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP028Output2556, pairMagnitude2542]

def sharedN05440MinusP029Output2556 : RatState2542 :=
  ((((15378381360168585499056981868587243 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-7205557748376929678185862056215515) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))),
    ((22065251884334472186547917618333 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN05440MinusP029Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP029Output2556.1‖ ≤ (sharedN05440MinusP029Output2556.2 : ℝ) := by
  have h := kernelN05440MinusP029BaseError2555
  convert h using 1
  all_goals norm_num [sharedN05440MinusPosition2556, kernelN05440MinusPosition2555,
      sharedN05440MinusP029Output2556,
    kernelN05440MinusP029Center2555, kernelN05440MinusP029Error2555, embedPair2542]

theorem sharedN05440MinusP029Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN05440MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN05440MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP029Output2556.1) + embedPair2542
            sharedN05440MinusP029Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN05440MinusPosition2556 - embedPair2542
            sharedN05440MinusP029Output2556.1‖ + ‖embedPair2542
            sharedN05440MinusP029Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN05440MinusP029Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN05440MinusP029Output2556.1 : ℝ) :=
      add_le_add sharedN05440MinusP029Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN05440MinusP029Output2556, pairMagnitude2542]

noncomputable def sharedN05440MinusValue2556 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 sharedN05440MinusP000Output2556.1
  | 1 => embedPair2542 sharedN05440MinusP001Output2556.1
  | 2 => embedPair2542 sharedN05440MinusP002Output2556.1
  | 3 => embedPair2542 sharedN05440MinusP003Output2556.1
  | 4 => embedPair2542 sharedN05440MinusP004Output2556.1
  | 5 => embedPair2542 sharedN05440MinusP005Output2556.1
  | 6 => embedPair2542 sharedN05440MinusP006Output2556.1
  | 7 => embedPair2542 sharedN05440MinusP007Output2556.1
  | 8 => embedPair2542 sharedN05440MinusP008Output2556.1
  | 9 => embedPair2542 sharedN05440MinusP009Output2556.1
  | 10 => embedPair2542 sharedN05440MinusP010Output2556.1
  | 11 => embedPair2542 sharedN05440MinusP011Output2556.1
  | 12 => embedPair2542 sharedN05440MinusP012Output2556.1
  | 13 => embedPair2542 sharedN05440MinusP013Output2556.1
  | 14 => embedPair2542 sharedN05440MinusP014Output2556.1
  | 15 => embedPair2542 sharedN05440MinusP015Output2556.1
  | 16 => embedPair2542 sharedN05440MinusP016Output2556.1
  | 17 => embedPair2542 sharedN05440MinusP017Output2556.1
  | 18 => embedPair2542 sharedN05440MinusP018Output2556.1
  | 19 => embedPair2542 sharedN05440MinusP019Output2556.1
  | 20 => embedPair2542 sharedN05440MinusP020Output2556.1
  | 21 => embedPair2542 sharedN05440MinusP021Output2556.1
  | 22 => embedPair2542 sharedN05440MinusP022Output2556.1
  | 23 => embedPair2542 sharedN05440MinusP023Output2556.1
  | 24 => embedPair2542 sharedN05440MinusP024Output2556.1
  | 25 => embedPair2542 sharedN05440MinusP025Output2556.1
  | 26 => embedPair2542 sharedN05440MinusP026Output2556.1
  | 27 => embedPair2542 sharedN05440MinusP027Output2556.1
  | 28 => embedPair2542 sharedN05440MinusP028Output2556.1
  | 29 => embedPair2542 sharedN05440MinusP029Output2556.1
  | _ => 0

noncomputable def sharedN05440MinusError2556 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (sharedN05440MinusP000Output2556.2 : ℝ)
  | 1 => (sharedN05440MinusP001Output2556.2 : ℝ)
  | 2 => (sharedN05440MinusP002Output2556.2 : ℝ)
  | 3 => (sharedN05440MinusP003Output2556.2 : ℝ)
  | 4 => (sharedN05440MinusP004Output2556.2 : ℝ)
  | 5 => (sharedN05440MinusP005Output2556.2 : ℝ)
  | 6 => (sharedN05440MinusP006Output2556.2 : ℝ)
  | 7 => (sharedN05440MinusP007Output2556.2 : ℝ)
  | 8 => (sharedN05440MinusP008Output2556.2 : ℝ)
  | 9 => (sharedN05440MinusP009Output2556.2 : ℝ)
  | 10 => (sharedN05440MinusP010Output2556.2 : ℝ)
  | 11 => (sharedN05440MinusP011Output2556.2 : ℝ)
  | 12 => (sharedN05440MinusP012Output2556.2 : ℝ)
  | 13 => (sharedN05440MinusP013Output2556.2 : ℝ)
  | 14 => (sharedN05440MinusP014Output2556.2 : ℝ)
  | 15 => (sharedN05440MinusP015Output2556.2 : ℝ)
  | 16 => (sharedN05440MinusP016Output2556.2 : ℝ)
  | 17 => (sharedN05440MinusP017Output2556.2 : ℝ)
  | 18 => (sharedN05440MinusP018Output2556.2 : ℝ)
  | 19 => (sharedN05440MinusP019Output2556.2 : ℝ)
  | 20 => (sharedN05440MinusP020Output2556.2 : ℝ)
  | 21 => (sharedN05440MinusP021Output2556.2 : ℝ)
  | 22 => (sharedN05440MinusP022Output2556.2 : ℝ)
  | 23 => (sharedN05440MinusP023Output2556.2 : ℝ)
  | 24 => (sharedN05440MinusP024Output2556.2 : ℝ)
  | 25 => (sharedN05440MinusP025Output2556.2 : ℝ)
  | 26 => (sharedN05440MinusP026Output2556.2 : ℝ)
  | 27 => (sharedN05440MinusP027Output2556.2 : ℝ)
  | 28 => (sharedN05440MinusP028Output2556.2 : ℝ)
  | 29 => (sharedN05440MinusP029Output2556.2 : ℝ)
  | _ => 0

theorem sharedN05440MinusExp_error2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN05440MinusPosition2556 - sharedN05440MinusValue2556 i‖
            ≤ sharedN05440MinusError2556 i := by
  fin_cases i
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP000Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP001Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP002Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP003Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP004Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP005Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP006Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP007Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP008Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP009Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP010Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP011Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP012Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP013Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP014Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP015Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP016Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP017Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP018Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP019Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP020Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP021Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP022Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP023Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP024Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP025Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP026Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP027Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP028Error2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP029Error2556

theorem sharedN05440MinusUnit_norm2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN05440MinusPosition2556‖ ≤ 1 := by
  fin_cases i
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP000Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP001Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP002Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP003Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP004Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP005Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP006Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP007Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP008Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP009Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP010Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP011Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP012Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP013Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP014Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP015Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP016Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP017Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP018Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP019Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP020Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP021Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP022Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP023Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP024Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP025Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP026Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP027Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP028Norm2556
  · simpa only [sharedN05440MinusValue2556, sharedN05440MinusError2556] using
      sharedN05440MinusP029Norm2556

noncomputable def sharedN05440MinusSumValue2556 : ℂ := ⟨(((((15259437906157027430201662 * 10^40
        + 1287329659729718825605879093918447269802) * 10^40
        + 7219803184041172131662171763609726189135) * 10^40
        + 5142833312865484389756831596348890957277) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816)),
    (((-(((1444936070459382229238662 * 10^40
        + 9677193661448056975425262862301665601226) * 10^40
        + 4723874756303100068995408771759808837289) * 10^40
        + 2153859962066789550882816175875783340509)) : ℝ) /
        (((6243497100631984462763194 * 10^40
        + 4595863326114971962853299423017183139192) * 10^40
        + 5074347763953124024061220612698394231965) * 10^40
        + 3862242813245790895951358576570612580352))⟩

noncomputable def sharedN05440MinusUpper2556 : ℝ := ((766536121 : ℝ) /
        2000000000)

theorem sharedN05440MinusSum_eq2556 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN05440MinusValue2556 i) =
      sharedN05440MinusSumValue2556 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN05440MinusValue2556,
      sharedN05440MinusSumValue2556, embedPair2542, sharedN05440MinusP000Output2556,
      sharedN05440MinusP001Output2556,
      sharedN05440MinusP002Output2556,
      sharedN05440MinusP003Output2556,
      sharedN05440MinusP004Output2556,
      sharedN05440MinusP005Output2556,
      sharedN05440MinusP006Output2556,
      sharedN05440MinusP007Output2556,
      sharedN05440MinusP008Output2556,
      sharedN05440MinusP009Output2556,
      sharedN05440MinusP010Output2556,
      sharedN05440MinusP011Output2556,
      sharedN05440MinusP012Output2556,
      sharedN05440MinusP013Output2556,
      sharedN05440MinusP014Output2556,
      sharedN05440MinusP015Output2556,
      sharedN05440MinusP016Output2556,
      sharedN05440MinusP017Output2556,
      sharedN05440MinusP018Output2556,
      sharedN05440MinusP019Output2556,
      sharedN05440MinusP020Output2556,
      sharedN05440MinusP021Output2556,
      sharedN05440MinusP022Output2556,
      sharedN05440MinusP023Output2556,
      sharedN05440MinusP024Output2556,
      sharedN05440MinusP025Output2556,
      sharedN05440MinusP026Output2556,
      sharedN05440MinusP027Output2556,
      sharedN05440MinusP028Output2556,
      sharedN05440MinusP029Output2556, Complex.mul_re, Complex.mul_im]

theorem sharedN05440MinusSum_norm2556 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN05440MinusValue2556 i‖ ≤
      ((958170151 : ℝ) /
        2500000000) := by
  rw [sharedN05440MinusSum_eq2556]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [sharedN05440MinusSumValue2556]

theorem sharedN05440MinusEvaluation_charge2556 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * sharedN05440MinusError2556 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN05440MinusError2556,
      sharedN05440MinusP000Output2556,
      sharedN05440MinusP001Output2556,
      sharedN05440MinusP002Output2556,
      sharedN05440MinusP003Output2556,
      sharedN05440MinusP004Output2556,
      sharedN05440MinusP005Output2556,
      sharedN05440MinusP006Output2556,
      sharedN05440MinusP007Output2556,
      sharedN05440MinusP008Output2556,
      sharedN05440MinusP009Output2556,
      sharedN05440MinusP010Output2556,
      sharedN05440MinusP011Output2556,
      sharedN05440MinusP012Output2556,
      sharedN05440MinusP013Output2556,
      sharedN05440MinusP014Output2556,
      sharedN05440MinusP015Output2556,
      sharedN05440MinusP016Output2556,
      sharedN05440MinusP017Output2556,
      sharedN05440MinusP018Output2556,
      sharedN05440MinusP019Output2556,
      sharedN05440MinusP020Output2556,
      sharedN05440MinusP021Output2556,
      sharedN05440MinusP022Output2556,
      sharedN05440MinusP023Output2556,
      sharedN05440MinusP024Output2556,
      sharedN05440MinusP025Output2556,
      sharedN05440MinusP026Output2556,
      sharedN05440MinusP027Output2556,
      sharedN05440MinusP028Output2556,
      sharedN05440MinusP029Output2556]

theorem sharedN05440MinusSigned_le2556 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 sharedN05440MinusPosition2556 ≤ sharedN05440MinusUpper2556 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN05440MinusPosition2556‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN05440MinusValue2556 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * sharedN05440MinusError2556 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (sharedN05440MinusExp_error2556 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN05440MinusPosition2556‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (sharedN05440MinusUnit_norm2556 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN05440MinusPosition2556‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 sharedN05440MinusUpper2556
  linarith [sharedN05440MinusSum_norm2556, sharedN05440MinusEvaluation_charge2556]

theorem sharedN05440MinusPhysical_le2556 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 sharedN05440MinusPosition2556‖ ≤
      sharedN05440MinusUpper2556 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        sharedN05440MinusPosition2556
  simpa only [iteratedDeriv_zero] using h.trans sharedN05440MinusSigned_le2556

theorem sharedN05440MinusGrid2556 :
    -stripRadius2303 + (5440 : ℝ)*(2*stripRadius2303/10240) = sharedN05440MinusPosition2556 :=
        by
  norm_num [stripRadius2303, sharedN05440MinusPosition2556]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.sharedN05440MinusSigned_le2556
#print axioms ConnesWeilRH.Dev.sharedN05440MinusPhysical_le2556
