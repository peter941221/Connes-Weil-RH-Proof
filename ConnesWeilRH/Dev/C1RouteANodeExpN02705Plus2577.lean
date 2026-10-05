import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def nodeExpN02705PlusPointPosition2577 : ℝ := (((-31653888483) : ℝ) /
        10240000000)

theorem nodeExpN02705PlusPointZero2577 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def nodeExpN02705PlusPointP000Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02705PlusPointP000Error2577 : ℝ := 0

theorem nodeExpN02705PlusPointP000Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02705PlusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |nodeExpN02705PlusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02705PlusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem nodeExpN02705PlusPointP000BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP000Center2577‖ ≤ nodeExpN02705PlusPointP000Error2577
          := by
  rw [nodeExpN02705PlusPointP000Exterior2577]
  norm_num [nodeExpN02705PlusPointP000Center2577, nodeExpN02705PlusPointP000Error2577,
      nodeExpN02705PlusPointZero2577]

def nodeExpN02705PlusPointP001Input2577 : RatPair2542 :=
    ((((-(3023607753986956922918087616536546748773 *
    10^40
        + 6838956371435611813009672146364574867683)) : ℚ) /
        (8511279604154028674011082907130390598740 * 10^40
        + 8004112173150622382000883902709760000000)),
    ((174865292075716174968560007 : ℚ) /
        737869762948382064640000000))

def nodeExpN02705PlusPointP001Center2577 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP001Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP001BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP001Center2577‖ ≤ nodeExpN02705PlusPointP001Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP001Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP001Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP001Input2577 9 =
      (nodeExpN02705PlusPointP001Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP001Input2577 9).2 : ℝ) =
      nodeExpN02705PlusPointP001Error2577 := by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP001Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP001Input2577 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          nodeExpN02705PlusPointP001Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP001Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP002Input2577 : RatPair2542 :=
    ((((-(1638859412615474757001081566597964099486 *
    10^40
        + 4331734993860018146222766991230985822547)) : ℚ) /
        (6677151314258110391825028471093402075161 * 10^40
        + 8148315816099404395428715739217920000000)),
    (((-174865292075716174968560007) : ℚ) /
        368934881474191032320000000))

def nodeExpN02705PlusPointP002Center2577 : RatPair2542 := ((((-283269467081739495401) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-697336509513847197747) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

noncomputable def nodeExpN02705PlusPointP002Error2577 : ℝ := ((715960097493195589 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem nodeExpN02705PlusPointP002BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP002Center2577‖ ≤ nodeExpN02705PlusPointP002Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP002Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP002Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP002Input2577 8 =
      (nodeExpN02705PlusPointP002Center2577, ((715960097493195589 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP002Input2577 8).2 : ℝ) =
      nodeExpN02705PlusPointP002Error2577 := by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP002Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP002Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02705PlusPointP002Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP002Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP003Input2577 : RatPair2542 := ((((-((589 * 10^40
        + 7228286059281175019250523115978507539176) * 10^40
        + 7815277842486084277325670743963551945163)) : ℚ) /
        ((3259 * 10^40
        + 8976654890313777338921755240451858920673) * 10^40
        + 3765349097629268219761063158087680000000)),
    (((-174865292075716174968560007) : ℚ) /
        368934881474191032320000000))

def nodeExpN02705PlusPointP003Center2577 : RatPair2542 := ((((-2122071398865999455084083525) : ℚ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-10447987052535926618002489217) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

noncomputable def nodeExpN02705PlusPointP003Error2577 : ℝ := ((40226203768278363825291287 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP003BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP003Center2577‖ ≤ nodeExpN02705PlusPointP003Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP003Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP003Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP003Input2577 8 =
      (nodeExpN02705PlusPointP003Center2577, ((40226203768278363825291287 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP003Input2577 8).2 : ℝ) =
      nodeExpN02705PlusPointP003Error2577 := by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP003Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP003Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02705PlusPointP003Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP003Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP004Input2577 : RatPair2542 := ((((-((18 * 10^40
        + 6932674971925147917508549558213400347396) * 10^40
        + 486924668160436812400090012701117804803)) : ℚ) /
        ((119 * 10^40
        + 2496410941960060508819208543369047417438) * 10^40
        + 2834992468434524816007071221678080000000)),
    ((174865292075716174968560007 : ℚ) /
        368934881474191032320000000))

def nodeExpN02705PlusPointP004Center2577 : RatPair2542 := ((((-2052089403884525222829097911721) :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((2525857934597415579677892312545 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

noncomputable def nodeExpN02705PlusPointP004Error2577 : ℝ := ((4746455199159367328887253045 : ℝ)
    /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem nodeExpN02705PlusPointP004BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP004Center2577‖ ≤ nodeExpN02705PlusPointP004Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP004Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP004Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP004Input2577 8 =
      (nodeExpN02705PlusPointP004Center2577, ((4746455199159367328887253045 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP004Input2577 8).2 : ℝ) =
      nodeExpN02705PlusPointP004Error2577 := by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP004Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP004Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02705PlusPointP004Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP004Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP005Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02705PlusPointP005Error2577 : ℝ := 0

theorem nodeExpN02705PlusPointP005Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02705PlusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |nodeExpN02705PlusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02705PlusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem nodeExpN02705PlusPointP005BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP005Center2577‖ ≤ nodeExpN02705PlusPointP005Error2577
          := by
  rw [nodeExpN02705PlusPointP005Exterior2577]
  norm_num [nodeExpN02705PlusPointP005Center2577, nodeExpN02705PlusPointP005Error2577,
      nodeExpN02705PlusPointZero2577]

def nodeExpN02705PlusPointP006Input2577 : RatPair2542 := ((((-1052182359368453146349943998425413)
    : ℚ) /
        1771445797272420243763363840000000),
    ((0 : ℚ) /
        1))

def nodeExpN02705PlusPointP006Center2577 : RatPair2542 := (((700265187724743 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP006Error2577 : ℝ := ((1278008009571 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeExpN02705PlusPointP006BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP006Center2577‖ ≤ nodeExpN02705PlusPointP006Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP006Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP006Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP006Input2577 7 =
      (nodeExpN02705PlusPointP006Center2577, ((1278008009571 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP006Input2577 7).2 : ℝ) =
      nodeExpN02705PlusPointP006Error2577 := by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP006Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP006Input2577 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          nodeExpN02705PlusPointP006Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP006Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP007Input2577 : RatPair2542 := ((((-((589 * 10^40
        + 7228286059281175019250523115978507539176) * 10^40
        + 7815277842486084277325670743963551945163)) : ℚ) /
        ((814 * 10^40
        + 9744163722578444334730438810112964730168) * 10^40
        + 3441337274407317054940265789521920000000)),
    ((0 : ℚ) /
        1))

def nodeExpN02705PlusPointP007Center2577 : RatPair2542 := (((11277108740164686308975014741 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP007Error2577 : ℝ := ((409050545734292758920081 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem nodeExpN02705PlusPointP007BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP007Center2577‖ ≤ nodeExpN02705PlusPointP007Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP007Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP007Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP007Input2577 6 =
      (nodeExpN02705PlusPointP007Center2577, ((409050545734292758920081 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP007Input2577 6).2 : ℝ) =
      nodeExpN02705PlusPointP007Error2577 := by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP007Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP007Input2577 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          nodeExpN02705PlusPointP007Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP007Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP008Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((125937256369443206862002451 : ℚ) /
        23611832414348226068480000000))

def nodeExpN02705PlusPointP008Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP008Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP008BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP008Center2577‖ ≤ nodeExpN02705PlusPointP008Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP008Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP008Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP008Input2577 13 =
      (nodeExpN02705PlusPointP008Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP008Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP008Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP008Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP008Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP008Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP008Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP009Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((187301696272790732683750413 : ℚ) /
        23611832414348226068480000000))

def nodeExpN02705PlusPointP009Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP009Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP009BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP009Center2577‖ ≤ nodeExpN02705PlusPointP009Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP009Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP009Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP009Input2577 13 =
      (nodeExpN02705PlusPointP009Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP009Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP009Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP009Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP009Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP009Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP009Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP010Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((111420588356197715176385643 : ℚ) /
        11805916207174113034240000000))

def nodeExpN02705PlusPointP010Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP010Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP010BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP010Center2577‖ ≤ nodeExpN02705PlusPointP010Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP010Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP010Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP010Input2577 13 =
      (nodeExpN02705PlusPointP010Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP010Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP010Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP010Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP010Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP010Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP010Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP011Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((123268206202301004985337883 : ℚ) /
        11805916207174113034240000000))

def nodeExpN02705PlusPointP011Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP011Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP011BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP011Center2577‖ ≤ nodeExpN02705PlusPointP011Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP011Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP011Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP011Input2577 13 =
      (nodeExpN02705PlusPointP011Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP011Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP011Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP011Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP011Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP011Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP011Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP012Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((2710788774631016534924847 : ℚ) /
        236118324143482260684800000))

def nodeExpN02705PlusPointP012Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP012Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP012BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP012Center2577‖ ≤ nodeExpN02705PlusPointP012Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP012Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP012Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP012Input2577 13 =
      (nodeExpN02705PlusPointP012Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP012Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP012Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP012Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP012Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP012Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP012Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP013Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((29344407147130955527319553 : ℚ) /
        2361183241434822606848000000))

def nodeExpN02705PlusPointP013Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP013Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP013BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP013Center2577‖ ≤ nodeExpN02705PlusPointP013Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP013Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP013Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP013Input2577 13 =
      (nodeExpN02705PlusPointP013Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP013Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP013Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP013Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP013Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP013Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP013Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP014Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((167442242677902990093140313 : ℚ) /
        11805916207174113034240000000))

def nodeExpN02705PlusPointP014Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP014Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP014BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP014Center2577‖ ≤ nodeExpN02705PlusPointP014Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP014Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP014Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP014Input2577 13 =
      (nodeExpN02705PlusPointP014Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP014Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP014Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP014Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP014Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP014Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP014Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP015Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((182288341473529359843979701 : ℚ) /
        11805916207174113034240000000))

def nodeExpN02705PlusPointP015Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP015Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP015BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP015Center2577‖ ≤ nodeExpN02705PlusPointP015Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP015Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP015Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP015Input2577 13 =
      (nodeExpN02705PlusPointP015Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP015Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP015Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP015Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP015Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP015Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP015Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP016Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((96508645919919764395179147 : ℚ) /
        5902958103587056517120000000))

def nodeExpN02705PlusPointP016Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP016Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP016BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP016Center2577‖ ≤ nodeExpN02705PlusPointP016Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP016Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP016Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP016Input2577 13 =
      (nodeExpN02705PlusPointP016Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP016Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP016Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP016Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP016Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP016Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP016Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP017Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((213857607167923887040711041 : ℚ) /
        11805916207174113034240000000))

def nodeExpN02705PlusPointP017Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP017Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP017BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP017Center2577‖ ≤ nodeExpN02705PlusPointP017Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP017Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP017Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP017Input2577 13 =
      (nodeExpN02705PlusPointP017Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP017Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP017Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP017Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP017Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP017Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP017Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP018Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((55434221733839136935063079 : ℚ) /
        2951479051793528258560000000))

def nodeExpN02705PlusPointP018Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP018Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP018BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP018Center2577‖ ≤ nodeExpN02705PlusPointP018Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP018Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP018Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP018Input2577 13 =
      (nodeExpN02705PlusPointP018Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP018Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP018Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP018Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP018Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP018Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP018Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP019Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((11798844492939419238077853 : ℚ) /
        590295810358705651712000000))

def nodeExpN02705PlusPointP019Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP019Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP019BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP019Center2577‖ ≤ nodeExpN02705PlusPointP019Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP019Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP019Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP019Input2577 13 =
      (nodeExpN02705PlusPointP019Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP019Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP019Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP019Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP019Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP019Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP019Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP020Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((251461754510132159483335377 : ℚ) /
        11805916207174113034240000000))

def nodeExpN02705PlusPointP020Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP020Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP020BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP020Center2577‖ ≤ nodeExpN02705PlusPointP020Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP020Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP020Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP020Input2577 13 =
      (nodeExpN02705PlusPointP020Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP020Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP020Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP020Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP020Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP020Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP020Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP021Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((264384479371882101864279921 : ℚ) /
        11805916207174113034240000000))

def nodeExpN02705PlusPointP021Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP021Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP021BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP021Center2577‖ ≤ nodeExpN02705PlusPointP021Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP021Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP021Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP021Input2577 13 =
      (nodeExpN02705PlusPointP021Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP021Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP021Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP021Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP021Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP021Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP021Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP022Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((54199761301639112700100539 : ℚ) /
        2361183241434822606848000000))

def nodeExpN02705PlusPointP022Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP022Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP022BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP022Center2577‖ ≤ nodeExpN02705PlusPointP022Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP022Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP022Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP022Input2577 13 =
      (nodeExpN02705PlusPointP022Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP022Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP022Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP022Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP022Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP022Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP022Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP023Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((145034570365256380837972839 : ℚ) /
        5902958103587056517120000000))

def nodeExpN02705PlusPointP023Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP023Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP023BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP023Center2577‖ ≤ nodeExpN02705PlusPointP023Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP023Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP023Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP023Input2577 13 =
      (nodeExpN02705PlusPointP023Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP023Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP023Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP023Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP023Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP023Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP023Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP024Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((149416547034989152754795001 : ℚ) /
        5902958103587056517120000000))

def nodeExpN02705PlusPointP024Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP024Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP024BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP024Center2577‖ ≤ nodeExpN02705PlusPointP024Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP024Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP024Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP024Input2577 13 =
      (nodeExpN02705PlusPointP024Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP024Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP024Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP024Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP024Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP024Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP024Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP025Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((4840960678205345786172339 : ℚ) /
        184467440737095516160000000))

def nodeExpN02705PlusPointP025Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP025Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP025BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP025Center2577‖ ≤ nodeExpN02705PlusPointP025Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP025Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP025Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP025Input2577 13 =
      (nodeExpN02705PlusPointP025Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP025Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP025Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP025Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP025Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP025Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP025Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP026Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((10032849088039534343392071 : ℚ) /
        368934881474191032320000000))

def nodeExpN02705PlusPointP026Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP026Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP026BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP026Center2577‖ ≤ nodeExpN02705PlusPointP026Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP026Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP026Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP026Input2577 13 =
      (nodeExpN02705PlusPointP026Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP026Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP026Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP026Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP026Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP026Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP026Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP027Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((21078498488072348391776841 : ℚ) /
        737869762948382064640000000))

def nodeExpN02705PlusPointP027Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP027Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP027BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP027Center2577‖ ≤ nodeExpN02705PlusPointP027Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP027Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP027Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP027Input2577 13 =
      (nodeExpN02705PlusPointP027Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP027Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP027Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP027Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP027Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP027Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP027Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP028Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((85917920262979814161755141 : ℚ) /
        2951479051793528258560000000))

def nodeExpN02705PlusPointP028Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP028Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP028BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP028Center2577‖ ≤ nodeExpN02705PlusPointP028Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP028Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP028Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP028Input2577 13 =
      (nodeExpN02705PlusPointP028Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP028Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP028Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP028Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP028Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP028Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP028Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705PlusPointP029Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((88359795091650310792539297 : ℚ) /
        2951479051793528258560000000))

def nodeExpN02705PlusPointP029Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705PlusPointP029Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705PlusPointP029BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeExpN02705PlusPointPosition2577 -
      embedPair2542 nodeExpN02705PlusPointP029Center2577‖ ≤ nodeExpN02705PlusPointP029Error2577
          := by
  have hx : |nodeExpN02705PlusPointPosition2577| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705PlusPointP029Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705PlusPointP029Input2577]
  have hs : compactExp2547 nodeExpN02705PlusPointP029Input2577 13 =
      (nodeExpN02705PlusPointP029Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705PlusPointP029Input2577 13).2 : ℝ) =
      nodeExpN02705PlusPointP029Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705PlusPointP029Error2577]
  have h := compactExp_error2547 nodeExpN02705PlusPointP029Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      nodeExpN02705PlusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705PlusPointP029Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705PlusPointP029Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem nodeExpN02705PlusPointGrid2577 :
    -stripRadius2303 + (2705 : ℝ) * (2 * stripRadius2303 / 10240) =
      nodeExpN02705PlusPointPosition2577 := by
  norm_num [stripRadius2303, nodeExpN02705PlusPointPosition2577]

end ConnesWeilRH.Dev
