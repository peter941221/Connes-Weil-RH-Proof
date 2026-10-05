import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def nodeExpN02705MinusPointPosition2577 : ℝ := (((-31653888483) : ℝ) /
        10240000000)

theorem nodeExpN02705MinusPointZero2577 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def nodeExpN02705MinusPointP000Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02705MinusPointP000Error2577 : ℝ := 0

theorem nodeExpN02705MinusPointP000Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02705MinusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |nodeExpN02705MinusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02705MinusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem nodeExpN02705MinusPointP000BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP000Center2577‖ ≤
          nodeExpN02705MinusPointP000Error2577 := by
  rw [nodeExpN02705MinusPointP000Exterior2577]
  norm_num [nodeExpN02705MinusPointP000Center2577, nodeExpN02705MinusPointP000Error2577,
      nodeExpN02705MinusPointZero2577]

def nodeExpN02705MinusPointP001Input2577 : RatPair2542 :=
    ((((-(2972220902592775860753336338870765187961 *
    10^40
        + 1585476530521012854490327853635425132317)) : ℚ) /
        (8511279604154028674011082907130390598740 * 10^40
        + 8004112173150622382000883902709760000000)),
    ((174865292075716174968560007 : ℚ) /
        737869762948382064640000000))

def nodeExpN02705MinusPointP001Center2577 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP001Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP001BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP001Center2577‖ ≤
          nodeExpN02705MinusPointP001Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP001Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP001Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP001Input2577 9 =
      (nodeExpN02705MinusPointP001Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP001Input2577 9).2 : ℝ) =
      nodeExpN02705MinusPointP001Error2577 := by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP001Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP001Input2577 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          nodeExpN02705MinusPointP001Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP001Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP002Input2577 : RatPair2542 :=
    ((((-(1558232809265543759449685049388990963208 *
    10^40
        + 5657148282816822161277233008769014177453)) : ℚ) /
        (6677151314258110391825028471093402075161 * 10^40
        + 8148315816099404395428715739217920000000)),
    (((-174865292075716174968560007) : ℚ) /
        368934881474191032320000000))

def nodeExpN02705MinusPointP002Center2577 : RatPair2542 := ((((-6232910466508290662095) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-7671910554999950297919) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

noncomputable def nodeExpN02705MinusPointP002Error2577 : ℝ := ((62258049251692668505 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP002BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP002Center2577‖ ≤
          nodeExpN02705MinusPointP002Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP002Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP002Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP002Input2577 8 =
      (nodeExpN02705MinusPointP002Center2577, ((62258049251692668505 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP002Input2577 8).2 : ℝ) =
      nodeExpN02705MinusPointP002Error2577 := by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP002Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP002Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02705MinusPointP002Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP002Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP003Input2577 : RatPair2542 := ((((-((550 * 10^40
        + 3595636945123166861610172112009740757253) * 10^40
        + 4707504622032470410174329256036448054837)) : ℚ) /
        ((3259 * 10^40
        + 8976654890313777338921755240451858920673) * 10^40
        + 3765349097629268219761063158087680000000)),
    (((-174865292075716174968560007) : ℚ) /
        368934881474191032320000000))

def nodeExpN02705MinusPointP003Center2577 : RatPair2542 := ((((-93385857423547319201975676215) :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-229891941848088526221276769381) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

noncomputable def nodeExpN02705MinusPointP003Error2577 : ℝ := ((874492453823048358099631199 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP003BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP003Center2577‖ ≤
          nodeExpN02705MinusPointP003Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP003Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP003Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP003Input2577 8 =
      (nodeExpN02705MinusPointP003Center2577, ((874492453823048358099631199 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP003Input2577 8).2 : ℝ) =
      nodeExpN02705MinusPointP003Error2577 := by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP003Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP003Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02705MinusPointP003Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP003Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP004Input2577 : RatPair2542 := ((((-((17 * 10^40
        + 2533280590083662039217955279786228756184) * 10^40
        + 5273242798277482655099909987298882195197)) : ℚ) /
        ((119 * 10^40
        + 2496410941960060508819208543369047417438) * 10^40
        + 2834992468434524816007071221678080000000)),
    ((174865292075716174968560007 : ℚ) /
        368934881474191032320000000))

def nodeExpN02705MinusPointP004Center2577 : RatPair2542 := ((((-5644135271377406361162294963633)
    : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((55577632561868580858707835001315 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

noncomputable def nodeExpN02705MinusPointP004Error2577 : ℝ := ((412739842713913026403732476439 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP004BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP004Center2577‖ ≤
          nodeExpN02705MinusPointP004Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP004Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP004Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP004Input2577 8 =
      (nodeExpN02705MinusPointP004Center2577, ((412739842713913026403732476439 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP004Input2577 8).2 : ℝ) =
      nodeExpN02705MinusPointP004Error2577 := by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP004Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP004Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02705MinusPointP004Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP004Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP005Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02705MinusPointP005Error2577 : ℝ := 0

theorem nodeExpN02705MinusPointP005Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02705MinusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |nodeExpN02705MinusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02705MinusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem nodeExpN02705MinusPointP005BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP005Center2577‖ ≤
          nodeExpN02705MinusPointP005Error2577 := by
  rw [nodeExpN02705MinusPointP005Exterior2577]
  norm_num [nodeExpN02705MinusPointP005Center2577, nodeExpN02705MinusPointP005Error2577,
      nodeExpN02705MinusPointZero2577]

def nodeExpN02705MinusPointP006Input2577 : RatPair2542 :=
    ((((-1009401942711546853650056001574587) : ℚ) /
        1771445797272420243763363840000000),
    ((0 : ℚ) /
        1))

def nodeExpN02705MinusPointP006Center2577 : RatPair2542 := (((30816524370707993 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP006Error2577 : ℝ := ((4933337008969 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeExpN02705MinusPointP006BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP006Center2577‖ ≤
          nodeExpN02705MinusPointP006Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP006Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP006Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP006Input2577 7 =
      (nodeExpN02705MinusPointP006Center2577, ((4933337008969 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP006Input2577 7).2 : ℝ) =
      nodeExpN02705MinusPointP006Error2577 := by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP006Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP006Input2577 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          nodeExpN02705MinusPointP006Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP006Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP007Input2577 : RatPair2542 := ((((-((550 * 10^40
        + 3595636945123166861610172112009740757253) * 10^40
        + 4707504622032470410174329256036448054837)) : ℚ) /
        ((814 * 10^40
        + 9744163722578444334730438810112964730168) * 10^40
        + 3441337274407317054940265789521920000000)),
    ((0 : ℚ) /
        1))

def nodeExpN02705MinusPointP007Center2577 : RatPair2542 := (((248135493820243347566162584705 : ℚ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP007Error2577 : ℝ := ((17152272637126015450671225 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeExpN02705MinusPointP007BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP007Center2577‖ ≤
          nodeExpN02705MinusPointP007Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP007Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP007Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP007Input2577 6 =
      (nodeExpN02705MinusPointP007Center2577, ((17152272637126015450671225 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP007Input2577 6).2 : ℝ) =
      nodeExpN02705MinusPointP007Error2577 := by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP007Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP007Input2577 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          nodeExpN02705MinusPointP007Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP007Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP008Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((125937256369443206862002451 : ℚ) /
        23611832414348226068480000000))

def nodeExpN02705MinusPointP008Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP008Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP008BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP008Center2577‖ ≤
          nodeExpN02705MinusPointP008Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP008Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP008Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP008Input2577 13 =
      (nodeExpN02705MinusPointP008Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP008Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP008Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP008Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP008Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP008Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP008Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP009Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((187301696272790732683750413 : ℚ) /
        23611832414348226068480000000))

def nodeExpN02705MinusPointP009Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP009Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP009BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP009Center2577‖ ≤
          nodeExpN02705MinusPointP009Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP009Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP009Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP009Input2577 13 =
      (nodeExpN02705MinusPointP009Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP009Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP009Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP009Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP009Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP009Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP009Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP010Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((111420588356197715176385643 : ℚ) /
        11805916207174113034240000000))

def nodeExpN02705MinusPointP010Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP010Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP010BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP010Center2577‖ ≤
          nodeExpN02705MinusPointP010Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP010Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP010Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP010Input2577 13 =
      (nodeExpN02705MinusPointP010Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP010Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP010Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP010Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP010Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP010Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP010Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP011Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((123268206202301004985337883 : ℚ) /
        11805916207174113034240000000))

def nodeExpN02705MinusPointP011Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP011Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP011BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP011Center2577‖ ≤
          nodeExpN02705MinusPointP011Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP011Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP011Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP011Input2577 13 =
      (nodeExpN02705MinusPointP011Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP011Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP011Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP011Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP011Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP011Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP011Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP012Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((2710788774631016534924847 : ℚ) /
        236118324143482260684800000))

def nodeExpN02705MinusPointP012Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP012Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP012BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP012Center2577‖ ≤
          nodeExpN02705MinusPointP012Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP012Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP012Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP012Input2577 13 =
      (nodeExpN02705MinusPointP012Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP012Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP012Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP012Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP012Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP012Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP012Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP013Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((29344407147130955527319553 : ℚ) /
        2361183241434822606848000000))

def nodeExpN02705MinusPointP013Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP013Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP013BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP013Center2577‖ ≤
          nodeExpN02705MinusPointP013Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP013Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP013Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP013Input2577 13 =
      (nodeExpN02705MinusPointP013Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP013Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP013Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP013Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP013Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP013Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP013Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP014Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((167442242677902990093140313 : ℚ) /
        11805916207174113034240000000))

def nodeExpN02705MinusPointP014Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP014Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP014BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP014Center2577‖ ≤
          nodeExpN02705MinusPointP014Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP014Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP014Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP014Input2577 13 =
      (nodeExpN02705MinusPointP014Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP014Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP014Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP014Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP014Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP014Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP014Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP015Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((182288341473529359843979701 : ℚ) /
        11805916207174113034240000000))

def nodeExpN02705MinusPointP015Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP015Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP015BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP015Center2577‖ ≤
          nodeExpN02705MinusPointP015Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP015Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP015Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP015Input2577 13 =
      (nodeExpN02705MinusPointP015Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP015Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP015Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP015Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP015Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP015Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP015Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP016Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((96508645919919764395179147 : ℚ) /
        5902958103587056517120000000))

def nodeExpN02705MinusPointP016Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP016Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP016BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP016Center2577‖ ≤
          nodeExpN02705MinusPointP016Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP016Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP016Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP016Input2577 13 =
      (nodeExpN02705MinusPointP016Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP016Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP016Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP016Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP016Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP016Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP016Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP017Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((213857607167923887040711041 : ℚ) /
        11805916207174113034240000000))

def nodeExpN02705MinusPointP017Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP017Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP017BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP017Center2577‖ ≤
          nodeExpN02705MinusPointP017Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP017Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP017Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP017Input2577 13 =
      (nodeExpN02705MinusPointP017Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP017Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP017Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP017Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP017Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP017Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP017Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP018Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((55434221733839136935063079 : ℚ) /
        2951479051793528258560000000))

def nodeExpN02705MinusPointP018Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP018Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP018BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP018Center2577‖ ≤
          nodeExpN02705MinusPointP018Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP018Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP018Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP018Input2577 13 =
      (nodeExpN02705MinusPointP018Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP018Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP018Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP018Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP018Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP018Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP018Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP019Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((11798844492939419238077853 : ℚ) /
        590295810358705651712000000))

def nodeExpN02705MinusPointP019Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP019Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP019BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP019Center2577‖ ≤
          nodeExpN02705MinusPointP019Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP019Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP019Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP019Input2577 13 =
      (nodeExpN02705MinusPointP019Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP019Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP019Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP019Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP019Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP019Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP019Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP020Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((251461754510132159483335377 : ℚ) /
        11805916207174113034240000000))

def nodeExpN02705MinusPointP020Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP020Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP020BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP020Center2577‖ ≤
          nodeExpN02705MinusPointP020Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP020Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP020Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP020Input2577 13 =
      (nodeExpN02705MinusPointP020Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP020Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP020Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP020Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP020Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP020Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP020Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP021Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((264384479371882101864279921 : ℚ) /
        11805916207174113034240000000))

def nodeExpN02705MinusPointP021Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP021Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP021BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP021Center2577‖ ≤
          nodeExpN02705MinusPointP021Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP021Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP021Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP021Input2577 13 =
      (nodeExpN02705MinusPointP021Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP021Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP021Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP021Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP021Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP021Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP021Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP022Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((54199761301639112700100539 : ℚ) /
        2361183241434822606848000000))

def nodeExpN02705MinusPointP022Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP022Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP022BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP022Center2577‖ ≤
          nodeExpN02705MinusPointP022Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP022Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP022Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP022Input2577 13 =
      (nodeExpN02705MinusPointP022Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP022Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP022Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP022Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP022Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP022Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP022Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP023Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((145034570365256380837972839 : ℚ) /
        5902958103587056517120000000))

def nodeExpN02705MinusPointP023Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP023Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP023BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP023Center2577‖ ≤
          nodeExpN02705MinusPointP023Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP023Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP023Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP023Input2577 13 =
      (nodeExpN02705MinusPointP023Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP023Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP023Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP023Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP023Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP023Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP023Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP024Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((149416547034989152754795001 : ℚ) /
        5902958103587056517120000000))

def nodeExpN02705MinusPointP024Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP024Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP024BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP024Center2577‖ ≤
          nodeExpN02705MinusPointP024Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP024Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP024Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP024Input2577 13 =
      (nodeExpN02705MinusPointP024Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP024Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP024Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP024Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP024Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP024Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP024Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP025Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((4840960678205345786172339 : ℚ) /
        184467440737095516160000000))

def nodeExpN02705MinusPointP025Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP025Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP025BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP025Center2577‖ ≤
          nodeExpN02705MinusPointP025Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP025Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP025Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP025Input2577 13 =
      (nodeExpN02705MinusPointP025Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP025Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP025Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP025Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP025Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP025Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP025Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP026Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((10032849088039534343392071 : ℚ) /
        368934881474191032320000000))

def nodeExpN02705MinusPointP026Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP026Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP026BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP026Center2577‖ ≤
          nodeExpN02705MinusPointP026Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP026Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP026Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP026Input2577 13 =
      (nodeExpN02705MinusPointP026Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP026Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP026Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP026Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP026Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP026Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP026Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP027Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((21078498488072348391776841 : ℚ) /
        737869762948382064640000000))

def nodeExpN02705MinusPointP027Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP027Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP027BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP027Center2577‖ ≤
          nodeExpN02705MinusPointP027Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP027Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP027Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP027Input2577 13 =
      (nodeExpN02705MinusPointP027Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP027Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP027Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP027Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP027Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP027Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP027Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP028Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((85917920262979814161755141 : ℚ) /
        2951479051793528258560000000))

def nodeExpN02705MinusPointP028Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP028Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP028BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP028Center2577‖ ≤
          nodeExpN02705MinusPointP028Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP028Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP028Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP028Input2577 13 =
      (nodeExpN02705MinusPointP028Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP028Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP028Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP028Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP028Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP028Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP028Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02705MinusPointP029Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((88359795091650310792539297 : ℚ) /
        2951479051793528258560000000))

def nodeExpN02705MinusPointP029Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02705MinusPointP029Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02705MinusPointP029BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeExpN02705MinusPointPosition2577 -
      embedPair2542 nodeExpN02705MinusPointP029Center2577‖ ≤
          nodeExpN02705MinusPointP029Error2577 := by
  have hx : |nodeExpN02705MinusPointPosition2577| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02705MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02705MinusPointP029Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02705MinusPointP029Input2577]
  have hs : compactExp2547 nodeExpN02705MinusPointP029Input2577 13 =
      (nodeExpN02705MinusPointP029Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02705MinusPointP029Input2577 13).2 : ℝ) =
      nodeExpN02705MinusPointP029Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02705MinusPointP029Error2577]
  have h := compactExp_error2547 nodeExpN02705MinusPointP029Input2577 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      nodeExpN02705MinusPointPosition2577 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          nodeExpN02705MinusPointP029Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02705MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02705MinusPointP029Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem nodeExpN02705MinusPointGrid2577 :
    -stripRadius2303 + (2705 : ℝ) * (2 * stripRadius2303 / 10240) =
      nodeExpN02705MinusPointPosition2577 := by
  norm_num [stripRadius2303, nodeExpN02705MinusPointPosition2577]

end ConnesWeilRH.Dev
