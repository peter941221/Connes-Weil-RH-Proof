import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def nodeExpN02704PlusPointPosition2577 : ℝ := (((-9895936151) : ℝ) /
        3200000000)

theorem nodeExpN02704PlusPointZero2577 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def nodeExpN02704PlusPointP000Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02704PlusPointP000Error2577 : ℝ := 0

theorem nodeExpN02704PlusPointP000Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02704PlusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |nodeExpN02704PlusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02704PlusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem nodeExpN02704PlusPointP000BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP000Center2577‖ ≤ nodeExpN02704PlusPointP000Error2577
          := by
  rw [nodeExpN02704PlusPointP000Exterior2577]
  norm_num [nodeExpN02704PlusPointP000Center2577, nodeExpN02704PlusPointP000Error2577,
      nodeExpN02704PlusPointZero2577]

def nodeExpN02704PlusPointP001Input2577 : RatPair2542 := ((((-((21 * 10^40
        + 2590665986622484827322845344600412856161) * 10^40
        + 1339369612967568308599015150185097693111)) : ℚ) /
        ((59 * 10^40
        + 5965149429887586107108459481843895661464) * 10^40
        + 568333469734220561590691302604800000000)),
    ((54668031270047913913566379 : ℚ) /
        230584300921369395200000000))

def nodeExpN02704PlusPointP001Center2577 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP001Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP001BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP001Center2577‖ ≤ nodeExpN02704PlusPointP001Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP001Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP001Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP001Input2577 9 =
      (nodeExpN02704PlusPointP001Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP001Input2577 9).2 : ℝ) =
      nodeExpN02704PlusPointP001Error2577 := by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP001Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP001Input2577 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          nodeExpN02704PlusPointP001Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP001Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP002Input2577 : RatPair2542 := ((((-((564 * 10^40
        + 6320295773356197331617375810041260089035) * 10^40
        + 1909897556892439653628817325904678324151)) : ℚ) /
        ((2298 * 10^40
        + 4999305507355519060301944907893290580952) * 10^40
        + 3852905515627880742725530420838400000000)),
    (((-54668031270047913913566379) : ℚ) /
        115292150460684697600000000))

def nodeExpN02704PlusPointP002Center2577 : RatPair2542 := ((((-150665789589046507317) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-646605045251160912061) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

noncomputable def nodeExpN02704PlusPointP002Error2577 : ℝ := ((2703320551278323549 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP002BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP002Center2577‖ ≤ nodeExpN02704PlusPointP002Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP002Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP002Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP002Input2577 8 =
      (nodeExpN02704PlusPointP002Center2577, ((2703320551278323549 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP002Input2577 8).2 : ℝ) =
      nodeExpN02704PlusPointP002Error2577 := by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP002Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP002Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02704PlusPointP002Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP002Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP003Input2577 : RatPair2542 := ((((-((75251 * 10^40
        + 1057389726409136056781964181355512754308) * 10^40
        + 182014849813444389447983162613849155677)) : ℚ) /
        ((415806 * 10^40
        + 9371244809296725772723606675176446357802) * 10^40
        + 447237920754980795911929244876800000000)),
    (((-54668031270047913913566379) : ℚ) /
        115292150460684697600000000))

def nodeExpN02704PlusPointP003Center2577 : RatPair2542 := ((((-2337165949435292114676855823) : ℚ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-10030301494560025509101554821) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

noncomputable def nodeExpN02704PlusPointP003Error2577 : ℝ := ((39308232611829201955562319 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP003BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP003Center2577‖ ≤ nodeExpN02704PlusPointP003Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP003Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP003Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP003Input2577 8 =
      (nodeExpN02704PlusPointP003Center2577, ((39308232611829201955562319 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP003Input2577 8).2 : ℝ) =
      nodeExpN02704PlusPointP003Error2577 := by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP003Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP003Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02704PlusPointP003Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP003Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP004Input2577 : RatPair2542 := ((((-((1314 * 10^40
        + 3793291039928624094795639072353193421464) * 10^40
        + 9080182155977962095085629655006240824151)) : ℚ) /
        ((8382 * 10^40
        + 7530312459026314251984141299542600038641) * 10^40
        + 5318978297451200742725530420838400000000)),
    ((54668031270047913913566379 : ℚ) /
        115292150460684697600000000))

def nodeExpN02704PlusPointP004Center2577 : RatPair2542 := ((((-2280774527693167736821574979679) :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((2447072292770089851661591621051 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

noncomputable def nodeExpN02704PlusPointP004Error2577 : ℝ := ((18721683894319600454709178461 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP004BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP004Center2577‖ ≤ nodeExpN02704PlusPointP004Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP004Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP004Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP004Input2577 8 =
      (nodeExpN02704PlusPointP004Center2577, ((18721683894319600454709178461 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP004Input2577 8).2 : ℝ) =
      nodeExpN02704PlusPointP004Error2577 := by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP004Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP004Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02704PlusPointP004Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP004Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP005Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02704PlusPointP005Error2577 : ℝ := 0

theorem nodeExpN02704PlusPointP005Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02704PlusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |nodeExpN02704PlusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02704PlusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem nodeExpN02704PlusPointP005BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP005Center2577‖ ≤ nodeExpN02704PlusPointP005Error2577
          := by
  rw [nodeExpN02704PlusPointP005Exterior2577]
  norm_num [nodeExpN02704PlusPointP005Center2577, nodeExpN02704PlusPointP005Error2577,
      nodeExpN02704PlusPointZero2577]

def nodeExpN02704PlusPointP006Input2577 : RatPair2542 := ((((-10703175194025607899013599449683) :
    ℚ) /
        17997946250671801739673600000000),
    ((0 : ℚ) /
        1))

def nodeExpN02704PlusPointP006Center2577 : RatPair2542 := (((638567541572489 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP006Error2577 : ℝ := ((2524797428367 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP006BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP006Center2577‖ ≤ nodeExpN02704PlusPointP006Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP006Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP006Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP006Input2577 7 =
      (nodeExpN02704PlusPointP006Center2577, ((2524797428367 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP006Input2577 7).2 : ℝ) =
      nodeExpN02704PlusPointP006Error2577 := by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP006Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP006Input2577 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          nodeExpN02704PlusPointP006Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP006Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP007Input2577 : RatPair2542 := ((((-((75251 * 10^40
        + 1057389726409136056781964181355512754308) * 10^40
        + 182014849813444389447983162613849155677)) : ℚ) /
        ((103951 * 10^40
        + 7342811202324181443180901668794111589450) * 10^40
        + 5111809480188745198977982311219200000000)),
    ((0 : ℚ) /
        1))

def nodeExpN02704PlusPointP007Center2577 : RatPair2542 := (((11065998679404049300331925531 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP007Error2577 : ℝ := ((803023130034719983008463 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeExpN02704PlusPointP007BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP007Center2577‖ ≤ nodeExpN02704PlusPointP007Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP007Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP007Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP007Input2577 6 =
      (nodeExpN02704PlusPointP007Center2577, ((803023130034719983008463 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP007Input2577 6).2 : ℝ) =
      nodeExpN02704PlusPointP007Error2577 := by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP007Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP007Input2577 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          nodeExpN02704PlusPointP007Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP007Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP008Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((39371688844277275851267847 : ℚ) /
        14757395258967641292800000000))

def nodeExpN02704PlusPointP008Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP008Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP008BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP008Center2577‖ ≤ nodeExpN02704PlusPointP008Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP008Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP008Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP008Input2577 14 =
      (nodeExpN02704PlusPointP008Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP008Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP008Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP008Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP008Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP008Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP008Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP009Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((58556016847187164876286361 : ℚ) /
        14757395258967641292800000000))

def nodeExpN02704PlusPointP009Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP009Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP009BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP009Center2577‖ ≤ nodeExpN02704PlusPointP009Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP009Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP009Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP009Input2577 14 =
      (nodeExpN02704PlusPointP009Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP009Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP009Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP009Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP009Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP009Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP009Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP010Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((34833351639308188388476671 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02704PlusPointP010Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP010Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP010BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP010Center2577‖ ≤ nodeExpN02704PlusPointP010Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP010Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP010Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP010Input2577 14 =
      (nodeExpN02704PlusPointP010Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP010Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP010Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP010Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP010Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP010Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP010Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP011Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((38537265293058906320467951 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02704PlusPointP011Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP011Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP011BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP011Center2577‖ ≤ nodeExpN02704PlusPointP011Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP011Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP011Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP011Input2577 14 =
      (nodeExpN02704PlusPointP011Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP011Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP011Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP011Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP011Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP011Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP011Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP012Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((847472267017150096839859 : ℚ) /
        147573952589676412928000000))

def nodeExpN02704PlusPointP012Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP012Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP012BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP012Center2577‖ ≤ nodeExpN02704PlusPointP012Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP012Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP012Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP012Input2577 14 =
      (nodeExpN02704PlusPointP012Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP012Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP012Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP012Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP012Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP012Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP012Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP013Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((9173924387612369119306941 : ℚ) /
        1475739525896764129280000000))

def nodeExpN02704PlusPointP013Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP013Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP013BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP013Center2577‖ ≤ nodeExpN02704PlusPointP013Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP013Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP013Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP013Input2577 14 =
      (nodeExpN02704PlusPointP013Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP013Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP013Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP013Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP013Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP013Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP013Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP014Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((52347367793712943072596661 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02704PlusPointP014Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP014Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP014BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP014Center2577‖ ≤ nodeExpN02704PlusPointP014Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP014Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP014Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP014Input2577 14 =
      (nodeExpN02704PlusPointP014Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP014Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP014Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP014Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP014Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP014Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP014Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP015Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((56988694746382884754536097 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02704PlusPointP015Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP015Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP015BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP015Center2577‖ ≤ nodeExpN02704PlusPointP015Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP015Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP015Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP015Input2577 14 =
      (nodeExpN02704PlusPointP015Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP015Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP015Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP015Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP015Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP015Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP015Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP016Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((30171440028794791767436959 : ℚ) /
        3689348814741910323200000000))

def nodeExpN02704PlusPointP016Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP016Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP016BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP016Center2577‖ ≤ nodeExpN02704PlusPointP016Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP016Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP016Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP016Input2577 14 =
      (nodeExpN02704PlusPointP016Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP016Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP016Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP016Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP016Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP016Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP016Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP017Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((66858175325789869447510077 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02704PlusPointP017Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP017Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP017BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP017Center2577‖ ≤ nodeExpN02704PlusPointP017Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP017Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP017Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP017Input2577 14 =
      (nodeExpN02704PlusPointP017Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP017Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP017Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP017Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP017Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP017Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP017Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP018Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((17330367457162959994191563 : ℚ) /
        1844674407370955161600000000))

def nodeExpN02704PlusPointP018Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP018Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP018BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP018Center2577‖ ≤ nodeExpN02704PlusPointP018Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP018Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP018Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP018Input2577 14 =
      (nodeExpN02704PlusPointP018Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP018Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP018Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP018Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP018Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP018Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP018Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP019Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((3688665669635304979192041 : ℚ) /
        368934881474191032320000000))

def nodeExpN02704PlusPointP019Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP019Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP019BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP019Center2577‖ ≤ nodeExpN02704PlusPointP019Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP019Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP019Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP019Input2577 14 =
      (nodeExpN02704PlusPointP019Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP019Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP019Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP019Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP019Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP019Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP019Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP020Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((78614337331324960832264269 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02704PlusPointP020Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP020Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP020BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP020Center2577‖ ≤ nodeExpN02704PlusPointP020Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP020Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP020Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP020Input2577 14 =
      (nodeExpN02704PlusPointP020Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP020Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP020Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP020Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP020Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP020Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP020Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP021Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((82654361045867903481379437 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02704PlusPointP021Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP021Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP021BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP021Center2577‖ ≤ nodeExpN02704PlusPointP021Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP021Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP021Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP021Input2577 14 =
      (nodeExpN02704PlusPointP021Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP021Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP021Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP021Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP021Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP021Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP021Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP022Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((16944438833431689477671183 : ℚ) /
        1475739525896764129280000000))

def nodeExpN02704PlusPointP022Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP022Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP022BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP022Center2577‖ ≤ nodeExpN02704PlusPointP022Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP022Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP022Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP022Input2577 14 =
      (nodeExpN02704PlusPointP022Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP022Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP022Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP022Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP022Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP022Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP022Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP023Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((45342070652492160469014283 : ℚ) /
        3689348814741910323200000000))

def nodeExpN02704PlusPointP023Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP023Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP023BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP023Center2577‖ ≤ nodeExpN02704PlusPointP023Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP023Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP023Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP023Input2577 14 =
      (nodeExpN02704PlusPointP023Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP023Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP023Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP023Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP023Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP023Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP023Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP024Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((46712005387750232020650197 : ℚ) /
        3689348814741910323200000000))

def nodeExpN02704PlusPointP024Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP024Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP024BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP024Center2577‖ ≤ nodeExpN02704PlusPointP024Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP024Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP024Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP024Input2577 14 =
      (nodeExpN02704PlusPointP024Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP024Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP024Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP024Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP024Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP024Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP024Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP025Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((1513426630246391746815783 : ℚ) /
        115292150460684697600000000))

def nodeExpN02704PlusPointP025Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP025Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP025BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP025Center2577‖ ≤ nodeExpN02704PlusPointP025Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP025Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP025Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP025Input2577 14 =
      (nodeExpN02704PlusPointP025Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP025Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP025Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP025Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP025Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP025Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP025Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP026Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((3136563586529957941722987 : ℚ) /
        230584300921369395200000000))

def nodeExpN02704PlusPointP026Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP026Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP026BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP026Center2577‖ ≤ nodeExpN02704PlusPointP026Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP026Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP026Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP026Input2577 14 =
      (nodeExpN02704PlusPointP026Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP026Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP026Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP026Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP026Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP026Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP026Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP027Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((6589758326498808710472677 : ℚ) /
        461168601842738790400000000))

def nodeExpN02704PlusPointP027Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP027Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP027BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP027Center2577‖ ≤ nodeExpN02704PlusPointP027Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP027Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP027Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP027Input2577 14 =
      (nodeExpN02704PlusPointP027Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP027Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP027Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP027Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP027Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP027Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP027Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP028Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((26860467825486442936697777 : ℚ) /
        1844674407370955161600000000))

def nodeExpN02704PlusPointP028Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP028Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP028BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP028Center2577‖ ≤ nodeExpN02704PlusPointP028Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP028Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP028Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP028Input2577 14 =
      (nodeExpN02704PlusPointP028Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP028Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP028Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP028Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP028Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP028Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP028Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704PlusPointP029Input2577 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((27623869687037674802636509 : ℚ) /
        1844674407370955161600000000))

def nodeExpN02704PlusPointP029Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704PlusPointP029Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704PlusPointP029BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeExpN02704PlusPointPosition2577 -
      embedPair2542 nodeExpN02704PlusPointP029Center2577‖ ≤ nodeExpN02704PlusPointP029Error2577
          := by
  have hx : |nodeExpN02704PlusPointPosition2577| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704PlusPointP029Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704PlusPointP029Input2577]
  have hs : compactExp2547 nodeExpN02704PlusPointP029Input2577 14 =
      (nodeExpN02704PlusPointP029Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704PlusPointP029Input2577 14).2 : ℝ) =
      nodeExpN02704PlusPointP029Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704PlusPointP029Error2577]
  have h := compactExp_error2547 nodeExpN02704PlusPointP029Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      nodeExpN02704PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704PlusPointP029Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704PlusPointP029Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem nodeExpN02704PlusPointGrid2577 :
    -stripRadius2303 + (2704 : ℝ) * (2 * stripRadius2303 / 10240) =
      nodeExpN02704PlusPointPosition2577 := by
  norm_num [stripRadius2303, nodeExpN02704PlusPointPosition2577]

end ConnesWeilRH.Dev
