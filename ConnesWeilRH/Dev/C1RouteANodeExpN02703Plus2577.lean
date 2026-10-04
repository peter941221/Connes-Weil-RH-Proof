import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def nodeExpN02703PlusPointPosition2577 : ℝ := (((-158400514417) : ℝ) /
        51200000000)

theorem nodeExpN02703PlusPointZero2577 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def nodeExpN02703PlusPointP000Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02703PlusPointP000Error2577 : ℝ := 0

theorem nodeExpN02703PlusPointP000Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02703PlusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |nodeExpN02703PlusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02703PlusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem nodeExpN02703PlusPointP000BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP000Center2577‖ ≤ nodeExpN02703PlusPointP000Error2577
          := by
  rw [nodeExpN02703PlusPointP000Exterior2577]
  norm_num [nodeExpN02703PlusPointP000Center2577, nodeExpN02703PlusPointP000Error2577,
      nodeExpN02703PlusPointZero2577]

def nodeExpN02703PlusPointP001Input2577 : RatPair2542 := ((((-((340 * 10^40
        + 1342439253873258425104217711532251719251) * 10^40
        + 716821260981140458137600388969873699153)) : ℚ) /
        ((949 * 10^40
        + 5678772037045116961918709892218078778647) * 10^40
        + 478078034072945845341163828019200000000)),
    ((875050540262952370391324093 : ℚ) /
        3689348814741910323200000000))

def nodeExpN02703PlusPointP001Center2577 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP001Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP001BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP001Center2577‖ ≤ nodeExpN02703PlusPointP001Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP001Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP001Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP001Input2577 9 =
      (nodeExpN02703PlusPointP001Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP001Input2577 9).2 : ℝ) =
      nodeExpN02703PlusPointP001Error2577 := by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP001Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP001Input2577 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          nodeExpN02703PlusPointP001Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP001Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP002Input2577 : RatPair2542 := ((((-((9034 * 10^40
        + 121958995836850665082431815495461739324) * 10^40
        + 1151769464373665887696246711951817077073)) : ℚ) /
        ((36744 * 10^40
        + 1879937388438218950297983988018634857015) * 10^40
        + 2724428396649426762729310624153600000000)),
    (((-875050540262952370391324093) : ℚ) /
        1844674407370955161600000000))

def nodeExpN02703PlusPointP002Center2577 : RatPair2542 := ((((-315978186676346367273) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-298827836871563509461) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

noncomputable def nodeExpN02703PlusPointP002Error2577 : ℝ := ((2549234199278350865 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP002BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP002Center2577‖ ≤ nodeExpN02703PlusPointP002Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP002Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP002Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP002Input2577 8 =
      (nodeExpN02703PlusPointP002Center2577, ((2549234199278350865 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP002Input2577 8).2 : ℝ) =
      nodeExpN02703PlusPointP002Error2577 := by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP002Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP002Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02703PlusPointP002Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP002Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP003Input2577 : RatPair2542 := ((((-((1204017 * 10^40
        + 9215552606038699152080738473326018463805) * 10^40
        + 4034063249232261059340317651547326123771)) : ℚ) /
        ((6650196 * 10^40
        + 4642788052740272456750226203440576329812) * 10^40
        + 5806699242230935752901173261107200000000)),
    (((-875050540262952370391324093) : ℚ) /
        1844674407370955161600000000))

def nodeExpN02703PlusPointP003Center2577 : RatPair2542 := ((((-1268809181176912783519253083) : ℚ)
    /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-9599536145252764711420508941) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

noncomputable def nodeExpN02703PlusPointP003Error2577 : ℝ := ((19188053210732762782261105 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeExpN02703PlusPointP003BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP003Center2577‖ ≤ nodeExpN02703PlusPointP003Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP003Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP003Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP003Input2577 8 =
      (nodeExpN02703PlusPointP003Center2577, ((19188053210732762782261105 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP003Input2577 8).2 : ℝ) =
      nodeExpN02703PlusPointP003Error2577 := by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP003Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP003Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02703PlusPointP003Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP003Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP004Input2577 : RatPair2542 := ((((-((21030 * 10^40
        + 2123584538409079574289961932172921746148) * 10^40
        + 9702161488119280594243368562537754577073)) : ℚ) /
        ((134092 * 10^40
        + 2376048615170942017213126254407586180041) * 10^40
        + 6181592905822546762729310624153600000000)),
    ((875050540262952370391324093 : ℚ) /
        1844674407370955161600000000))

def nodeExpN02703PlusPointP004Center2577 : RatPair2542 := ((((-312386221358806970386657117599) :
    ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((2363446661405167442454675371511 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

noncomputable def nodeExpN02703PlusPointP004Error2577 : ℝ := ((288197090536147820321281271 : ℝ) /
        (2510840694154672305 * 10^40
        + 5343157692830665664409421777856138051584))

theorem nodeExpN02703PlusPointP004BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP004Center2577‖ ≤ nodeExpN02703PlusPointP004Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP004Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP004Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP004Input2577 8 =
      (nodeExpN02703PlusPointP004Center2577, ((288197090536147820321281271 : ℚ) /
        (2510840694154672305 * 10^40
        + 5343157692830665664409421777856138051584))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP004Input2577 8).2 : ℝ) =
      nodeExpN02703PlusPointP004Error2577 := by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP004Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP004Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02703PlusPointP004Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP004Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP005Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02703PlusPointP005Error2577 : ℝ := 0

theorem nodeExpN02703PlusPointP005Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02703PlusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |nodeExpN02703PlusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02703PlusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem nodeExpN02703PlusPointP005BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP005Center2577‖ ≤ nodeExpN02703PlusPointP005Error2577
          := by
  rw [nodeExpN02703PlusPointP005Exterior2577]
  norm_num [nodeExpN02703PlusPointP005Center2577, nodeExpN02703PlusPointP005Error2577,
      nodeExpN02703PlusPointZero2577]

def nodeExpN02703PlusPointP006Input2577 : RatPair2542 :=
    ((((-43839478189018415751735075264883429) : ℚ) /
        73628896602487849615844966400000000),
    ((0 : ℚ) /
        1))

def nodeExpN02703PlusPointP006Center2577 : RatPair2542 := (((582152360891653 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP006Error2577 : ℝ := ((2496231124509 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP006BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP006Center2577‖ ≤ nodeExpN02703PlusPointP006Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP006Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP006Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP006Input2577 7 =
      (nodeExpN02703PlusPointP006Center2577, ((2496231124509 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP006Input2577 7).2 : ℝ) =
      nodeExpN02703PlusPointP006Error2577 := by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP006Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP006Input2577 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          nodeExpN02703PlusPointP006Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP006Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP007Input2577 : RatPair2542 := ((((-((1204017 * 10^40
        + 9215552606038699152080738473326018463805) * 10^40
        + 4034063249232261059340317651547326123771)) : ℚ) /
        ((1662549 * 10^40
        + 1160697013185068114187556550860144082453) * 10^40
        + 1451674810557733938225293315276800000000)),
    ((0 : ℚ) /
        1))

def nodeExpN02703PlusPointP007Center2577 : RatPair2542 := (((5429298343613002153233162827 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP007Error2577 : ℝ := ((1576411260228435144735031 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP007BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP007Center2577‖ ≤ nodeExpN02703PlusPointP007Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP007Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP007Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP007Input2577 6 =
      (nodeExpN02703PlusPointP007Center2577, ((1576411260228435144735031 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP007Input2577 6).2 : ℝ) =
      nodeExpN02703PlusPointP007Error2577 := by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP007Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP007Input2577 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          nodeExpN02703PlusPointP007Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP007Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP008Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((630207761169656792930558849 : ℚ) /
        236118324143482260684800000000))

def nodeExpN02703PlusPointP008Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP008Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP008BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP008Center2577‖ ≤ nodeExpN02703PlusPointP008Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP008Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP008Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP008Input2577 14 =
      (nodeExpN02703PlusPointP008Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP008Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP008Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP008Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP008Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP008Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP008Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP009Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((937284057746035612622411487 : ℚ) /
        236118324143482260684800000000))

def nodeExpN02703PlusPointP009Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP009Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP009BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP009Center2577‖ ≤ nodeExpN02703PlusPointP009Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP009Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP009Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP009Input2577 14 =
      (nodeExpN02703PlusPointP009Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP009Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP009Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP009Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP009Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP009Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP009Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP010Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((557564310676873452549325257 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02703PlusPointP010Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP010Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP010BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP010Center2577‖ ≤ nodeExpN02703PlusPointP010Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP010Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP010Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP010Input2577 14 =
      (nodeExpN02703PlusPointP010Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP010Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP010Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP010Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP010Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP010Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP010Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP011Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((616851458366379977328285017 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02703PlusPointP011Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP011Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP011BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP011Center2577‖ ≤ nodeExpN02703PlusPointP011Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP011Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP011Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP011Input2577 14 =
      (nodeExpN02703PlusPointP011Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP011Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP011Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP011Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP011Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP011Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP011Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP012Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((13565168671393720424251253 : ℚ) /
        2361183241434822606848000000))

def nodeExpN02703PlusPointP012Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP012Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP012BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP012Center2577‖ ≤ nodeExpN02703PlusPointP012Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP012Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP012Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP012Input2577 14 =
      (nodeExpN02703PlusPointP012Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP012Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP012Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP012Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP012Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP012Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP012Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP013Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((146843544667941034181224347 : ℚ) /
        23611832414348226068480000000))

def nodeExpN02703PlusPointP013Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP013Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP013BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP013Center2577‖ ≤ nodeExpN02703PlusPointP013Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP013Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP013Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP013Input2577 14 =
      (nodeExpN02703PlusPointP013Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP013Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP013Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP013Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP013Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP013Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP013Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP014Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((837904556009299227857391587 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02703PlusPointP014Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP014Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP014BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP014Center2577‖ ≤ nodeExpN02703PlusPointP014Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP014Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP014Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP014Input2577 14 =
      (nodeExpN02703PlusPointP014Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP014Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP014Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP014Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP014Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP014Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP014Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP015Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((912196524516605512925256599 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02703PlusPointP015Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP015Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP015BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP015Center2577‖ ≤ nodeExpN02703PlusPointP015Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP015Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP015Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP015Input2577 14 =
      (nodeExpN02703PlusPointP015Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP015Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP015Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP015Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP015Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP015Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP015Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP016Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((482942851321834514582086953 : ℚ) /
        59029581035870565171200000000))

def nodeExpN02703PlusPointP016Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP016Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP016BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP016Center2577‖ ≤ nodeExpN02703PlusPointP016Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP016Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP016Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP016Input2577 14 =
      (nodeExpN02703PlusPointP016Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP016Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP016Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP016Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP016Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP016Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP016Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP017Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((1070173574585656387116767259 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02703PlusPointP017Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP017Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP017BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP017Center2577‖ ≤ nodeExpN02703PlusPointP017Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP017Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP017Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP017Input2577 14 =
      (nodeExpN02703PlusPointP017Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP017Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP017Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP017Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP017Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP017Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP017Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP018Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((277400649960019035138814621 : ℚ) /
        29514790517935282585600000000))

def nodeExpN02703PlusPointP018Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP018Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP018BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP018Center2577‖ ≤ nodeExpN02703PlusPointP018Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP018Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP018Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP018Input2577 14 =
      (nodeExpN02703PlusPointP018Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP018Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP018Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP018Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP018Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP018Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP018Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP019Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((59043078963632663143756047 : ℚ) /
        5902958103587056517120000000))

def nodeExpN02703PlusPointP019Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP019Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP019BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP019Center2577‖ ≤ nodeExpN02703PlusPointP019Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP019Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP019Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP019Input2577 14 =
      (nodeExpN02703PlusPointP019Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP019Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP019Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP019Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP019Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP019Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP019Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP020Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((1258350022051737949215779723 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02703PlusPointP020Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP020Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP020BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP020Center2577‖ ≤ nodeExpN02703PlusPointP020Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP020Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP020Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP020Input2577 14 =
      (nodeExpN02703PlusPointP020Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP020Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP020Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP020Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP020Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP020Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP020Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP021Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((1323017156608362402082742379 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02703PlusPointP021Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP021Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP021BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP021Center2577‖ ≤ nodeExpN02703PlusPointP021Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP021Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP021Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP021Input2577 14 =
      (nodeExpN02703PlusPointP021Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP021Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP021Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP021Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP021Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP021Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP021Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP022Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((271223236161618499784975161 : ℚ) /
        23611832414348226068480000000))

def nodeExpN02703PlusPointP022Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP022Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP022BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP022Center2577‖ ≤ nodeExpN02703PlusPointP022Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP022Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP022Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP022Input2577 14 =
      (nodeExpN02703PlusPointP022Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP022Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP022Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP022Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP022Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP022Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP022Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP023Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((725773409053467230818592861 : ℚ) /
        59029581035870565171200000000))

def nodeExpN02703PlusPointP023Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP023Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP023BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP023Center2577‖ ≤ nodeExpN02703PlusPointP023Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP023Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP023Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP023Input2577 14 =
      (nodeExpN02703PlusPointP023Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP023Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP023Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP023Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP023Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP023Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP023Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP024Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((747701437233061660886831299 : ℚ) /
        59029581035870565171200000000))

def nodeExpN02703PlusPointP024Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP024Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP024BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP024Center2577‖ ≤ nodeExpN02703PlusPointP024Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP024Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP024Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP024Input2577 14 =
      (nodeExpN02703PlusPointP024Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP024Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP024Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP024Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP024Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP024Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP024Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP025Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((24224848776857806967243361 : ℚ) /
        1844674407370955161600000000))

def nodeExpN02703PlusPointP025Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP025Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP025BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP025Center2577‖ ≤ nodeExpN02703PlusPointP025Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP025Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP025Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP025Input2577 14 =
      (nodeExpN02703PlusPointP025Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP025Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP025Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP025Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP025Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP025Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP025Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP026Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((50205789328760982418175229 : ℚ) /
        3689348814741910323200000000))

def nodeExpN02703PlusPointP026Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP026Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP026BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP026Center2577‖ ≤ nodeExpN02703PlusPointP026Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP026Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP026Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP026Input2577 14 =
      (nodeExpN02703PlusPointP026Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP026Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP026Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP026Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP026Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP026Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP026Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP027Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((105479774007600136776241459 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02703PlusPointP027Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP027Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP027BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP027Center2577‖ ≤ nodeExpN02703PlusPointP027Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP027Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP027Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP027Input2577 14 =
      (nodeExpN02703PlusPointP027Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP027Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP027Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP027Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP027Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP027Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP027Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP028Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((429945369100667103165553159 : ℚ) /
        29514790517935282585600000000))

def nodeExpN02703PlusPointP028Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP028Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP028BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP028Center2577‖ ≤ nodeExpN02703PlusPointP028Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP028Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP028Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP028Input2577 14 =
      (nodeExpN02703PlusPointP028Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP028Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP028Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP028Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP028Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP028Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP028Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703PlusPointP029Input2577 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((442164854526954039721671803 : ℚ) /
        29514790517935282585600000000))

def nodeExpN02703PlusPointP029Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703PlusPointP029Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703PlusPointP029BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeExpN02703PlusPointPosition2577 -
      embedPair2542 nodeExpN02703PlusPointP029Center2577‖ ≤ nodeExpN02703PlusPointP029Error2577
          := by
  have hx : |nodeExpN02703PlusPointPosition2577| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703PlusPointP029Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703PlusPointP029Input2577]
  have hs : compactExp2547 nodeExpN02703PlusPointP029Input2577 14 =
      (nodeExpN02703PlusPointP029Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703PlusPointP029Input2577 14).2 : ℝ) =
      nodeExpN02703PlusPointP029Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703PlusPointP029Error2577]
  have h := compactExp_error2547 nodeExpN02703PlusPointP029Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      nodeExpN02703PlusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703PlusPointP029Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703PlusPointP029Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem nodeExpN02703PlusPointGrid2577 :
    -stripRadius2303 + (2703 : ℝ) * (2 * stripRadius2303 / 10240) =
      nodeExpN02703PlusPointPosition2577 := by
  norm_num [stripRadius2303, nodeExpN02703PlusPointPosition2577]

end ConnesWeilRH.Dev
