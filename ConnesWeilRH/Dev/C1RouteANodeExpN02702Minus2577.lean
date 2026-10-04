import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def nodeExpN02702MinusPointPosition2577 : ℝ := (((-79233025209) : ℝ) /
        25600000000)

theorem nodeExpN02702MinusPointZero2577 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def nodeExpN02702MinusPointP000Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02702MinusPointP000Error2577 : ℝ := 0

theorem nodeExpN02702MinusPointP000Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02702MinusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |nodeExpN02702MinusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02702MinusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem nodeExpN02702MinusPointP000BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP000Center2577‖ ≤
          nodeExpN02702MinusPointP000Error2577 := by
  rw [nodeExpN02702MinusPointP000Exterior2577]
  norm_num [nodeExpN02702MinusPointP000Center2577, nodeExpN02702MinusPointP000Error2577,
      nodeExpN02702MinusPointZero2577]

def nodeExpN02702MinusPointP001Input2577 : RatPair2542 := ((((-((18 * 10^40
        + 5781842504157709083773797513449382919147) * 10^40
        + 7891878721064052424381933342951022830831)) : ℚ) /
        ((52 * 10^40
        + 5327705452767415333723241392768703787170) * 10^40
        + 3821134574968135018370261083750400000000)),
    ((437706290102569059082793061 : ℚ) /
        1844674407370955161600000000))

def nodeExpN02702MinusPointP001Center2577 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP001Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP001BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP001Center2577‖ ≤
          nodeExpN02702MinusPointP001Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP001Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP001Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP001Input2577 9 =
      (nodeExpN02702MinusPointP001Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP001Input2577 9).2 : ℝ) =
      nodeExpN02702MinusPointP001Error2577 := by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP001Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP001Input2577 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          nodeExpN02702MinusPointP001Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP001Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP002Input2577 : RatPair2542 := ((((-((477 * 10^40
        + 2255107326888302176340661150205602907439) * 10^40
        + 5476330259514208027845595586673152402671)) : ℚ) /
        ((2039 * 10^40
        + 5757741460588060628394170300498186110020) * 10^40
        + 7730176828859850146962088670003200000000)),
    (((-437706290102569059082793061) : ℚ) /
        922337203685477580800000000))

def nodeExpN02702MinusPointP002Center2577 : RatPair2542 := ((((-1808320510932834055125) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-3040243993904768592253) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

noncomputable def nodeExpN02702MinusPointP002Error2577 : ℝ := ((26203547001217881765 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeExpN02702MinusPointP002BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP002Center2577‖ ≤
          nodeExpN02702MinusPointP002Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP002Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP002Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP002Input2577 8 =
      (nodeExpN02702MinusPointP002Center2577, ((26203547001217881765 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP002Input2577 8).2 : ℝ) =
      nodeExpN02702MinusPointP002Error2577 := by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP002Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP002Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02702MinusPointP002Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP002Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP003Input2577 : RatPair2542 := ((((-((9973 * 10^40
        + 2256215055554662430951253447146088309355) * 10^40
        + 5495472998434125712497953547040931958511)) : ℚ) /
        ((59001 * 10^40
        + 3089754565407751898622199770334889942512) * 10^40
        + 5741483004646831459175457370931200000000)),
    (((-437706290102569059082793061) : ℚ) /
        922337203685477580800000000))

def nodeExpN02702MinusPointP003Center2577 : RatPair2542 := ((((-120309152640455605580363375995) :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-202270104506104807991901408963) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

noncomputable def nodeExpN02702MinusPointP003Error2577 : ℝ := ((408428881659359733954910165 : ℝ)
    /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeExpN02702MinusPointP003BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP003Center2577‖ ≤
          nodeExpN02702MinusPointP003Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP003Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP003Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP003Input2577 8 =
      (nodeExpN02702MinusPointP003Center2577, ((408428881659359733954910165 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP003Input2577 8).2 : ℝ) =
      nodeExpN02702MinusPointP003Error2577 := by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP003Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP003Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02702MinusPointP003Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP003Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP004Input2577 : RatPair2542 := ((((-((1078 * 10^40
        + 3091548951820516196409849396445654228081) * 10^40
        + 7733082618942795786190859673587214902671)) : ℚ) /
        ((7447 * 10^40
        + 8007525417628767465445011537519794516855) * 10^40
        + 5700019301591690146962088670003200000000)),
    ((437706290102569059082793061 : ℚ) /
        922337203685477580800000000))

def nodeExpN02702MinusPointP004Center2577 : RatPair2542 := ((((-29892566899523530686861247311731)
    : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((100513925965249929978375590473809 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

noncomputable def nodeExpN02702MinusPointP004Error2577 : ℝ := ((198097311830982059347853453109 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeExpN02702MinusPointP004BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP004Center2577‖ ≤
          nodeExpN02702MinusPointP004Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP004Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP004Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP004Input2577 8 =
      (nodeExpN02702MinusPointP004Center2577, ((198097311830982059347853453109 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP004Input2577 8).2 : ℝ) =
      nodeExpN02702MinusPointP004Error2577 := by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP004Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP004Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02702MinusPointP004Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP004Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP005Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02702MinusPointP005Error2577 : ℝ := 0

theorem nodeExpN02702MinusPointP005Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02702MinusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |nodeExpN02702MinusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02702MinusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem nodeExpN02702MinusPointP005BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP005Center2577‖ ≤
          nodeExpN02702MinusPointP005Error2577 := by
  rw [nodeExpN02702MinusPointP005Exterior2577]
  norm_num [nodeExpN02702MinusPointP005Center2577, nodeExpN02702MinusPointP005Error2577,
      nodeExpN02702MinusPointZero2577]

def nodeExpN02702MinusPointP006Input2577 : RatPair2542 :=
    ((((-15772723686503309308431500179204329) : ℚ) /
        27576812937084734710212198400000000),
    ((0 : ℚ) /
        1))

def nodeExpN02702MinusPointP006Center2577 : RatPair2542 := (((11719533816037623 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP006Error2577 : ℝ := ((4021762308289 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeExpN02702MinusPointP006BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP006Center2577‖ ≤
          nodeExpN02702MinusPointP006Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP006Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP006Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP006Input2577 7 =
      (nodeExpN02702MinusPointP006Center2577, ((4021762308289 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP006Input2577 7).2 : ℝ) =
      nodeExpN02702MinusPointP006Error2577 := by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP006Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP006Input2577 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          nodeExpN02702MinusPointP006Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP006Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP007Input2577 : RatPair2542 := ((((-((9973 * 10^40
        + 2256215055554662430951253447146088309355) * 10^40
        + 5495472998434125712497953547040931958511)) : ℚ) /
        ((14750 * 10^40
        + 3272438641351937974655549942583722485628) * 10^40
        + 1435370751161707864793864342732800000000)),
    ((0 : ℚ) /
        1))

def nodeExpN02702MinusPointP007Center2577 : RatPair2542 := (((117672731958146325856108455551 : ℚ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP007Error2577 : ℝ := ((16281624050426687031899557 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeExpN02702MinusPointP007BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP007Center2577‖ ≤
          nodeExpN02702MinusPointP007Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP007Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP007Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP007Input2577 6 =
      (nodeExpN02702MinusPointP007Center2577, ((16281624050426687031899557 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP007Input2577 6).2 : ℝ) =
      nodeExpN02702MinusPointP007Error2577 := by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP007Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP007Input2577 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          nodeExpN02702MinusPointP007Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP007Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP008Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((315234250415438586120416073 : ℚ) /
        236118324143482260684800000000))

def nodeExpN02702MinusPointP008Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP008Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP008BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP008Center2577‖ ≤
          nodeExpN02702MinusPointP008Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP008Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP008Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP008Input2577 15 =
      (nodeExpN02702MinusPointP008Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP008Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP008Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP008Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP008Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP008Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP008Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP009Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((468835922968538293612120599 : ℚ) /
        236118324143482260684800000000))

def nodeExpN02702MinusPointP009Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP009Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP009BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP009Center2577‖ ≤
          nodeExpN02702MinusPointP009Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP009Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP009Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP009Input2577 15 =
      (nodeExpN02702MinusPointP009Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP009Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP009Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP009Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP009Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP009Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP009Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP010Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((278897497562407945441511889 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02702MinusPointP010Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP010Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP010BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP010Center2577‖ ≤
          nodeExpN02702MinusPointP010Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP010Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP010Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP010Input2577 15 =
      (nodeExpN02702MinusPointP010Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP010Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP010Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP010Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP010Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP010Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP010Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP011Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((308553336021908726764541409 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02702MinusPointP011Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP011Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP011BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP011Center2577‖ ≤
          nodeExpN02702MinusPointP011Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP011Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP011Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP011Input2577 15 =
      (nodeExpN02702MinusPointP011Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP011Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP011Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP011Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP011Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP011Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP011Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP012Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((6785390535256519649532381 : ℚ) /
        2361183241434822606848000000))

def nodeExpN02702MinusPointP012Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP012Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP012BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP012Center2577‖ ≤
          nodeExpN02702MinusPointP012Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP012Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP012Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP012Input2577 15 =
      (nodeExpN02702MinusPointP012Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP012Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP012Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP012Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP012Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP012Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP012Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP013Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((73452149567042081226768819 : ℚ) /
        23611832414348226068480000000))

def nodeExpN02702MinusPointP013Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP013Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP013BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP013Center2577‖ ≤
          nodeExpN02702MinusPointP013Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP013Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP013Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP013Input2577 15 =
      (nodeExpN02702MinusPointP013Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP013Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP013Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP013Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP013Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP013Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP013Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP014Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((419125613659595683276618299 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02702MinusPointP014Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP014Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP014BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP014Center2577‖ ≤
          nodeExpN02702MinusPointP014Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP014Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP014Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP014Input2577 15 =
      (nodeExpN02702MinusPointP014Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP014Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP014Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP014Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP014Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP014Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP014Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP015Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((456286966545542434888967823 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02702MinusPointP015Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP015Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP015BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP015Center2577‖ ≤
          nodeExpN02702MinusPointP015Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP015Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP015Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP015Input2577 15 =
      (nodeExpN02702MinusPointP015Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP015Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP015Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP015Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP015Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP015Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP015Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP016Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((241571331091476180442591281 : ℚ) /
        59029581035870565171200000000))

def nodeExpN02702MinusPointP016Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP016Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP016BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP016Center2577‖ ≤
          nodeExpN02702MinusPointP016Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP016Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP016Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP016Input2577 15 =
      (nodeExpN02702MinusPointP016Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP016Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP016Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP016Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP016Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP016Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP016Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP017Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((535308171979337431536686643 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02702MinusPointP017Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP017Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP017BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP017Center2577‖ ≤
          nodeExpN02702MinusPointP017Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP017Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP017Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP017Input2577 15 =
      (nodeExpN02702MinusPointP017Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP017Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP017Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP017Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP017Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP017Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP017Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP018Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((138757710302715355185282117 : ℚ) /
        29514790517935282585600000000))

def nodeExpN02702MinusPointP018Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP018Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP018BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP018Center2577‖ ≤
          nodeExpN02702MinusPointP018Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP018Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP018Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP018Input2577 15 =
      (nodeExpN02702MinusPointP018Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP018Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP018Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP018Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP018Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP018Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP018Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP019Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((29533753606550223310219719 : ℚ) /
        5902958103587056517120000000))

def nodeExpN02702MinusPointP019Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP019Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP019BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP019Center2577‖ ≤
          nodeExpN02702MinusPointP019Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP019Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP019Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP019Input2577 15 =
      (nodeExpN02702MinusPointP019Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP019Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP019Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP019Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP019Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP019Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP019Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP020Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((629435323401138262557665571 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02702MinusPointP020Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP020Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP020BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP020Center2577‖ ≤
          nodeExpN02702MinusPointP020Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP020Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP020Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP020Input2577 15 =
      (nodeExpN02702MinusPointP020Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP020Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP020Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP020Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP020Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP020Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP020Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP021Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((661782268241419174231706883 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02702MinusPointP021Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP021Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP021BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP021Center2577‖ ≤
          nodeExpN02702MinusPointP021Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP021Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP021Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP021Input2577 15 =
      (nodeExpN02702MinusPointP021Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP021Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP021Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP021Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP021Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP021Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP021Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP022Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((135667725494164983963605697 : ℚ) /
        23611832414348226068480000000))

def nodeExpN02702MinusPointP022Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP022Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP022BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP022Center2577‖ ≤
          nodeExpN02702MinusPointP022Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP022Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP022Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP022Input2577 15 =
      (nodeExpN02702MinusPointP022Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP022Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP022Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP022Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP022Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP022Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP022Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP023Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((363036843833529947066478597 : ℚ) /
        59029581035870565171200000000))

def nodeExpN02702MinusPointP023Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP023Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP023BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP023Center2577‖ ≤
          nodeExpN02702MinusPointP023Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP023Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP023Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP023Input2577 15 =
      (nodeExpN02702MinusPointP023Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP023Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP023Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP023Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP023Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP023Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP023Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP024Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((374005394131059804721629723 : ℚ) /
        59029581035870565171200000000))

def nodeExpN02702MinusPointP024Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP024Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP024BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP024Center2577‖ ≤
          nodeExpN02702MinusPointP024Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP024Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP024Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP024Input2577 15 =
      (nodeExpN02702MinusPointP024Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP024Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP024Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP024Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP024Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP024Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP024Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP025Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((12117435734886672992717097 : ℚ) /
        1844674407370955161600000000))

def nodeExpN02702MinusPointP025Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP025Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP025BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP025Center2577‖ ≤
          nodeExpN02702MinusPointP025Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP025Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP025Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP025Input2577 15 =
      (nodeExpN02702MinusPointP025Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP025Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP025Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP025Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP025Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP025Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP025Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP026Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((25113280636521318884391333 : ℚ) /
        3689348814741910323200000000))

def nodeExpN02702MinusPointP026Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP026Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP026BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP026Center2577‖ ≤
          nodeExpN02702MinusPointP026Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP026Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP026Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP026Input2577 15 =
      (nodeExpN02702MinusPointP026Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP026Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP026Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP026Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP026Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP026Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP026Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP027Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((52761707395609667092460043 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02702MinusPointP027Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP027Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP027BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP027Center2577‖ ≤
          nodeExpN02702MinusPointP027Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP027Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP027Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP027Input2577 15 =
      (nodeExpN02702MinusPointP027Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP027Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP027Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP027Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP027Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP027Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP027Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP028Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((215061626496775559671970943 : ℚ) /
        29514790517935282585600000000))

def nodeExpN02702MinusPointP028Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP028Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP028BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP028Center2577‖ ≤
          nodeExpN02702MinusPointP028Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP028Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP028Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP028Input2577 15 =
      (nodeExpN02702MinusPointP028Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP028Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP028Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP028Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP028Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP028Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP028Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702MinusPointP029Input2577 : RatPair2542 := ((((-((578154 * 10^40
        + 6953538535139781891480462516901598321515) * 10^40
        + 9047419746790429937938596620327657238359)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((221173897030652641300579731 : ℚ) /
        29514790517935282585600000000))

def nodeExpN02702MinusPointP029Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702MinusPointP029Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702MinusPointP029BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeExpN02702MinusPointPosition2577 -
      embedPair2542 nodeExpN02702MinusPointP029Center2577‖ ≤
          nodeExpN02702MinusPointP029Error2577 := by
  have hx : |nodeExpN02702MinusPointPosition2577| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702MinusPointP029Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702MinusPointP029Input2577]
  have hs : compactExp2547 nodeExpN02702MinusPointP029Input2577 15 =
      (nodeExpN02702MinusPointP029Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702MinusPointP029Input2577 15).2 : ℝ) =
      nodeExpN02702MinusPointP029Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702MinusPointP029Error2577]
  have h := compactExp_error2547 nodeExpN02702MinusPointP029Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      nodeExpN02702MinusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702MinusPointP029Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702MinusPointP029Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem nodeExpN02702MinusPointGrid2577 :
    -stripRadius2303 + (2702 : ℝ) * (2 * stripRadius2303 / 10240) =
      nodeExpN02702MinusPointPosition2577 := by
  norm_num [stripRadius2303, nodeExpN02702MinusPointPosition2577]

end ConnesWeilRH.Dev
