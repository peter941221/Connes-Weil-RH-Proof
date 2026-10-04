import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def nodeExpN02702PlusPointPosition2577 : ℝ := (((-79233025209) : ℝ) /
        25600000000)

theorem nodeExpN02702PlusPointZero2577 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def nodeExpN02702PlusPointP000Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02702PlusPointP000Error2577 : ℝ := 0

theorem nodeExpN02702PlusPointP000Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02702PlusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |nodeExpN02702PlusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02702PlusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem nodeExpN02702PlusPointP000BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP000Center2577‖ ≤ nodeExpN02702PlusPointP000Error2577
          := by
  rw [nodeExpN02702PlusPointP000Exterior2577]
  norm_num [nodeExpN02702PlusPointP000Center2577, nodeExpN02702PlusPointP000Error2577,
      nodeExpN02702PlusPointZero2577]

def nodeExpN02702PlusPointP001Input2577 : RatPair2542 := ((((-((18 * 10^40
        + 8957448532075589895690199699507613126779) * 10^40
        + 8635177651224989294368066657048977169169)) : ℚ) /
        ((52 * 10^40
        + 5327705452767415333723241392768703787170) * 10^40
        + 3821134574968135018370261083750400000000)),
    ((437706290102569059082793061 : ℚ) /
        1844674407370955161600000000))

def nodeExpN02702PlusPointP001Center2577 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP001Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP001BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP001Center2577‖ ≤ nodeExpN02702PlusPointP001Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP001Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP001Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP001Input2577 9 =
      (nodeExpN02702PlusPointP001Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP001Input2577 9).2 : ℝ) =
      nodeExpN02702PlusPointP001Error2577 := by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP001Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP001Input2577 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          nodeExpN02702PlusPointP001Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP001Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP002Input2577 : RatPair2542 := ((((-((501 * 10^40
        + 8839822183730904454132100309844276595994) * 10^40
        + 5478704563309233690904404413326847597329)) : ℚ) /
        ((2039 * 10^40
        + 5757741460588060628394170300498186110020) * 10^40
        + 7730176828859850146962088670003200000000)),
    (((-437706290102569059082793061) : ℚ) /
        922337203685477580800000000))

def nodeExpN02702PlusPointP002Center2577 : RatPair2542 := ((((-327473819977610762985) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-137641572432642977529) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

noncomputable def nodeExpN02702PlusPointP002Error2577 : ℝ := ((2401498195160185481 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP002BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP002Center2577‖ ≤ nodeExpN02702PlusPointP002Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP002Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP002Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP002Input2577 8 =
      (nodeExpN02702PlusPointP002Center2577, ((2401498195160185481 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP002Input2577 8).2 : ℝ) =
      nodeExpN02702PlusPointP002Error2577 := by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP002Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP002Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02702PlusPointP002Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP002Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP003Input2577 : RatPair2542 := ((((-((10686 * 10^40
        + 5514579033133485558018445580747464399624) * 10^40
        + 6137789117471636006252046452959068041489)) : ℚ) /
        ((59001 * 10^40
        + 3089754565407751898622199770334889942512) * 10^40
        + 5741483004646831459175457370931200000000)),
    (((-437706290102569059082793061) : ℚ) /
        922337203685477580800000000))

def nodeExpN02702PlusPointP003Center2577 : RatPair2542 := ((((-170211882877148968493082023) : ℚ)
    /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    (((-2289353691360944363304748813) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

noncomputable def nodeExpN02702PlusPointP003Error2577 : ℝ := ((37431587606157667393148409 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP003BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP003Center2577‖ ≤ nodeExpN02702PlusPointP003Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP003Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP003Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP003Input2577 8 =
      (nodeExpN02702PlusPointP003Center2577, ((37431587606157667393148409 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP003Input2577 8).2 : ℝ) =
      nodeExpN02702PlusPointP003Error2577 := by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP003Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP003Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02702PlusPointP003Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP003Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP004Input2577 : RatPair2542 := ((((-((1168 * 10^40
        + 3530673673730106098996702978531164745704) * 10^40
        + 2277384033427170932559140326412785097329)) : ℚ) /
        ((7447 * 10^40
        + 8007525417628767465445011537519794516855) * 10^40
        + 5700019301591690146962088670003200000000)),
    ((437706290102569059082793061 : ℚ) /
        922337203685477580800000000))

def nodeExpN02702PlusPointP004Center2577 : RatPair2542 := ((((-676666070280422645745488920633) :
    ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((2275293504233894188352239524669 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

noncomputable def nodeExpN02702PlusPointP004Error2577 : ℝ := ((9077586350185816146255924959 : ℝ)
    /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeExpN02702PlusPointP004BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP004Center2577‖ ≤ nodeExpN02702PlusPointP004Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP004Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP004Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP004Input2577 8 =
      (nodeExpN02702PlusPointP004Center2577, ((9077586350185816146255924959 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP004Input2577 8).2 : ℝ) =
      nodeExpN02702PlusPointP004Error2577 := by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP004Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP004Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02702PlusPointP004Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP004Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP005Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02702PlusPointP005Error2577 : ℝ := 0

theorem nodeExpN02702PlusPointP005Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02702PlusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |nodeExpN02702PlusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02702PlusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem nodeExpN02702PlusPointP005BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP005Center2577‖ ≤ nodeExpN02702PlusPointP005Error2577
          := by
  rw [nodeExpN02702PlusPointP005Exterior2577]
  norm_num [nodeExpN02702PlusPointP005Center2577, nodeExpN02702PlusPointP005Error2577,
      nodeExpN02702PlusPointZero2577]

def nodeExpN02702PlusPointP006Input2577 : RatPair2542 :=
    ((((-16439531033496690691568499820795671) : ℚ) /
        27576812937084734710212198400000000),
    ((0 : ℚ) /
        1))

def nodeExpN02702PlusPointP006Center2577 : RatPair2542 := (((1061161581669737 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP006Error2577 : ℝ := ((308762315073 : ℝ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))

theorem nodeExpN02702PlusPointP006BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP006Center2577‖ ≤ nodeExpN02702PlusPointP006Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP006Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP006Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP006Input2577 7 =
      (nodeExpN02702PlusPointP006Center2577, ((308762315073 : ℚ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP006Input2577 7).2 : ℝ) =
      nodeExpN02702PlusPointP006Error2577 := by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP006Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP006Input2577 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          nodeExpN02702PlusPointP006Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP006Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP007Input2577 : RatPair2542 := ((((-((10686 * 10^40
        + 5514579033133485558018445580747464399624) * 10^40
        + 6137789117471636006252046452959068041489)) : ℚ) /
        ((14750 * 10^40
        + 3272438641351937974655549942583722485628) * 10^40
        + 1435370751161707864793864342732800000000)),
    ((0 : ℚ) /
        1))

def nodeExpN02702PlusPointP007Center2577 : RatPair2542 := (((5327421052927345222380711195 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP007Error2577 : ℝ := ((1547288813920703326910549 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP007BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP007Center2577‖ ≤ nodeExpN02702PlusPointP007Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP007Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP007Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP007Input2577 6 =
      (nodeExpN02702PlusPointP007Center2577, ((1547288813920703326910549 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP007Input2577 6).2 : ℝ) =
      nodeExpN02702PlusPointP007Error2577 := by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP007Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP007Input2577 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          nodeExpN02702PlusPointP007Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP007Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP008Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((315234250415438586120416073 : ℚ) /
        236118324143482260684800000000))

def nodeExpN02702PlusPointP008Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP008Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP008BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP008Center2577‖ ≤ nodeExpN02702PlusPointP008Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP008Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP008Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP008Input2577 15 =
      (nodeExpN02702PlusPointP008Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP008Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP008Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP008Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP008Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP008Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP008Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP009Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((468835922968538293612120599 : ℚ) /
        236118324143482260684800000000))

def nodeExpN02702PlusPointP009Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP009Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP009BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP009Center2577‖ ≤ nodeExpN02702PlusPointP009Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP009Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP009Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP009Input2577 15 =
      (nodeExpN02702PlusPointP009Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP009Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP009Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP009Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP009Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP009Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP009Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP010Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((278897497562407945441511889 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02702PlusPointP010Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP010Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP010BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP010Center2577‖ ≤ nodeExpN02702PlusPointP010Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP010Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP010Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP010Input2577 15 =
      (nodeExpN02702PlusPointP010Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP010Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP010Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP010Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP010Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP010Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP010Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP011Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((308553336021908726764541409 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02702PlusPointP011Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP011Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP011BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP011Center2577‖ ≤ nodeExpN02702PlusPointP011Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP011Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP011Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP011Input2577 15 =
      (nodeExpN02702PlusPointP011Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP011Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP011Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP011Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP011Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP011Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP011Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP012Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((6785390535256519649532381 : ℚ) /
        2361183241434822606848000000))

def nodeExpN02702PlusPointP012Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP012Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP012BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP012Center2577‖ ≤ nodeExpN02702PlusPointP012Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP012Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP012Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP012Input2577 15 =
      (nodeExpN02702PlusPointP012Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP012Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP012Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP012Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP012Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP012Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP012Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP013Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((73452149567042081226768819 : ℚ) /
        23611832414348226068480000000))

def nodeExpN02702PlusPointP013Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP013Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP013BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP013Center2577‖ ≤ nodeExpN02702PlusPointP013Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP013Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP013Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP013Input2577 15 =
      (nodeExpN02702PlusPointP013Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP013Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP013Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP013Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP013Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP013Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP013Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP014Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((419125613659595683276618299 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02702PlusPointP014Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP014Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP014BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP014Center2577‖ ≤ nodeExpN02702PlusPointP014Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP014Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP014Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP014Input2577 15 =
      (nodeExpN02702PlusPointP014Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP014Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP014Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP014Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP014Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP014Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP014Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP015Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((456286966545542434888967823 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02702PlusPointP015Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP015Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP015BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP015Center2577‖ ≤ nodeExpN02702PlusPointP015Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP015Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP015Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP015Input2577 15 =
      (nodeExpN02702PlusPointP015Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP015Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP015Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP015Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP015Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP015Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP015Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP016Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((241571331091476180442591281 : ℚ) /
        59029581035870565171200000000))

def nodeExpN02702PlusPointP016Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP016Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP016BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP016Center2577‖ ≤ nodeExpN02702PlusPointP016Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP016Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP016Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP016Input2577 15 =
      (nodeExpN02702PlusPointP016Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP016Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP016Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP016Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP016Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP016Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP016Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP017Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((535308171979337431536686643 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02702PlusPointP017Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP017Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP017BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP017Center2577‖ ≤ nodeExpN02702PlusPointP017Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP017Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP017Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP017Input2577 15 =
      (nodeExpN02702PlusPointP017Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP017Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP017Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP017Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP017Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP017Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP017Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP018Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((138757710302715355185282117 : ℚ) /
        29514790517935282585600000000))

def nodeExpN02702PlusPointP018Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP018Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP018BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP018Center2577‖ ≤ nodeExpN02702PlusPointP018Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP018Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP018Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP018Input2577 15 =
      (nodeExpN02702PlusPointP018Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP018Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP018Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP018Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP018Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP018Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP018Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP019Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((29533753606550223310219719 : ℚ) /
        5902958103587056517120000000))

def nodeExpN02702PlusPointP019Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP019Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP019BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP019Center2577‖ ≤ nodeExpN02702PlusPointP019Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP019Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP019Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP019Input2577 15 =
      (nodeExpN02702PlusPointP019Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP019Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP019Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP019Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP019Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP019Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP019Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP020Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((629435323401138262557665571 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02702PlusPointP020Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP020Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP020BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP020Center2577‖ ≤ nodeExpN02702PlusPointP020Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP020Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP020Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP020Input2577 15 =
      (nodeExpN02702PlusPointP020Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP020Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP020Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP020Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP020Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP020Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP020Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP021Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((661782268241419174231706883 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02702PlusPointP021Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP021Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP021BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP021Center2577‖ ≤ nodeExpN02702PlusPointP021Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP021Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP021Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP021Input2577 15 =
      (nodeExpN02702PlusPointP021Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP021Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP021Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP021Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP021Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP021Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP021Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP022Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((135667725494164983963605697 : ℚ) /
        23611832414348226068480000000))

def nodeExpN02702PlusPointP022Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP022Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP022BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP022Center2577‖ ≤ nodeExpN02702PlusPointP022Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP022Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP022Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP022Input2577 15 =
      (nodeExpN02702PlusPointP022Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP022Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP022Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP022Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP022Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP022Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP022Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP023Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((363036843833529947066478597 : ℚ) /
        59029581035870565171200000000))

def nodeExpN02702PlusPointP023Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP023Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP023BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP023Center2577‖ ≤ nodeExpN02702PlusPointP023Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP023Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP023Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP023Input2577 15 =
      (nodeExpN02702PlusPointP023Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP023Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP023Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP023Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP023Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP023Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP023Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP024Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((374005394131059804721629723 : ℚ) /
        59029581035870565171200000000))

def nodeExpN02702PlusPointP024Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP024Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP024BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP024Center2577‖ ≤ nodeExpN02702PlusPointP024Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP024Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP024Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP024Input2577 15 =
      (nodeExpN02702PlusPointP024Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP024Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP024Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP024Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP024Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP024Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP024Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP025Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((12117435734886672992717097 : ℚ) /
        1844674407370955161600000000))

def nodeExpN02702PlusPointP025Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP025Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP025BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP025Center2577‖ ≤ nodeExpN02702PlusPointP025Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP025Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP025Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP025Input2577 15 =
      (nodeExpN02702PlusPointP025Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP025Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP025Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP025Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP025Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP025Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP025Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP026Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((25113280636521318884391333 : ℚ) /
        3689348814741910323200000000))

def nodeExpN02702PlusPointP026Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP026Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP026BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP026Center2577‖ ≤ nodeExpN02702PlusPointP026Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP026Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP026Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP026Input2577 15 =
      (nodeExpN02702PlusPointP026Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP026Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP026Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP026Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP026Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP026Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP026Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP027Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((52761707395609667092460043 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02702PlusPointP027Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP027Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP027BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP027Center2577‖ ≤ nodeExpN02702PlusPointP027Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP027Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP027Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP027Input2577 15 =
      (nodeExpN02702PlusPointP027Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP027Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP027Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP027Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP027Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP027Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP027Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP028Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((215061626496775559671970943 : ℚ) /
        29514790517935282585600000000))

def nodeExpN02702PlusPointP028Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP028Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP028BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP028Center2577‖ ≤ nodeExpN02702PlusPointP028Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP028Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP028Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP028Input2577 15 =
      (nodeExpN02702PlusPointP028Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP028Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP028Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP028Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP028Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP028Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP028Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02702PlusPointP029Input2577 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((221173897030652641300579731 : ℚ) /
        29514790517935282585600000000))

def nodeExpN02702PlusPointP029Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02702PlusPointP029Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02702PlusPointP029BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeExpN02702PlusPointPosition2577 -
      embedPair2542 nodeExpN02702PlusPointP029Center2577‖ ≤ nodeExpN02702PlusPointP029Error2577
          := by
  have hx : |nodeExpN02702PlusPointPosition2577| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02702PlusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02702PlusPointP029Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02702PlusPointP029Input2577]
  have hs : compactExp2547 nodeExpN02702PlusPointP029Input2577 15 =
      (nodeExpN02702PlusPointP029Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02702PlusPointP029Input2577 15).2 : ℝ) =
      nodeExpN02702PlusPointP029Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02702PlusPointP029Error2577]
  have h := compactExp_error2547 nodeExpN02702PlusPointP029Input2577 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      nodeExpN02702PlusPointPosition2577 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          nodeExpN02702PlusPointP029Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02702PlusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02702PlusPointP029Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem nodeExpN02702PlusPointGrid2577 :
    -stripRadius2303 + (2702 : ℝ) * (2 * stripRadius2303 / 10240) =
      nodeExpN02702PlusPointPosition2577 := by
  norm_num [stripRadius2303, nodeExpN02702PlusPointPosition2577]

end ConnesWeilRH.Dev
