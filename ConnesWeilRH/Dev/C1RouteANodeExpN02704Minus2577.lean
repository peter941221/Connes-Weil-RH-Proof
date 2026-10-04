import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def nodeExpN02704MinusPointPosition2577 : ℝ := (((-9895936151) : ℝ) /
        3200000000)

theorem nodeExpN02704MinusPointZero2577 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def nodeExpN02704MinusPointP000Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02704MinusPointP000Error2577 : ℝ := 0

theorem nodeExpN02704MinusPointP000Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02704MinusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |nodeExpN02704MinusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02704MinusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem nodeExpN02704MinusPointP000BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP000Center2577‖ ≤
          nodeExpN02704MinusPointP000Error2577 := by
  rw [nodeExpN02704MinusPointP000Exterior2577]
  norm_num [nodeExpN02704MinusPointP000Center2577, nodeExpN02704MinusPointP000Error2577,
      nodeExpN02704MinusPointZero2577]

def nodeExpN02704MinusPointP001Input2577 : RatPair2542 := ((((-((20 * 10^40
        + 8991036429139976524574151519976207695507) * 10^40
        + 4753568805857603624994734849814902306889)) : ℚ) /
        ((59 * 10^40
        + 5965149429887586107108459481843895661464) * 10^40
        + 568333469734220561590691302604800000000)),
    ((54668031270047913913566379 : ℚ) /
        230584300921369395200000000))

def nodeExpN02704MinusPointP001Center2577 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP001Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP001BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP001Center2577‖ ≤
          nodeExpN02704MinusPointP001Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP001Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP001Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP001Input2577 9 =
      (nodeExpN02704MinusPointP001Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP001Input2577 9).2 : ℝ) =
      nodeExpN02704MinusPointP001Error2577 := by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP001Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP001Input2577 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          nodeExpN02704MinusPointP001Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP001Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP002Input2577 : RatPair2542 := ((((-((536 * 10^40
        + 8661499926090410127664480832514854352328) * 10^40
        + 1664516618783932279964932674095321675849)) : ℚ) /
        ((2298 * 10^40
        + 4999305507355519060301944907893290580952) * 10^40
        + 3852905515627880742725530420838400000000)),
    (((-54668031270047913913566379) : ℚ) /
        115292150460684697600000000))

def nodeExpN02704MinusPointP002Center2577 : RatPair2542 := ((((-1659707957179232547945) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-14245775921432001046225) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

noncomputable def nodeExpN02704MinusPointP002Error2577 : ℝ := ((14710856534966248467 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem nodeExpN02704MinusPointP002BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP002Center2577‖ ≤
          nodeExpN02704MinusPointP002Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP002Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP002Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP002Input2577 8 =
      (nodeExpN02704MinusPointP002Center2577, ((14710856534966248467 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP002Input2577 8).2 : ℝ) =
      nodeExpN02704MinusPointP002Error2577 := by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP002Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP002Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02704MinusPointP002Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP002Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP003Input2577 : RatPair2542 := ((((-((70228 * 10^40
        + 1578618648103239365546333140061587571427) * 10^40
        + 2985539216356294380083266837386150844323)) : ℚ) /
        ((415806 * 10^40
        + 9371244809296725772723606675176446357802) * 10^40
        + 447237920754980795911929244876800000000)),
    (((-54668031270047913913566379) : ℚ) /
        115292150460684697600000000))

def nodeExpN02704MinusPointP003Center2577 : RatPair2542 := ((((-102983243484972695843730390395) :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-220984090002582734303232415591) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

noncomputable def nodeExpN02704MinusPointP003Error2577 : ℝ := ((53476660314846633286429113 : ℝ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))

theorem nodeExpN02704MinusPointP003BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP003Center2577‖ ≤
          nodeExpN02704MinusPointP003Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP003Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP003Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP003Input2577 8 =
      (nodeExpN02704MinusPointP003Center2577, ((53476660314846633286429113 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP003Input2577 8).2 : ℝ) =
      nodeExpN02704MinusPointP003Error2577 := by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP003Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP003Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02704MinusPointP003Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP003Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP004Input2577 : RatPair2542 := ((((-((1213 * 10^40
        + 1156709413815825987536732349495727924044) * 10^40
        + 3431592827938250463508120344993759175849)) : ℚ) /
        ((8382 * 10^40
        + 7530312459026314251984141299542600038641) * 10^40
        + 5318978297451200742725530420838400000000)),
    ((54668031270047913913566379 : ℚ) /
        115292150460684697600000000))

def nodeExpN02704MinusPointP004Center2577 : RatPair2542 := ((((-50249225686456146115974385225945)
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((26956519905289865112084360768053 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

noncomputable def nodeExpN02704MinusPointP004Error2577 : ℝ := ((203758462513469541571904517823 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeExpN02704MinusPointP004BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP004Center2577‖ ≤
          nodeExpN02704MinusPointP004Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP004Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP004Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP004Input2577 8 =
      (nodeExpN02704MinusPointP004Center2577, ((203758462513469541571904517823 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP004Input2577 8).2 : ℝ) =
      nodeExpN02704MinusPointP004Error2577 := by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP004Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP004Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02704MinusPointP004Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP004Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP005Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02704MinusPointP005Error2577 : ℝ := 0

theorem nodeExpN02704MinusPointP005Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02704MinusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |nodeExpN02704MinusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02704MinusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem nodeExpN02704MinusPointP005BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP005Center2577‖ ≤
          nodeExpN02704MinusPointP005Error2577 := by
  rw [nodeExpN02704MinusPointP005Exterior2577]
  norm_num [nodeExpN02704MinusPointP005Center2577, nodeExpN02704MinusPointP005Error2577,
      nodeExpN02704MinusPointZero2577]

def nodeExpN02704MinusPointP006Input2577 : RatPair2542 := ((((-10268344805974392100986400550317)
    : ℚ) /
        17997946250671801739673600000000),
    ((0 : ℚ) /
        1))

def nodeExpN02704MinusPointP006Center2577 : RatPair2542 := (((14068696455048369 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP006Error2577 : ℝ := ((2301259777463 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem nodeExpN02704MinusPointP006BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP006Center2577‖ ≤
          nodeExpN02704MinusPointP006Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP006Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP006Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP006Input2577 7 =
      (nodeExpN02704MinusPointP006Center2577, ((2301259777463 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP006Input2577 7).2 : ℝ) =
      nodeExpN02704MinusPointP006Error2577 := by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP006Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP006Input2577 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          nodeExpN02704MinusPointP006Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP006Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP007Input2577 : RatPair2542 := ((((-((70228 * 10^40
        + 1578618648103239365546333140061587571427) * 10^40
        + 2985539216356294380083266837386150844323)) : ℚ) /
        ((103951 * 10^40
        + 7342811202324181443180901668794111589450) * 10^40
        + 5111809480188745198977982311219200000000)),
    ((0 : ℚ) /
        1))

def nodeExpN02704MinusPointP007Center2577 : RatPair2542 := (((121901103843397125307301253425 : ℚ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP007Error2577 : ℝ := ((8428687828913767722721185 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem nodeExpN02704MinusPointP007BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP007Center2577‖ ≤
          nodeExpN02704MinusPointP007Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP007Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP007Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP007Input2577 6 =
      (nodeExpN02704MinusPointP007Center2577, ((8428687828913767722721185 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP007Input2577 6).2 : ℝ) =
      nodeExpN02704MinusPointP007Error2577 := by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP007Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP007Input2577 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          nodeExpN02704MinusPointP007Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP007Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP008Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((39371688844277275851267847 : ℚ) /
        14757395258967641292800000000))

def nodeExpN02704MinusPointP008Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP008Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP008BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP008Center2577‖ ≤
          nodeExpN02704MinusPointP008Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP008Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP008Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP008Input2577 14 =
      (nodeExpN02704MinusPointP008Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP008Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP008Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP008Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP008Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP008Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP008Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP009Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((58556016847187164876286361 : ℚ) /
        14757395258967641292800000000))

def nodeExpN02704MinusPointP009Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP009Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP009BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP009Center2577‖ ≤
          nodeExpN02704MinusPointP009Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP009Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP009Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP009Input2577 14 =
      (nodeExpN02704MinusPointP009Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP009Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP009Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP009Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP009Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP009Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP009Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP010Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((34833351639308188388476671 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02704MinusPointP010Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP010Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP010BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP010Center2577‖ ≤
          nodeExpN02704MinusPointP010Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP010Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP010Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP010Input2577 14 =
      (nodeExpN02704MinusPointP010Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP010Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP010Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP010Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP010Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP010Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP010Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP011Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((38537265293058906320467951 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02704MinusPointP011Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP011Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP011BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP011Center2577‖ ≤
          nodeExpN02704MinusPointP011Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP011Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP011Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP011Input2577 14 =
      (nodeExpN02704MinusPointP011Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP011Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP011Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP011Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP011Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP011Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP011Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP012Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((847472267017150096839859 : ℚ) /
        147573952589676412928000000))

def nodeExpN02704MinusPointP012Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP012Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP012BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP012Center2577‖ ≤
          nodeExpN02704MinusPointP012Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP012Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP012Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP012Input2577 14 =
      (nodeExpN02704MinusPointP012Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP012Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP012Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP012Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP012Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP012Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP012Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP013Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((9173924387612369119306941 : ℚ) /
        1475739525896764129280000000))

def nodeExpN02704MinusPointP013Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP013Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP013BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP013Center2577‖ ≤
          nodeExpN02704MinusPointP013Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP013Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP013Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP013Input2577 14 =
      (nodeExpN02704MinusPointP013Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP013Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP013Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP013Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP013Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP013Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP013Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP014Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((52347367793712943072596661 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02704MinusPointP014Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP014Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP014BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP014Center2577‖ ≤
          nodeExpN02704MinusPointP014Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP014Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP014Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP014Input2577 14 =
      (nodeExpN02704MinusPointP014Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP014Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP014Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP014Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP014Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP014Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP014Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP015Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((56988694746382884754536097 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02704MinusPointP015Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP015Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP015BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP015Center2577‖ ≤
          nodeExpN02704MinusPointP015Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP015Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP015Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP015Input2577 14 =
      (nodeExpN02704MinusPointP015Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP015Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP015Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP015Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP015Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP015Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP015Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP016Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((30171440028794791767436959 : ℚ) /
        3689348814741910323200000000))

def nodeExpN02704MinusPointP016Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP016Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP016BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP016Center2577‖ ≤
          nodeExpN02704MinusPointP016Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP016Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP016Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP016Input2577 14 =
      (nodeExpN02704MinusPointP016Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP016Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP016Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP016Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP016Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP016Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP016Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP017Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((66858175325789869447510077 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02704MinusPointP017Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP017Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP017BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP017Center2577‖ ≤
          nodeExpN02704MinusPointP017Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP017Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP017Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP017Input2577 14 =
      (nodeExpN02704MinusPointP017Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP017Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP017Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP017Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP017Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP017Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP017Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP018Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((17330367457162959994191563 : ℚ) /
        1844674407370955161600000000))

def nodeExpN02704MinusPointP018Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP018Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP018BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP018Center2577‖ ≤
          nodeExpN02704MinusPointP018Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP018Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP018Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP018Input2577 14 =
      (nodeExpN02704MinusPointP018Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP018Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP018Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP018Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP018Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP018Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP018Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP019Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((3688665669635304979192041 : ℚ) /
        368934881474191032320000000))

def nodeExpN02704MinusPointP019Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP019Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP019BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP019Center2577‖ ≤
          nodeExpN02704MinusPointP019Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP019Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP019Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP019Input2577 14 =
      (nodeExpN02704MinusPointP019Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP019Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP019Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP019Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP019Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP019Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP019Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP020Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((78614337331324960832264269 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02704MinusPointP020Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP020Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP020BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP020Center2577‖ ≤
          nodeExpN02704MinusPointP020Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP020Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP020Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP020Input2577 14 =
      (nodeExpN02704MinusPointP020Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP020Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP020Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP020Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP020Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP020Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP020Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP021Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((82654361045867903481379437 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02704MinusPointP021Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP021Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP021BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP021Center2577‖ ≤
          nodeExpN02704MinusPointP021Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP021Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP021Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP021Input2577 14 =
      (nodeExpN02704MinusPointP021Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP021Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP021Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP021Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP021Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP021Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP021Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP022Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((16944438833431689477671183 : ℚ) /
        1475739525896764129280000000))

def nodeExpN02704MinusPointP022Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP022Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP022BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP022Center2577‖ ≤
          nodeExpN02704MinusPointP022Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP022Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP022Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP022Input2577 14 =
      (nodeExpN02704MinusPointP022Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP022Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP022Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP022Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP022Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP022Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP022Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP023Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((45342070652492160469014283 : ℚ) /
        3689348814741910323200000000))

def nodeExpN02704MinusPointP023Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP023Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP023BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP023Center2577‖ ≤
          nodeExpN02704MinusPointP023Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP023Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP023Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP023Input2577 14 =
      (nodeExpN02704MinusPointP023Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP023Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP023Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP023Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP023Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP023Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP023Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP024Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((46712005387750232020650197 : ℚ) /
        3689348814741910323200000000))

def nodeExpN02704MinusPointP024Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP024Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP024BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP024Center2577‖ ≤
          nodeExpN02704MinusPointP024Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP024Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP024Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP024Input2577 14 =
      (nodeExpN02704MinusPointP024Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP024Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP024Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP024Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP024Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP024Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP024Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP025Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((1513426630246391746815783 : ℚ) /
        115292150460684697600000000))

def nodeExpN02704MinusPointP025Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP025Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP025BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP025Center2577‖ ≤
          nodeExpN02704MinusPointP025Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP025Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP025Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP025Input2577 14 =
      (nodeExpN02704MinusPointP025Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP025Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP025Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP025Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP025Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP025Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP025Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP026Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((3136563586529957941722987 : ℚ) /
        230584300921369395200000000))

def nodeExpN02704MinusPointP026Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP026Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP026BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP026Center2577‖ ≤
          nodeExpN02704MinusPointP026Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP026Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP026Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP026Input2577 14 =
      (nodeExpN02704MinusPointP026Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP026Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP026Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP026Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP026Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP026Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP026Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP027Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((6589758326498808710472677 : ℚ) /
        461168601842738790400000000))

def nodeExpN02704MinusPointP027Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP027Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP027BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP027Center2577‖ ≤
          nodeExpN02704MinusPointP027Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP027Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP027Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP027Input2577 14 =
      (nodeExpN02704MinusPointP027Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP027Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP027Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP027Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP027Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP027Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP027Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP028Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((26860467825486442936697777 : ℚ) /
        1844674407370955161600000000))

def nodeExpN02704MinusPointP028Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP028Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP028BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP028Center2577‖ ≤
          nodeExpN02704MinusPointP028Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP028Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP028Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP028Input2577 14 =
      (nodeExpN02704MinusPointP028Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP028Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP028Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP028Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP028Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP028Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP028Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02704MinusPointP029Input2577 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((27623869687037674802636509 : ℚ) /
        1844674407370955161600000000))

def nodeExpN02704MinusPointP029Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02704MinusPointP029Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02704MinusPointP029BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeExpN02704MinusPointPosition2577 -
      embedPair2542 nodeExpN02704MinusPointP029Center2577‖ ≤
          nodeExpN02704MinusPointP029Error2577 := by
  have hx : |nodeExpN02704MinusPointPosition2577| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02704MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02704MinusPointP029Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02704MinusPointP029Input2577]
  have hs : compactExp2547 nodeExpN02704MinusPointP029Input2577 14 =
      (nodeExpN02704MinusPointP029Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02704MinusPointP029Input2577 14).2 : ℝ) =
      nodeExpN02704MinusPointP029Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02704MinusPointP029Error2577]
  have h := compactExp_error2547 nodeExpN02704MinusPointP029Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      nodeExpN02704MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02704MinusPointP029Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02704MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02704MinusPointP029Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem nodeExpN02704MinusPointGrid2577 :
    -stripRadius2303 + (2704 : ℝ) * (2 * stripRadius2303 / 10240) =
      nodeExpN02704MinusPointPosition2577 := by
  norm_num [stripRadius2303, nodeExpN02704MinusPointPosition2577]

end ConnesWeilRH.Dev
