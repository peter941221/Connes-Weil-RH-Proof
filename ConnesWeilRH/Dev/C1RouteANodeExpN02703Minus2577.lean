import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def nodeExpN02703MinusPointPosition2577 : ℝ := (((-158400514417) : ℝ) /
        51200000000)

theorem nodeExpN02703MinusPointZero2577 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def nodeExpN02703MinusPointP000Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02703MinusPointP000Error2577 : ℝ := 0

theorem nodeExpN02703MinusPointP000Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02703MinusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |nodeExpN02703MinusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02703MinusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem nodeExpN02703MinusPointP000BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP000Center2577‖ ≤
          nodeExpN02703MinusPointP000Error2577 := by
  rw [nodeExpN02703MinusPointP000Exterior2577]
  norm_num [nodeExpN02703MinusPointP000Center2577, nodeExpN02703MinusPointP000Error2577,
      nodeExpN02703MinusPointZero2577]

def nodeExpN02703MinusPointP001Input2577 : RatPair2542 := ((((-((334 * 10^40
        + 3964799398326123205247732121693677107446) * 10^40
        + 6770193440221610479362399611030126300847)) : ℚ) /
        ((949 * 10^40
        + 5678772037045116961918709892218078778647) * 10^40
        + 478078034072945845341163828019200000000)),
    ((875050540262952370391324093 : ℚ) /
        3689348814741910323200000000))

def nodeExpN02703MinusPointP001Center2577 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP001Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP001BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP001Center2577‖ ≤
          nodeExpN02703MinusPointP001Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP001Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP001Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP001Input2577 9 =
      (nodeExpN02703MinusPointP001Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP001Input2577 9).2 : ℝ) =
      nodeExpN02703MinusPointP001Error2577 := by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP001Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP001Input2577 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          nodeExpN02703MinusPointP001Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP001Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP002Input2577 : RatPair2542 := ((((-((8589 * 10^40
        + 9586772195308868683427274465402369322489) * 10^40
        + 6038857346448285049803753288048182922927)) : ℚ) /
        ((36744 * 10^40
        + 1879937388438218950297983988018634857015) * 10^40
        + 2724428396649426762729310624153600000000)),
    (((-875050540262952370391324093) : ℚ) /
        1844674407370955161600000000))

def nodeExpN02703MinusPointP002Center2577 : RatPair2542 := ((((-6970437208017745221721) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-1648025687177071950569) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)))

noncomputable def nodeExpN02703MinusPointP002Error2577 : ℝ := ((13890051478555904937 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem nodeExpN02703MinusPointP002BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP002Center2577‖ ≤
          nodeExpN02703MinusPointP002Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP002Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP002Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP002Input2577 8 =
      (nodeExpN02703MinusPointP002Center2577, ((13890051478555904937 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP002Input2577 8).2 : ℝ) =
      nodeExpN02703MinusPointP002Error2577 := by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP002Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP002Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02703MinusPointP002Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP002Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP003Input2577 : RatPair2542 := ((((-((1123650 * 10^40
        + 2960581386159307605172018669347586747959) * 10^40
        + 6646801809483559253159682348452673876229)) : ℚ) /
        ((6650196 * 10^40
        + 4642788052740272456750226203440576329812) * 10^40
        + 5806699242230935752901173261107200000000)),
    (((-875050540262952370391324093) : ℚ) /
        1844674407370955161600000000))

def nodeExpN02703MinusPointP003Center2577 : RatPair2542 := ((((-111959054128113850382852145511) :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-52941125960634317898434698617) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

noncomputable def nodeExpN02703MinusPointP003Error2577 : ℝ := ((836402606886840621453327411 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP003BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP003Center2577‖ ≤
          nodeExpN02703MinusPointP003Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP003Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP003Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP003Input2577 8 =
      (nodeExpN02703MinusPointP003Center2577, ((836402606886840621453327411 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP003Input2577 8).2 : ℝ) =
      nodeExpN02703MinusPointP003Error2577 := by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP003Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP003Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02703MinusPointP003Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP003Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP004Input2577 : RatPair2542 := ((((-((19409 * 10^40
        + 7076422721502121743027980817409819781999) * 10^40
        + 486238254540120343256631437462245422927)) : ℚ) /
        ((134092 * 10^40
        + 2376048615170942017213126254407586180041) * 10^40
        + 6181592905822546762729310624153600000000)),
    ((875050540262952370391324093 : ℚ) /
        1844674407370955161600000000))

def nodeExpN02703MinusPointP004Center2577 : RatPair2542 := ((((-55129591407190581895480487846843)
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((26068661133083737741581242579421 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

noncomputable def nodeExpN02703MinusPointP004Error2577 : ℝ := ((401998131106820665747522716369 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP004BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP004Center2577‖ ≤
          nodeExpN02703MinusPointP004Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP004Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP004Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP004Input2577 8 =
      (nodeExpN02703MinusPointP004Center2577, ((401998131106820665747522716369 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP004Input2577 8).2 : ℝ) =
      nodeExpN02703MinusPointP004Error2577 := by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP004Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP004Input2577 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          nodeExpN02703MinusPointP004Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP004Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP005Center2577 : RatPair2542 := (0, 0)

noncomputable def nodeExpN02703MinusPointP005Error2577 : ℝ := 0

theorem nodeExpN02703MinusPointP005Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02703MinusPointPosition2577 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |nodeExpN02703MinusPointPosition2577| := by
    norm_num [storedWidth, nodeExpN02703MinusPointPosition2577]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem nodeExpN02703MinusPointP005BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP005Center2577‖ ≤
          nodeExpN02703MinusPointP005Error2577 := by
  rw [nodeExpN02703MinusPointP005Exterior2577]
  norm_num [nodeExpN02703MinusPointP005Center2577, nodeExpN02703MinusPointP005Error2577,
      nodeExpN02703MinusPointZero2577]

def nodeExpN02703MinusPointP006Input2577 : RatPair2542 :=
    ((((-42059867730981584248264924735116571) : ℚ) /
        73628896602487849615844966400000000),
    ((0 : ℚ) /
        1))

def nodeExpN02703MinusPointP006Center2577 : RatPair2542 := (((25684408913017653 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP006Error2577 : ℝ := ((4299411043621 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeExpN02703MinusPointP006BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP006Center2577‖ ≤
          nodeExpN02703MinusPointP006Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP006Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP006Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP006Input2577 7 =
      (nodeExpN02703MinusPointP006Center2577, ((4299411043621 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP006Input2577 7).2 : ℝ) =
      nodeExpN02703MinusPointP006Error2577 := by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP006Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP006Input2577 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          nodeExpN02703MinusPointP006Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP006Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP007Input2577 : RatPair2542 := ((((-((1123650 * 10^40
        + 2960581386159307605172018669347586747959) * 10^40
        + 6646801809483559253159682348452673876229)) : ℚ) /
        ((1662549 * 10^40
        + 1160697013185068114187556550860144082453) * 10^40
        + 1451674810557733938225293315276800000000)),
    ((0 : ℚ) /
        1))

def nodeExpN02703MinusPointP007Center2577 : RatPair2542 := (((29942401709609983149248847675 : ℚ)
    /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP007Error2577 : ℝ := ((8283591204048782430816091 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem nodeExpN02703MinusPointP007BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP007Center2577‖ ≤
          nodeExpN02703MinusPointP007Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP007Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP007Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP007Input2577 6 =
      (nodeExpN02703MinusPointP007Center2577, ((8283591204048782430816091 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP007Input2577 6).2 : ℝ) =
      nodeExpN02703MinusPointP007Error2577 := by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP007Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP007Input2577 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          nodeExpN02703MinusPointP007Input2577)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP007Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP008Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((630207761169656792930558849 : ℚ) /
        236118324143482260684800000000))

def nodeExpN02703MinusPointP008Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP008Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP008BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP008Center2577‖ ≤
          nodeExpN02703MinusPointP008Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP008Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP008Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP008Input2577 14 =
      (nodeExpN02703MinusPointP008Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP008Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP008Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP008Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP008Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP008Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP008Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP009Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((937284057746035612622411487 : ℚ) /
        236118324143482260684800000000))

def nodeExpN02703MinusPointP009Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP009Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP009BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP009Center2577‖ ≤
          nodeExpN02703MinusPointP009Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP009Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP009Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP009Input2577 14 =
      (nodeExpN02703MinusPointP009Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP009Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP009Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP009Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP009Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP009Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP009Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP010Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((557564310676873452549325257 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02703MinusPointP010Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP010Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP010BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP010Center2577‖ ≤
          nodeExpN02703MinusPointP010Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP010Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP010Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP010Input2577 14 =
      (nodeExpN02703MinusPointP010Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP010Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP010Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP010Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP010Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP010Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP010Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP011Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((616851458366379977328285017 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02703MinusPointP011Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP011Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP011BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP011Center2577‖ ≤
          nodeExpN02703MinusPointP011Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP011Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP011Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP011Input2577 14 =
      (nodeExpN02703MinusPointP011Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP011Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP011Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP011Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP011Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP011Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP011Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP012Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((13565168671393720424251253 : ℚ) /
        2361183241434822606848000000))

def nodeExpN02703MinusPointP012Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP012Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP012BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP012Center2577‖ ≤
          nodeExpN02703MinusPointP012Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP012Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP012Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP012Input2577 14 =
      (nodeExpN02703MinusPointP012Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP012Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP012Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP012Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP012Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP012Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP012Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP013Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((146843544667941034181224347 : ℚ) /
        23611832414348226068480000000))

def nodeExpN02703MinusPointP013Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP013Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP013BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP013Center2577‖ ≤
          nodeExpN02703MinusPointP013Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP013Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP013Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP013Input2577 14 =
      (nodeExpN02703MinusPointP013Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP013Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP013Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP013Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP013Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP013Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP013Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP014Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((837904556009299227857391587 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02703MinusPointP014Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP014Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP014BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP014Center2577‖ ≤
          nodeExpN02703MinusPointP014Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP014Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP014Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP014Input2577 14 =
      (nodeExpN02703MinusPointP014Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP014Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP014Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP014Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP014Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP014Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP014Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP015Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((912196524516605512925256599 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02703MinusPointP015Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP015Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP015BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP015Center2577‖ ≤
          nodeExpN02703MinusPointP015Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP015Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP015Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP015Input2577 14 =
      (nodeExpN02703MinusPointP015Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP015Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP015Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP015Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP015Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP015Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP015Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP016Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((482942851321834514582086953 : ℚ) /
        59029581035870565171200000000))

def nodeExpN02703MinusPointP016Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP016Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP016BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP016Center2577‖ ≤
          nodeExpN02703MinusPointP016Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP016Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP016Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP016Input2577 14 =
      (nodeExpN02703MinusPointP016Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP016Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP016Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP016Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP016Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP016Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP016Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP017Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((1070173574585656387116767259 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02703MinusPointP017Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP017Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP017BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP017Center2577‖ ≤
          nodeExpN02703MinusPointP017Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP017Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP017Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP017Input2577 14 =
      (nodeExpN02703MinusPointP017Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP017Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP017Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP017Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP017Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP017Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP017Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP018Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((277400649960019035138814621 : ℚ) /
        29514790517935282585600000000))

def nodeExpN02703MinusPointP018Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP018Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP018BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP018Center2577‖ ≤
          nodeExpN02703MinusPointP018Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP018Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP018Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP018Input2577 14 =
      (nodeExpN02703MinusPointP018Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP018Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP018Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP018Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP018Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP018Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP018Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP019Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((59043078963632663143756047 : ℚ) /
        5902958103587056517120000000))

def nodeExpN02703MinusPointP019Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP019Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP019BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP019Center2577‖ ≤
          nodeExpN02703MinusPointP019Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP019Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP019Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP019Input2577 14 =
      (nodeExpN02703MinusPointP019Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP019Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP019Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP019Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP019Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP019Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP019Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP020Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((1258350022051737949215779723 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02703MinusPointP020Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP020Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP020BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP020Center2577‖ ≤
          nodeExpN02703MinusPointP020Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP020Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP020Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP020Input2577 14 =
      (nodeExpN02703MinusPointP020Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP020Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP020Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP020Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP020Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP020Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP020Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP021Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((1323017156608362402082742379 : ℚ) /
        118059162071741130342400000000))

def nodeExpN02703MinusPointP021Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP021Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP021BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP021Center2577‖ ≤
          nodeExpN02703MinusPointP021Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP021Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP021Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP021Input2577 14 =
      (nodeExpN02703MinusPointP021Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP021Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP021Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP021Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP021Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP021Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP021Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP022Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((271223236161618499784975161 : ℚ) /
        23611832414348226068480000000))

def nodeExpN02703MinusPointP022Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP022Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP022BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP022Center2577‖ ≤
          nodeExpN02703MinusPointP022Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP022Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP022Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP022Input2577 14 =
      (nodeExpN02703MinusPointP022Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP022Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP022Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP022Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP022Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP022Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP022Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP023Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((725773409053467230818592861 : ℚ) /
        59029581035870565171200000000))

def nodeExpN02703MinusPointP023Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP023Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP023BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP023Center2577‖ ≤
          nodeExpN02703MinusPointP023Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP023Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP023Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP023Input2577 14 =
      (nodeExpN02703MinusPointP023Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP023Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP023Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP023Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP023Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP023Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP023Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP024Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((747701437233061660886831299 : ℚ) /
        59029581035870565171200000000))

def nodeExpN02703MinusPointP024Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP024Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP024BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP024Center2577‖ ≤
          nodeExpN02703MinusPointP024Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP024Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP024Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP024Input2577 14 =
      (nodeExpN02703MinusPointP024Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP024Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP024Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP024Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP024Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP024Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP024Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP025Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((24224848776857806967243361 : ℚ) /
        1844674407370955161600000000))

def nodeExpN02703MinusPointP025Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP025Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP025BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP025Center2577‖ ≤
          nodeExpN02703MinusPointP025Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP025Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP025Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP025Input2577 14 =
      (nodeExpN02703MinusPointP025Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP025Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP025Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP025Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP025Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP025Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP025Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP026Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((50205789328760982418175229 : ℚ) /
        3689348814741910323200000000))

def nodeExpN02703MinusPointP026Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP026Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP026BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP026Center2577‖ ≤
          nodeExpN02703MinusPointP026Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP026Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP026Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP026Input2577 14 =
      (nodeExpN02703MinusPointP026Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP026Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP026Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP026Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP026Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP026Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP026Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP027Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((105479774007600136776241459 : ℚ) /
        7378697629483820646400000000))

def nodeExpN02703MinusPointP027Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP027Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP027BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP027Center2577‖ ≤
          nodeExpN02703MinusPointP027Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP027Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP027Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP027Input2577 14 =
      (nodeExpN02703MinusPointP027Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP027Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP027Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP027Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP027Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP027Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP027Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP028Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((429945369100667103165553159 : ℚ) /
        29514790517935282585600000000))

def nodeExpN02703MinusPointP028Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP028Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP028BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP028Center2577‖ ≤
          nodeExpN02703MinusPointP028Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP028Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP028Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP028Input2577 14 =
      (nodeExpN02703MinusPointP028Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP028Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP028Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP028Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP028Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP028Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP028Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

def nodeExpN02703MinusPointP029Input2577 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((442164854526954039721671803 : ℚ) /
        29514790517935282585600000000))

def nodeExpN02703MinusPointP029Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeExpN02703MinusPointP029Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeExpN02703MinusPointP029BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeExpN02703MinusPointPosition2577 -
      embedPair2542 nodeExpN02703MinusPointP029Center2577‖ ≤
          nodeExpN02703MinusPointP029Error2577 := by
  have hx : |nodeExpN02703MinusPointPosition2577| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [nodeExpN02703MinusPointPosition2577, storedWidth]
  have hz : ‖embedPair2542 nodeExpN02703MinusPointP029Input2577‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, nodeExpN02703MinusPointP029Input2577]
  have hs : compactExp2547 nodeExpN02703MinusPointP029Input2577 14 =
      (nodeExpN02703MinusPointP029Center2577, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 nodeExpN02703MinusPointP029Input2577 14).2 : ℝ) =
      nodeExpN02703MinusPointP029Error2577 :=
      by
    rw [hs]
    norm_num [nodeExpN02703MinusPointP029Error2577]
  have h := compactExp_error2547 nodeExpN02703MinusPointP029Input2577 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      nodeExpN02703MinusPointPosition2577 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          nodeExpN02703MinusPointP029Input2577) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [nodeExpN02703MinusPointPosition2577, storedWidth,
        nodeModulation2541,
      embedPair2542, nodeExpN02703MinusPointP029Input2577, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem nodeExpN02703MinusPointGrid2577 :
    -stripRadius2303 + (2703 : ℝ) * (2 * stripRadius2303 / 10240) =
      nodeExpN02703MinusPointPosition2577 := by
  norm_num [stripRadius2303, nodeExpN02703MinusPointPosition2577]

end ConnesWeilRH.Dev
