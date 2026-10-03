import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteAKernelN02701Minus2555
import ConnesWeilRH.Dev.C1RouteABatchN02702Minus2558

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC02701MinusFourthCell2558 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 kernelN02701MinusPosition2555 batchN02702MinusPosition2558 < storedWidth i ^
      2 then
    weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 kernelN02701MinusPosition2555 batchN02702MinusPosition2558 / (storedWidth i
          ^ 2))
      (min (max |kernelN02701MinusPosition2555| |batchN02702MinusPosition2558|) (storedWidth i ^
          2) /
        (storedWidth i ^ 2)) kernelN02701MinusPosition2555 batchN02702MinusPosition2558
  else 0


def batchC02701MinusFourthP001Input2558 : RatPair2542 := ((((-((37 * 10^40
        + 1562371689031746587393783446176657389078) * 10^40
        + 1953838790792223568007048599337075457221)) : ℚ) /
        ((52 * 10^40
        + 5327705452767415333723241392768703787170) * 10^40
        + 3821134574968135018370261083750400000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP001Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP001Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP001ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP001Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02701MinusFourthP001Upper2558 : ℝ := ((375164486795 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP001Exponent2558 : ℝ := (((-((37 * 10^40
        + 1562371689031746587393783446176657389078) * 10^40
        + 1953838790792223568007048599337075457221)) : ℝ) /
        (2052061349424872716147356411690502749168 * 10^40
        + 6343051306933469277415508832358400000000))

theorem batchC02701MinusFourthP001ExpBound2558 :
    Real.exp batchC02701MinusFourthP001Exponent2558 ≤ batchC02701MinusFourthP001ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP001Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP001Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP001Input2558 8).1 =
      batchC02701MinusFourthP001Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP001Input2558 8).2 : ℝ) =
      batchC02701MinusFourthP001Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP001Input2558 8).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP001Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP001Input2558 hz 8
  rw [hc, he] at h
  have ha : (2 : ℂ)^8 * embedPair2542 batchC02701MinusFourthP001Input2558 =
      (batchC02701MinusFourthP001Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP001Input2558,
        batchC02701MinusFourthP001Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP001Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP001Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP001Center2558))).trans
  norm_num [batchC02701MinusFourthP001Error2558, batchC02701MinusFourthP001ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP001Center2558]

theorem batchC02701MinusFourthP001Bound2558 : batchC02701MinusFourthCell2558 ⟨1, by omega⟩ ≤
    batchC02701MinusFourthP001Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      batchC02701MinusFourthP001Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP001Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP001Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((31928949980445633354893769391996928 : ℝ) /
        34926414975038190094216904485546875) ((95826464023198495143285394738511872 : ℝ) /
        104779244925114570282650713456640625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP001ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP001Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((31928949980445633354893769391996928 : ℝ) /
        34926414975038190094216904485546875) ((95826464023198495143285394738511872 : ℝ) /
        104779244925114570282650713456640625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP001ExpUpper2558, batchC02701MinusFourthP001Frequency2558,
        batchC02701MinusFourthP001Upper2558]

def batchC02701MinusFourthP002Input2558 : RatPair2542 := ((((-((954 * 10^40
        + 4408235863513228586644187710188030184734) * 10^40
        + 9451418842310552107939719374824115518661)) : ℚ) /
        ((1019 * 10^40
        + 7878870730294030314197085150249093055010) * 10^40
        + 3865088414429925073481044335001600000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP002Center2558 : RatPair2542 := (((7079303255138996714707 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP002Error2558 : ℝ := ((1270094357691497131 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02701MinusFourthP002ExpUpper2558 : ℝ :=
    ((7783776245577814985017367540398763 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02701MinusFourthP002Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02701MinusFourthP002Upper2558 : ℝ := ((626426160582072021612586092855 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP002Exponent2558 : ℝ := (((-((954 * 10^40
        + 4408235863513228586644187710188030184734) * 10^40
        + 9451418842310552107939719374824115518661)) : ℝ) /
        ((15 * 10^40
        + 9341857355160844223659329455472642078984) * 10^40
        + 5372892006475467579273141317734400000000))

theorem batchC02701MinusFourthP002ExpBound2558 :
    Real.exp batchC02701MinusFourthP002Exponent2558 ≤ batchC02701MinusFourthP002ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP002Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP002Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP002Input2558 6).1 =
      batchC02701MinusFourthP002Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP002Input2558 6).2 : ℝ) =
      batchC02701MinusFourthP002Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP002Input2558 6).2 =
        ((1270094357691497131 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP002Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP002Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02701MinusFourthP002Input2558 =
      (batchC02701MinusFourthP002Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP002Input2558,
        batchC02701MinusFourthP002Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP002Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP002Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP002Center2558))).trans
  norm_num [batchC02701MinusFourthP002Error2558, batchC02701MinusFourthP002ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP002Center2558]

theorem batchC02701MinusFourthP002Bound2558 : batchC02701MinusFourthCell2558 ⟨2, by omega⟩ ≤
    batchC02701MinusFourthP002Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      batchC02701MinusFourthP002Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP002Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP002Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((127715799921782533419575077567987712 : ℝ) /
        178527459532142319574701358885546875) ((383305856092793980573141578954047488 : ℝ) /
        535582378596426958724104076656640625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP002ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP002Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((127715799921782533419575077567987712 : ℝ) /
        178527459532142319574701358885546875) ((383305856092793980573141578954047488 : ℝ) /
        535582378596426958724104076656640625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP002ExpUpper2558, batchC02701MinusFourthP002Frequency2558,
        batchC02701MinusFourthP002Upper2558]

def batchC02701MinusFourthP003Input2558 : RatPair2542 := ((((-((19946 * 10^40
        + 1562364617322071419749046517065707894108) * 10^40
        + 101515758605622181698242043252286524101)) : ℚ) /
        ((29500 * 10^40
        + 6544877282703875949311099885167444971256) * 10^40
        + 2870741502323415729587728685465600000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP003Center2558 : RatPair2542 := (((235496133224533901602178114065 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP003Error2558 : ℝ := ((32583769411003995748883247 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP003ExpUpper2558 : ℝ := (((25 * 10^40
        + 8930736776661058433276483586685699152687) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP003Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02701MinusFourthP003Upper2558 : ℝ :=
    ((491265195902332713803877422632473017 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02701MinusFourthP003Exponent2558 : ℝ := (((-((19946 * 10^40
        + 1562364617322071419749046517065707894108) * 10^40
        + 101515758605622181698242043252286524101)) : ℝ) /
        ((460 * 10^40
        + 9477263707542248061707985935705741327675) * 10^40
        + 8794855335973803370774808260710400000000))

theorem batchC02701MinusFourthP003ExpBound2558 :
    Real.exp batchC02701MinusFourthP003Exponent2558 ≤ batchC02701MinusFourthP003ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP003Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP003Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP003Input2558 6).1 =
      batchC02701MinusFourthP003Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP003Input2558 6).2 : ℝ) =
      batchC02701MinusFourthP003Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP003Input2558 6).2 =
        ((32583769411003995748883247 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP003Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP003Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02701MinusFourthP003Input2558 =
      (batchC02701MinusFourthP003Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP003Input2558,
        batchC02701MinusFourthP003Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP003Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP003Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP003Center2558))).trans
  norm_num [batchC02701MinusFourthP003Error2558, batchC02701MinusFourthP003ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP003Center2558]

theorem batchC02701MinusFourthP003Bound2558 : batchC02701MinusFourthCell2558 ⟨3, by omega⟩ ≤
    batchC02701MinusFourthP003Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      batchC02701MinusFourthP003Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP003Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP003Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP003ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP003Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP003ExpUpper2558, batchC02701MinusFourthP003Frequency2558,
        batchC02701MinusFourthP003Upper2558]

def batchC02701MinusFourthP004Input2558 : RatPair2542 := ((((-((2156 * 10^40
        + 5810707860331723215854195544925185416247) * 10^40
        + 2428719290236921442048233705878803018661)) : ℚ) /
        ((3723 * 10^40
        + 9003762708814383732722505768759897258427) * 10^40
        + 7850009650795845073481044335001600000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP004Center2558 : RatPair2542 := (((7314056913474520724846408633949 : ℚ)
    /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP004Error2558 : ℝ := ((14694887279485050564603307313 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP004ExpUpper2558 : ℝ := (((12867 * 10^40
        + 249961290841416124434120265373002786097) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP004Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02701MinusFourthP004Upper2558 : ℝ :=
    ((68418077913878457088667160427699458941 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC02701MinusFourthP004Exponent2558 : ℝ := (((-((2156 * 10^40
        + 5810707860331723215854195544925185416247) * 10^40
        + 2428719290236921442048233705878803018661)) : ℝ) /
        ((58 * 10^40
        + 1859433792325224745823789152636873394662) * 10^40
        + 9341406400793685079273141317734400000000))

theorem batchC02701MinusFourthP004ExpBound2558 :
    Real.exp batchC02701MinusFourthP004Exponent2558 ≤ batchC02701MinusFourthP004ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP004Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP004Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP004Input2558 6).1 =
      batchC02701MinusFourthP004Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP004Input2558 6).2 : ℝ) =
      batchC02701MinusFourthP004Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP004Input2558 6).2 =
        ((14694887279485050564603307313 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP004Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP004Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02701MinusFourthP004Input2558 =
      (batchC02701MinusFourthP004Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP004Input2558,
        batchC02701MinusFourthP004Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP004Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP004Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP004Center2558))).trans
  norm_num [batchC02701MinusFourthP004Error2558, batchC02701MinusFourthP004ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP004Center2558]

theorem batchC02701MinusFourthP004Bound2558 : batchC02701MinusFourthCell2558 ⟨4, by omega⟩ ≤
    batchC02701MinusFourthP004Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      batchC02701MinusFourthP004Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP004Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP004Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((127715799921782533419575077567987712 : ℝ) /
        270432128048689044069954655791796875) ((383305856092793980573141578954047488 : ℝ) /
        811296384146067132209863967375390625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP004ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP004Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((127715799921782533419575077567987712 : ℝ) /
        270432128048689044069954655791796875) ((383305856092793980573141578954047488 : ℝ) /
        811296384146067132209863967375390625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP004ExpUpper2558, batchC02701MinusFourthP004Frequency2558,
        batchC02701MinusFourthP004Upper2558]

def batchC02701MinusFourthP006Input2558 : RatPair2542 := ((((-31545171604873039881799668265918339)
    : ℚ) /
        55153625874169469420424396800000000),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP006Center2558 : RatPair2542 := (((23454073436934101 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP006Error2558 : ℝ := ((8047237053573 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP006ExpUpper2558 : ℝ := ((25788026462621264316590242949 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP006Frequency2558 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02701MinusFourthP006Upper2558 : ℝ := ((716715405356610904439711 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP006Exponent2558 : ℝ :=
    (((-31545171604873039881799668265918339) : ℝ)
    /
        430887702141948979847065600000000)

theorem batchC02701MinusFourthP006ExpBound2558 :
    Real.exp batchC02701MinusFourthP006Exponent2558 ≤ batchC02701MinusFourthP006ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP006Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP006Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP006Input2558 7).1 =
      batchC02701MinusFourthP006Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP006Input2558 7).2 : ℝ) =
      batchC02701MinusFourthP006Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP006Input2558 7).2 =
        ((8047237053573 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP006Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP006Input2558 hz 7
  rw [hc, he] at h
  have ha : (2 : ℂ)^7 * embedPair2542 batchC02701MinusFourthP006Input2558 =
      (batchC02701MinusFourthP006Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP006Input2558,
        batchC02701MinusFourthP006Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP006Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP006Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP006Center2558))).trans
  norm_num [batchC02701MinusFourthP006Error2558, batchC02701MinusFourthP006ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP006Center2558]

theorem batchC02701MinusFourthP006Bound2558 : batchC02701MinusFourthCell2558 ⟨6, by omega⟩ ≤
    batchC02701MinusFourthP006Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      batchC02701MinusFourthP006Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP006Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP006Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) ((79233025209 : ℝ) /
        102400000000) ((158531586419 : ℝ) /
        204800000000) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP006ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP006Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) ((79233025209 : ℝ) /
        102400000000) ((158531586419 : ℝ) /
        204800000000) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP006ExpUpper2558, batchC02701MinusFourthP006Frequency2558,
        batchC02701MinusFourthP006Upper2558]

def batchC02701MinusFourthP007Input2558 : RatPair2542 := ((((-((19946 * 10^40
        + 1562364617322071419749046517065707894108) * 10^40
        + 101515758605622181698242043252286524101)) : ℚ) /
        ((29500 * 10^40
        + 6544877282703875949311099885167444971256) * 10^40
        + 2870741502323415729587728685465600000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP007Center2558 : RatPair2542 := (((235496133224533901602178114065 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP007Error2558 : ℝ := ((32583769411003995748883247 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP007ExpUpper2558 : ℝ := (((25 * 10^40
        + 8930736776661058433276483586685699152687) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP007Frequency2558 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02701MinusFourthP007Upper2558 : ℝ := ((401413335568531436816828925907521 :
    ℝ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968))

noncomputable def batchC02701MinusFourthP007Exponent2558 : ℝ := (((-((19946 * 10^40
        + 1562364617322071419749046517065707894108) * 10^40
        + 101515758605622181698242043252286524101)) : ℝ) /
        ((460 * 10^40
        + 9477263707542248061707985935705741327675) * 10^40
        + 8794855335973803370774808260710400000000))

theorem batchC02701MinusFourthP007ExpBound2558 :
    Real.exp batchC02701MinusFourthP007Exponent2558 ≤ batchC02701MinusFourthP007ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP007Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP007Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP007Input2558 6).1 =
      batchC02701MinusFourthP007Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP007Input2558 6).2 : ℝ) =
      batchC02701MinusFourthP007Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP007Input2558 6).2 =
        ((32583769411003995748883247 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP007Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP007Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02701MinusFourthP007Input2558 =
      (batchC02701MinusFourthP007Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP007Input2558,
        batchC02701MinusFourthP007Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP007Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP007Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP007Center2558))).trans
  norm_num [batchC02701MinusFourthP007Error2558, batchC02701MinusFourthP007ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP007Center2558]

theorem batchC02701MinusFourthP007Bound2558 : batchC02701MinusFourthCell2558 ⟨7, by omega⟩ ≤
    batchC02701MinusFourthP007Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      batchC02701MinusFourthP007Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP007Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP007Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP007ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP007Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP007ExpUpper2558, batchC02701MinusFourthP007Frequency2558,
        batchC02701MinusFourthP007Upper2558]

def batchC02701MinusFourthP008Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP008Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP008Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP008ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP008Frequency2558 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def batchC02701MinusFourthP008Upper2558 : ℝ := ((5909173563002281060698845961 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP008Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP008ExpBound2558 :
    Real.exp batchC02701MinusFourthP008Exponent2558 ≤ batchC02701MinusFourthP008ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP008Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP008Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP008Input2558 15).1 =
      batchC02701MinusFourthP008Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP008Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP008Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP008Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP008Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP008Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP008Input2558 =
      (batchC02701MinusFourthP008Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP008Input2558,
        batchC02701MinusFourthP008Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP008Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP008Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP008Center2558))).trans
  norm_num [batchC02701MinusFourthP008Error2558, batchC02701MinusFourthP008ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP008Center2558]

theorem batchC02701MinusFourthP008Bound2558 : batchC02701MinusFourthCell2558 ⟨8, by omega⟩ ≤
    batchC02701MinusFourthP008Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      batchC02701MinusFourthP008Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP008Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP008Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP008ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP008Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP008ExpUpper2558, batchC02701MinusFourthP008Frequency2558,
        batchC02701MinusFourthP008Upper2558]

def batchC02701MinusFourthP009Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP009Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP009Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP009ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP009Frequency2558 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def batchC02701MinusFourthP009Upper2558 : ℝ := ((5909195049938260179575100899 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP009Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP009ExpBound2558 :
    Real.exp batchC02701MinusFourthP009Exponent2558 ≤ batchC02701MinusFourthP009ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP009Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP009Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP009Input2558 15).1 =
      batchC02701MinusFourthP009Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP009Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP009Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP009Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP009Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP009Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP009Input2558 =
      (batchC02701MinusFourthP009Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP009Input2558,
        batchC02701MinusFourthP009Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP009Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP009Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP009Center2558))).trans
  norm_num [batchC02701MinusFourthP009Error2558, batchC02701MinusFourthP009ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP009Center2558]

theorem batchC02701MinusFourthP009Bound2558 : batchC02701MinusFourthCell2558 ⟨9, by omega⟩ ≤
    batchC02701MinusFourthP009Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      batchC02701MinusFourthP009Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP009Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP009Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP009ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP009Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP009ExpUpper2558, batchC02701MinusFourthP009Frequency2558,
        batchC02701MinusFourthP009Upper2558]

def batchC02701MinusFourthP010Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP010Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP010Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP010ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP010Frequency2558 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def batchC02701MinusFourthP010Upper2558 : ℝ := ((5909207496492113742843870253 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP010Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP010ExpBound2558 :
    Real.exp batchC02701MinusFourthP010Exponent2558 ≤ batchC02701MinusFourthP010ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP010Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP010Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP010Input2558 15).1 =
      batchC02701MinusFourthP010Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP010Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP010Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP010Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP010Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP010Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP010Input2558 =
      (batchC02701MinusFourthP010Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP010Input2558,
        batchC02701MinusFourthP010Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP010Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP010Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP010Center2558))).trans
  norm_num [batchC02701MinusFourthP010Error2558, batchC02701MinusFourthP010ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP010Center2558]

theorem batchC02701MinusFourthP010Bound2558 : batchC02701MinusFourthCell2558 ⟨10, by omega⟩ ≤
    batchC02701MinusFourthP010Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      batchC02701MinusFourthP010Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP010Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP010Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP010ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP010Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP010ExpUpper2558, batchC02701MinusFourthP010Frequency2558,
        batchC02701MinusFourthP010Upper2558]

def batchC02701MinusFourthP011Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP011Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP011Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP011ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP011Frequency2558 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def batchC02701MinusFourthP011Upper2558 : ℝ := ((92331496804173259513001223 : ℝ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984))

noncomputable def batchC02701MinusFourthP011Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP011ExpBound2558 :
    Real.exp batchC02701MinusFourthP011Exponent2558 ≤ batchC02701MinusFourthP011ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP011Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP011Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP011Input2558 15).1 =
      batchC02701MinusFourthP011Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP011Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP011Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP011Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP011Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP011Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP011Input2558 =
      (batchC02701MinusFourthP011Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP011Input2558,
        batchC02701MinusFourthP011Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP011Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP011Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP011Center2558))).trans
  norm_num [batchC02701MinusFourthP011Error2558, batchC02701MinusFourthP011ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP011Center2558]

theorem batchC02701MinusFourthP011Bound2558 : batchC02701MinusFourthCell2558 ⟨11, by omega⟩ ≤
    batchC02701MinusFourthP011Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      batchC02701MinusFourthP011Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP011Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP011Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP011ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP011Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP011ExpUpper2558, batchC02701MinusFourthP011Frequency2558,
        batchC02701MinusFourthP011Upper2558]

def batchC02701MinusFourthP012Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP012Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP012Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP012ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP012Frequency2558 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def batchC02701MinusFourthP012Upper2558 : ℝ := ((5909224391459577560014098539 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP012Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP012ExpBound2558 :
    Real.exp batchC02701MinusFourthP012Exponent2558 ≤ batchC02701MinusFourthP012ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP012Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP012Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP012Input2558 15).1 =
      batchC02701MinusFourthP012Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP012Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP012Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP012Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP012Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP012Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP012Input2558 =
      (batchC02701MinusFourthP012Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP012Input2558,
        batchC02701MinusFourthP012Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP012Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP012Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP012Center2558))).trans
  norm_num [batchC02701MinusFourthP012Error2558, batchC02701MinusFourthP012ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP012Center2558]

theorem batchC02701MinusFourthP012Bound2558 : batchC02701MinusFourthCell2558 ⟨12, by omega⟩ ≤
    batchC02701MinusFourthP012Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      batchC02701MinusFourthP012Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP012Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP012Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP012ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP012Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP012ExpUpper2558, batchC02701MinusFourthP012Frequency2558,
        batchC02701MinusFourthP012Upper2558]

def batchC02701MinusFourthP013Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP013Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP013Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP013ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP013Frequency2558 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def batchC02701MinusFourthP013Upper2558 : ℝ := ((5909232225057521861936677647 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP013Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP013ExpBound2558 :
    Real.exp batchC02701MinusFourthP013Exponent2558 ≤ batchC02701MinusFourthP013ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP013Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP013Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP013Input2558 15).1 =
      batchC02701MinusFourthP013Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP013Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP013Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP013Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP013Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP013Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP013Input2558 =
      (batchC02701MinusFourthP013Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP013Input2558,
        batchC02701MinusFourthP013Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP013Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP013Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP013Center2558))).trans
  norm_num [batchC02701MinusFourthP013Error2558, batchC02701MinusFourthP013ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP013Center2558]

theorem batchC02701MinusFourthP013Bound2558 : batchC02701MinusFourthCell2558 ⟨13, by omega⟩ ≤
    batchC02701MinusFourthP013Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      batchC02701MinusFourthP013Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP013Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP013Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP013ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP013Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP013ExpUpper2558, batchC02701MinusFourthP013Frequency2558,
        batchC02701MinusFourthP013Upper2558]

def batchC02701MinusFourthP014Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP014Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP014Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP014ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP014Frequency2558 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def batchC02701MinusFourthP014Upper2558 : ℝ := ((2954623370138946023806003689 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02701MinusFourthP014Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP014ExpBound2558 :
    Real.exp batchC02701MinusFourthP014Exponent2558 ≤ batchC02701MinusFourthP014ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP014Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP014Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP014Input2558 15).1 =
      batchC02701MinusFourthP014Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP014Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP014Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP014Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP014Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP014Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP014Input2558 =
      (batchC02701MinusFourthP014Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP014Input2558,
        batchC02701MinusFourthP014Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP014Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP014Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP014Center2558))).trans
  norm_num [batchC02701MinusFourthP014Error2558, batchC02701MinusFourthP014ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP014Center2558]

theorem batchC02701MinusFourthP014Bound2558 : batchC02701MinusFourthCell2558 ⟨14, by omega⟩ ≤
    batchC02701MinusFourthP014Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      batchC02701MinusFourthP014Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP014Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP014Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP014ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP014Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP014ExpUpper2558, batchC02701MinusFourthP014Frequency2558,
        batchC02701MinusFourthP014Upper2558]

def batchC02701MinusFourthP015Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP015Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP015Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP015ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP015Frequency2558 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def batchC02701MinusFourthP015Upper2558 : ℝ := ((2954628570352075329484660245 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02701MinusFourthP015Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP015ExpBound2558 :
    Real.exp batchC02701MinusFourthP015Exponent2558 ≤ batchC02701MinusFourthP015ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP015Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP015Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP015Input2558 15).1 =
      batchC02701MinusFourthP015Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP015Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP015Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP015Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP015Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP015Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP015Input2558 =
      (batchC02701MinusFourthP015Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP015Input2558,
        batchC02701MinusFourthP015Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP015Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP015Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP015Center2558))).trans
  norm_num [batchC02701MinusFourthP015Error2558, batchC02701MinusFourthP015ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP015Center2558]

theorem batchC02701MinusFourthP015Bound2558 : batchC02701MinusFourthCell2558 ⟨15, by omega⟩ ≤
    batchC02701MinusFourthP015Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      batchC02701MinusFourthP015Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP015Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP015Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP015ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP015Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP015ExpUpper2558, batchC02701MinusFourthP015Frequency2558,
        batchC02701MinusFourthP015Upper2558]

def batchC02701MinusFourthP016Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP016Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP016Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP016ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP016Frequency2558 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def batchC02701MinusFourthP016Upper2558 : ℝ := ((2954632328476960164631006819 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02701MinusFourthP016Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP016ExpBound2558 :
    Real.exp batchC02701MinusFourthP016Exponent2558 ≤ batchC02701MinusFourthP016ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP016Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP016Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP016Input2558 15).1 =
      batchC02701MinusFourthP016Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP016Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP016Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP016Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP016Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP016Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP016Input2558 =
      (batchC02701MinusFourthP016Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP016Input2558,
        batchC02701MinusFourthP016Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP016Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP016Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP016Center2558))).trans
  norm_num [batchC02701MinusFourthP016Error2558, batchC02701MinusFourthP016ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP016Center2558]

theorem batchC02701MinusFourthP016Bound2558 : batchC02701MinusFourthCell2558 ⟨16, by omega⟩ ≤
    batchC02701MinusFourthP016Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      batchC02701MinusFourthP016Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP016Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP016Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP016ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP016Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP016ExpUpper2558, batchC02701MinusFourthP016Frequency2558,
        batchC02701MinusFourthP016Upper2558]

def batchC02701MinusFourthP017Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP017Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP017Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP017ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP017Frequency2558 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def batchC02701MinusFourthP017Upper2558 : ℝ := ((5909279256971808120426219925 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP017Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP017ExpBound2558 :
    Real.exp batchC02701MinusFourthP017Exponent2558 ≤ batchC02701MinusFourthP017ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP017Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP017Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP017Input2558 15).1 =
      batchC02701MinusFourthP017Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP017Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP017Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP017Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP017Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP017Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP017Input2558 =
      (batchC02701MinusFourthP017Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP017Input2558,
        batchC02701MinusFourthP017Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP017Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP017Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP017Center2558))).trans
  norm_num [batchC02701MinusFourthP017Error2558, batchC02701MinusFourthP017ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP017Center2558]

theorem batchC02701MinusFourthP017Bound2558 : batchC02701MinusFourthCell2558 ⟨17, by omega⟩ ≤
    batchC02701MinusFourthP017Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      batchC02701MinusFourthP017Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP017Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP017Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP017ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP017Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP017ExpUpper2558, batchC02701MinusFourthP017Frequency2558,
        batchC02701MinusFourthP017Upper2558]

def batchC02701MinusFourthP018Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP018Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP018Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP018ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP018Frequency2558 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def batchC02701MinusFourthP018Upper2558 : ℝ := ((5909284776977974914640013257 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP018Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP018ExpBound2558 :
    Real.exp batchC02701MinusFourthP018Exponent2558 ≤ batchC02701MinusFourthP018ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP018Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP018Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP018Input2558 15).1 =
      batchC02701MinusFourthP018Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP018Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP018Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP018Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP018Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP018Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP018Input2558 =
      (batchC02701MinusFourthP018Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP018Input2558,
        batchC02701MinusFourthP018Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP018Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP018Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP018Center2558))).trans
  norm_num [batchC02701MinusFourthP018Error2558, batchC02701MinusFourthP018ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP018Center2558]

theorem batchC02701MinusFourthP018Bound2558 : batchC02701MinusFourthCell2558 ⟨18, by omega⟩ ≤
    batchC02701MinusFourthP018Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      batchC02701MinusFourthP018Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP018Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP018Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP018ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP018Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP018ExpUpper2558, batchC02701MinusFourthP018Frequency2558,
        batchC02701MinusFourthP018Upper2558]

def batchC02701MinusFourthP019Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP019Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP019Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP019ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP019Frequency2558 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def batchC02701MinusFourthP019Upper2558 : ℝ := ((5909294753190229834671786109 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP019Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP019ExpBound2558 :
    Real.exp batchC02701MinusFourthP019Exponent2558 ≤ batchC02701MinusFourthP019ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP019Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP019Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP019Input2558 15).1 =
      batchC02701MinusFourthP019Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP019Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP019Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP019Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP019Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP019Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP019Input2558 =
      (batchC02701MinusFourthP019Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP019Input2558,
        batchC02701MinusFourthP019Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP019Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP019Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP019Center2558))).trans
  norm_num [batchC02701MinusFourthP019Error2558, batchC02701MinusFourthP019ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP019Center2558]

theorem batchC02701MinusFourthP019Bound2558 : batchC02701MinusFourthCell2558 ⟨19, by omega⟩ ≤
    batchC02701MinusFourthP019Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      batchC02701MinusFourthP019Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP019Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP019Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP019ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP019Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP019ExpUpper2558, batchC02701MinusFourthP019Frequency2558,
        batchC02701MinusFourthP019Upper2558]

def batchC02701MinusFourthP020Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP020Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP020Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP020ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP020Frequency2558 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def batchC02701MinusFourthP020Upper2558 : ℝ := ((2954652800799345591304433769 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02701MinusFourthP020Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP020ExpBound2558 :
    Real.exp batchC02701MinusFourthP020Exponent2558 ≤ batchC02701MinusFourthP020ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP020Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP020Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP020Input2558 15).1 =
      batchC02701MinusFourthP020Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP020Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP020Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP020Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP020Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP020Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP020Input2558 =
      (batchC02701MinusFourthP020Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP020Input2558,
        batchC02701MinusFourthP020Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP020Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP020Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP020Center2558))).trans
  norm_num [batchC02701MinusFourthP020Error2558, batchC02701MinusFourthP020ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP020Center2558]

theorem batchC02701MinusFourthP020Bound2558 : batchC02701MinusFourthCell2558 ⟨20, by omega⟩ ≤
    batchC02701MinusFourthP020Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      batchC02701MinusFourthP020Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP020Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP020Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP020ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP020Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP020ExpUpper2558, batchC02701MinusFourthP020Frequency2558,
        batchC02701MinusFourthP020Upper2558]

def batchC02701MinusFourthP021Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP021Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP021Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP021ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP021Frequency2558 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def batchC02701MinusFourthP021Upper2558 : ℝ := ((1477328663767956256761638021 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02701MinusFourthP021Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP021ExpBound2558 :
    Real.exp batchC02701MinusFourthP021Exponent2558 ≤ batchC02701MinusFourthP021ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP021Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP021Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP021Input2558 15).1 =
      batchC02701MinusFourthP021Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP021Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP021Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP021Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP021Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP021Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP021Input2558 =
      (batchC02701MinusFourthP021Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP021Input2558,
        batchC02701MinusFourthP021Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP021Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP021Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP021Center2558))).trans
  norm_num [batchC02701MinusFourthP021Error2558, batchC02701MinusFourthP021ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP021Center2558]

theorem batchC02701MinusFourthP021Bound2558 : batchC02701MinusFourthCell2558 ⟨21, by omega⟩ ≤
    batchC02701MinusFourthP021Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      batchC02701MinusFourthP021Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP021Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP021Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP021ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP021Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP021ExpUpper2558, batchC02701MinusFourthP021Frequency2558,
        batchC02701MinusFourthP021Upper2558]

def batchC02701MinusFourthP022Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP022Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP022Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP022ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP022Frequency2558 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def batchC02701MinusFourthP022Upper2558 : ℝ := ((5909319288989766954684515467 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP022Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP022ExpBound2558 :
    Real.exp batchC02701MinusFourthP022Exponent2558 ≤ batchC02701MinusFourthP022ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP022Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP022Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP022Input2558 15).1 =
      batchC02701MinusFourthP022Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP022Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP022Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP022Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP022Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP022Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP022Input2558 =
      (batchC02701MinusFourthP022Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP022Input2558,
        batchC02701MinusFourthP022Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP022Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP022Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP022Center2558))).trans
  norm_num [batchC02701MinusFourthP022Error2558, batchC02701MinusFourthP022ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP022Center2558]

theorem batchC02701MinusFourthP022Bound2558 : batchC02701MinusFourthCell2558 ⟨22, by omega⟩ ≤
    batchC02701MinusFourthP022Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      batchC02701MinusFourthP022Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP022Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP022Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP022ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP022Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP022ExpUpper2558, batchC02701MinusFourthP022Frequency2558,
        batchC02701MinusFourthP022Upper2558]

def batchC02701MinusFourthP023Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP023Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP023Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP023ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP023Frequency2558 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def batchC02701MinusFourthP023Upper2558 : ℝ := ((5909332649492632842648795565 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP023Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP023ExpBound2558 :
    Real.exp batchC02701MinusFourthP023Exponent2558 ≤ batchC02701MinusFourthP023ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP023Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP023Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP023Input2558 15).1 =
      batchC02701MinusFourthP023Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP023Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP023Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP023Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP023Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP023Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP023Input2558 =
      (batchC02701MinusFourthP023Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP023Input2558,
        batchC02701MinusFourthP023Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP023Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP023Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP023Center2558))).trans
  norm_num [batchC02701MinusFourthP023Error2558, batchC02701MinusFourthP023ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP023Center2558]

theorem batchC02701MinusFourthP023Bound2558 : batchC02701MinusFourthCell2558 ⟨23, by omega⟩ ≤
    batchC02701MinusFourthP023Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      batchC02701MinusFourthP023Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP023Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP023Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP023ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP023Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP023ExpUpper2558, batchC02701MinusFourthP023Frequency2558,
        batchC02701MinusFourthP023Upper2558]

def batchC02701MinusFourthP024Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP024Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP024Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP024ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP024Frequency2558 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def batchC02701MinusFourthP024Upper2558 : ℝ := ((5909338789464419944217059477 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP024Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP024ExpBound2558 :
    Real.exp batchC02701MinusFourthP024Exponent2558 ≤ batchC02701MinusFourthP024ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP024Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP024Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP024Input2558 15).1 =
      batchC02701MinusFourthP024Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP024Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP024Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP024Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP024Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP024Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP024Input2558 =
      (batchC02701MinusFourthP024Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP024Input2558,
        batchC02701MinusFourthP024Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP024Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP024Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP024Center2558))).trans
  norm_num [batchC02701MinusFourthP024Error2558, batchC02701MinusFourthP024ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP024Center2558]

theorem batchC02701MinusFourthP024Bound2558 : batchC02701MinusFourthCell2558 ⟨24, by omega⟩ ≤
    batchC02701MinusFourthP024Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      batchC02701MinusFourthP024Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP024Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP024Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP024ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP024Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP024ExpUpper2558, batchC02701MinusFourthP024Frequency2558,
        batchC02701MinusFourthP024Upper2558]

def batchC02701MinusFourthP025Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP025Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP025Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP025ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP025Frequency2558 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def batchC02701MinusFourthP025Upper2558 : ℝ := ((5909346487883247116836575453 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP025Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP025ExpBound2558 :
    Real.exp batchC02701MinusFourthP025Exponent2558 ≤ batchC02701MinusFourthP025ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP025Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP025Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP025Input2558 15).1 =
      batchC02701MinusFourthP025Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP025Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP025Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP025Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP025Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP025Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP025Input2558 =
      (batchC02701MinusFourthP025Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP025Input2558,
        batchC02701MinusFourthP025Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP025Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP025Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP025Center2558))).trans
  norm_num [batchC02701MinusFourthP025Error2558, batchC02701MinusFourthP025ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP025Center2558]

theorem batchC02701MinusFourthP025Bound2558 : batchC02701MinusFourthCell2558 ⟨25, by omega⟩ ≤
    batchC02701MinusFourthP025Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      batchC02701MinusFourthP025Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP025Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP025Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP025ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP025Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP025ExpUpper2558, batchC02701MinusFourthP025Frequency2558,
        batchC02701MinusFourthP025Upper2558]

def batchC02701MinusFourthP026Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP026Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP026Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP026ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP026Frequency2558 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def batchC02701MinusFourthP026Upper2558 : ℝ := ((5909354355376910988070849507 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP026Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP026ExpBound2558 :
    Real.exp batchC02701MinusFourthP026Exponent2558 ≤ batchC02701MinusFourthP026ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP026Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP026Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP026Input2558 15).1 =
      batchC02701MinusFourthP026Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP026Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP026Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP026Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP026Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP026Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP026Input2558 =
      (batchC02701MinusFourthP026Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP026Input2558,
        batchC02701MinusFourthP026Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP026Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP026Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP026Center2558))).trans
  norm_num [batchC02701MinusFourthP026Error2558, batchC02701MinusFourthP026ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP026Center2558]

theorem batchC02701MinusFourthP026Bound2558 : batchC02701MinusFourthCell2558 ⟨26, by omega⟩ ≤
    batchC02701MinusFourthP026Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      batchC02701MinusFourthP026Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP026Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP026Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP026ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP026Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP026ExpUpper2558, batchC02701MinusFourthP026Frequency2558,
        batchC02701MinusFourthP026Upper2558]

def batchC02701MinusFourthP027Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP027Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP027Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP027ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP027Frequency2558 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def batchC02701MinusFourthP027Upper2558 : ℝ := ((1477341427115933043002903169 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02701MinusFourthP027Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP027ExpBound2558 :
    Real.exp batchC02701MinusFourthP027Exponent2558 ≤ batchC02701MinusFourthP027ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP027Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP027Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP027Input2558 15).1 =
      batchC02701MinusFourthP027Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP027Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP027Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP027Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP027Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP027Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP027Input2558 =
      (batchC02701MinusFourthP027Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP027Input2558,
        batchC02701MinusFourthP027Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP027Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP027Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP027Center2558))).trans
  norm_num [batchC02701MinusFourthP027Error2558, batchC02701MinusFourthP027ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP027Center2558]

theorem batchC02701MinusFourthP027Bound2558 : batchC02701MinusFourthCell2558 ⟨27, by omega⟩ ≤
    batchC02701MinusFourthP027Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      batchC02701MinusFourthP027Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP027Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP027Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP027ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP027Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP027ExpUpper2558, batchC02701MinusFourthP027Frequency2558,
        batchC02701MinusFourthP027Upper2558]

def batchC02701MinusFourthP028Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP028Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP028Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP028ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP028Frequency2558 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def batchC02701MinusFourthP028Upper2558 : ℝ := ((5909370203318340831251978527 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP028Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP028ExpBound2558 :
    Real.exp batchC02701MinusFourthP028Exponent2558 ≤ batchC02701MinusFourthP028ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP028Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP028Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP028Input2558 15).1 =
      batchC02701MinusFourthP028Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP028Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP028Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP028Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP028Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP028Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP028Input2558 =
      (batchC02701MinusFourthP028Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP028Input2558,
        batchC02701MinusFourthP028Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP028Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP028Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP028Center2558))).trans
  norm_num [batchC02701MinusFourthP028Error2558, batchC02701MinusFourthP028ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP028Center2558]

theorem batchC02701MinusFourthP028Bound2558 : batchC02701MinusFourthCell2558 ⟨28, by omega⟩ ≤
    batchC02701MinusFourthP028Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      batchC02701MinusFourthP028Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP028Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP028Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP028ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP028Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP028ExpUpper2558, batchC02701MinusFourthP028Frequency2558,
        batchC02701MinusFourthP028Upper2558]

def batchC02701MinusFourthP029Input2558 : RatPair2542 := ((((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℚ) /
        ((2086877 * 10^40
        + 683672164435489381003336168428151087122) * 10^40
        + 6847815307670681766987695967436800000000)),
    ((0 : ℚ) /
        1))

def batchC02701MinusFourthP029Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusFourthP029Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP029ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02701MinusFourthP029Frequency2558 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def batchC02701MinusFourthP029Upper2558 : ℝ := ((5909377046457567147687827547 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02701MinusFourthP029Exponent2558 : ℝ := (((-((1156309 * 10^40
        + 3499483886644713503833447474676575117313) * 10^40
        + 9913209647017028650445897621648141323069)) : ℝ) /
        ((63 * 10^40
        + 6864339711674940047893707377202405644259) * 10^40
        + 2505702142801137410942596060057600000000))

theorem batchC02701MinusFourthP029ExpBound2558 :
    Real.exp batchC02701MinusFourthP029Exponent2558 ≤ batchC02701MinusFourthP029ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02701MinusFourthP029Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02701MinusFourthP029Input2558]
  have hc : (compactExp2547 batchC02701MinusFourthP029Input2558 15).1 =
      batchC02701MinusFourthP029Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02701MinusFourthP029Input2558 15).2 : ℝ) =
      batchC02701MinusFourthP029Error2558 := by
    have hq : (compactExp2547 batchC02701MinusFourthP029Input2558 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02701MinusFourthP029Error2558]
  have h := compactExp_error2547 batchC02701MinusFourthP029Input2558 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 batchC02701MinusFourthP029Input2558 =
      (batchC02701MinusFourthP029Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02701MinusFourthP029Input2558,
        batchC02701MinusFourthP029Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02701MinusFourthP029Exponent2558 : ℂ)) (embedPair2542
        batchC02701MinusFourthP029Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02701MinusFourthP029Center2558))).trans
  norm_num [batchC02701MinusFourthP029Error2558, batchC02701MinusFourthP029ExpUpper2558,
      pairMagnitude2542,
      batchC02701MinusFourthP029Center2558]

theorem batchC02701MinusFourthP029Bound2558 : batchC02701MinusFourthCell2558 ⟨29, by omega⟩ ≤
    batchC02701MinusFourthP029Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      batchC02701MinusFourthP029Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02701MinusFourthP029Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02701MinusFourthP029Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02701MinusFourthP029ExpBound2558 using 1; norm_num
        [batchC02701MinusFourthP029Exponent2558])
  have hid : batchC02701MinusFourthCell2558 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [batchC02701MinusFourthCell2558, cellNearAbs2538, kernelN02701MinusPosition2555,
      batchN02702MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02701MinusFourthP029ExpUpper2558, batchC02701MinusFourthP029Frequency2558,
        batchC02701MinusFourthP029Upper2558]

noncomputable def batchC02701MinusFourthP000Upper2558 : ℝ := 0

theorem batchC02701MinusFourthP000Bound2558 :
    batchC02701MinusFourthCell2558 ⟨0, by omega⟩ ≤ batchC02701MinusFourthP000Upper2558 := by
  norm_num [batchC02701MinusFourthCell2558, batchC02701MinusFourthP000Upper2558, cellNearAbs2538,
    kernelN02701MinusPosition2555, batchN02702MinusPosition2558, storedWidth]

noncomputable def batchC02701MinusFourthP005Upper2558 : ℝ := 0

theorem batchC02701MinusFourthP005Bound2558 :
    batchC02701MinusFourthCell2558 ⟨5, by omega⟩ ≤ batchC02701MinusFourthP005Upper2558 := by
  norm_num [batchC02701MinusFourthCell2558, batchC02701MinusFourthP005Upper2558, cellNearAbs2538,
    kernelN02701MinusPosition2555, batchN02702MinusPosition2558, storedWidth]

noncomputable def batchC02701MinusFourthUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02701MinusFourthP000Upper2558
  | 1 => batchC02701MinusFourthP001Upper2558
  | 2 => batchC02701MinusFourthP002Upper2558
  | 3 => batchC02701MinusFourthP003Upper2558
  | 4 => batchC02701MinusFourthP004Upper2558
  | 5 => batchC02701MinusFourthP005Upper2558
  | 6 => batchC02701MinusFourthP006Upper2558
  | 7 => batchC02701MinusFourthP007Upper2558
  | 8 => batchC02701MinusFourthP008Upper2558
  | 9 => batchC02701MinusFourthP009Upper2558
  | 10 => batchC02701MinusFourthP010Upper2558
  | 11 => batchC02701MinusFourthP011Upper2558
  | 12 => batchC02701MinusFourthP012Upper2558
  | 13 => batchC02701MinusFourthP013Upper2558
  | 14 => batchC02701MinusFourthP014Upper2558
  | 15 => batchC02701MinusFourthP015Upper2558
  | 16 => batchC02701MinusFourthP016Upper2558
  | 17 => batchC02701MinusFourthP017Upper2558
  | 18 => batchC02701MinusFourthP018Upper2558
  | 19 => batchC02701MinusFourthP019Upper2558
  | 20 => batchC02701MinusFourthP020Upper2558
  | 21 => batchC02701MinusFourthP021Upper2558
  | 22 => batchC02701MinusFourthP022Upper2558
  | 23 => batchC02701MinusFourthP023Upper2558
  | 24 => batchC02701MinusFourthP024Upper2558
  | 25 => batchC02701MinusFourthP025Upper2558
  | 26 => batchC02701MinusFourthP026Upper2558
  | 27 => batchC02701MinusFourthP027Upper2558
  | 28 => batchC02701MinusFourthP028Upper2558
  | 29 => batchC02701MinusFourthP029Upper2558
  | _ => 0

theorem batchC02701MinusFourthBound2558 (i : Fin 30) :
    batchC02701MinusFourthCell2558 i ≤ batchC02701MinusFourthUpper2558 i := by
  fin_cases i
  · exact batchC02701MinusFourthP000Bound2558
  · exact batchC02701MinusFourthP001Bound2558
  · exact batchC02701MinusFourthP002Bound2558
  · exact batchC02701MinusFourthP003Bound2558
  · exact batchC02701MinusFourthP004Bound2558
  · exact batchC02701MinusFourthP005Bound2558
  · exact batchC02701MinusFourthP006Bound2558
  · exact batchC02701MinusFourthP007Bound2558
  · exact batchC02701MinusFourthP008Bound2558
  · exact batchC02701MinusFourthP009Bound2558
  · exact batchC02701MinusFourthP010Bound2558
  · exact batchC02701MinusFourthP011Bound2558
  · exact batchC02701MinusFourthP012Bound2558
  · exact batchC02701MinusFourthP013Bound2558
  · exact batchC02701MinusFourthP014Bound2558
  · exact batchC02701MinusFourthP015Bound2558
  · exact batchC02701MinusFourthP016Bound2558
  · exact batchC02701MinusFourthP017Bound2558
  · exact batchC02701MinusFourthP018Bound2558
  · exact batchC02701MinusFourthP019Bound2558
  · exact batchC02701MinusFourthP020Bound2558
  · exact batchC02701MinusFourthP021Bound2558
  · exact batchC02701MinusFourthP022Bound2558
  · exact batchC02701MinusFourthP023Bound2558
  · exact batchC02701MinusFourthP024Bound2558
  · exact batchC02701MinusFourthP025Bound2558
  · exact batchC02701MinusFourthP026Bound2558
  · exact batchC02701MinusFourthP027Bound2558
  · exact batchC02701MinusFourthP028Bound2558
  · exact batchC02701MinusFourthP029Bound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP001Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP002Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP003Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP004Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP006Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP007Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP008Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP009Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP010Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP011Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP012Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP013Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP014Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP015Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP016Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP017Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP018Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP019Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP020Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP021Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP022Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP023Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP024Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP025Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP026Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP027Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP028Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP029Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthBound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP000Bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusFourthP005Bound2558
