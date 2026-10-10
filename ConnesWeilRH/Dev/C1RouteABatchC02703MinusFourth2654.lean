import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteABatchN02703Minus2654
import ConnesWeilRH.Dev.C1RouteABatchN02704Minus2654

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC02703MinusFourthCell2654 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 batchN02703MinusPosition2654 batchN02704MinusPosition2654 < storedWidth i ^ 2
      then
    weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 batchN02703MinusPosition2654 batchN02704MinusPosition2654 / (storedWidth i
          ^ 2))
      (min (max |batchN02703MinusPosition2654| |batchN02704MinusPosition2654|) (storedWidth i ^ 2)
          /
        (storedWidth i ^ 2)) batchN02703MinusPosition2654 batchN02704MinusPosition2654
  else 0


def batchC02703MinusFourthP001Input2654 : RatPair2542 := ((((-((334 * 10^40
        + 3844663563069152511389243214239772779905) * 10^40
        + 5207479036744472686393889119222641561263)) : ℚ) /
        ((476 * 10^40
        + 7721195439100688856867675854751165291712) * 10^40
        + 4546667757873764492725530420838400000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP001Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP001Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP001ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP001Frequency2654 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02703MinusFourthP001Upper2654 : ℝ := ((351072401719 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP001Exponent2654 : ℝ := (((-((334 * 10^40
        + 3844663563069152511389243214239772779905) * 10^40
        + 5207479036744472686393889119222641561263)) : ℝ) /
        ((1 * 10^40
        + 8623910919683987065847139358807621739420) * 10^40
        + 7517760420929194392549709103206400000000))

theorem batchC02703MinusFourthP001ExpBound2654 :
    Real.exp batchC02703MinusFourthP001Exponent2654 ≤ batchC02703MinusFourthP001ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP001Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP001Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP001Input2654 8).1 =
      batchC02703MinusFourthP001Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP001Input2654 8).2 : ℝ) =
      batchC02703MinusFourthP001Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP001Input2654 8).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP001Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP001Input2654 hz 8
  rw [hc, he] at h
  have ha : (2 : ℂ)^8 * embedPair2542 batchC02703MinusFourthP001Input2654 =
      (batchC02703MinusFourthP001Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP001Input2654,
        batchC02703MinusFourthP001Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP001Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP001Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP001Center2654))).trans
  norm_num [batchC02703MinusFourthP001Error2654, batchC02703MinusFourthP001ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP001Center2654]

theorem batchC02703MinusFourthP001Bound2654 : batchC02703MinusFourthCell2654 ⟨1, by omega⟩ ≤
    batchC02703MinusFourthP001Upper2654 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      batchC02703MinusFourthP001Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP001Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP001Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((95707621777613709907473135050948608 : ℝ) /
        104779244925114570282650713456640625) ((95747235859475304986077221613469696 : ℝ) /
        104779244925114570282650713456640625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP001ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP001Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((95707621777613709907473135050948608 : ℝ) /
        104779244925114570282650713456640625) ((95747235859475304986077221613469696 : ℝ) /
        104779244925114570282650713456640625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP001ExpUpper2654, batchC02703MinusFourthP001Frequency2654,
        batchC02703MinusFourthP001Upper2654]

def batchC02703MinusFourthP002Input2654 : RatPair2542 := ((((-((8589 * 10^40
        + 7664598831197337581691451946139900081831) * 10^40
        + 1035426890814080362307585419128427089583)) : ℚ) /
        ((9193 * 10^40
        + 9997222029422076241207779631573162323809) * 10^40
        + 5411622062511522970902121683353600000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP002Center2654 : RatPair2542 := (((15726811592362811858003 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP002Error2654 : ℝ := ((1408456071729877091 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02703MinusFourthP002ExpUpper2654 : ℝ :=
    ((8645906106822652326436728481222755 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02703MinusFourthP002Frequency2654 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02703MinusFourthP002Upper2654 : ℝ := ((172405265909765307548800798367 : ℝ)
    /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02703MinusFourthP002Exponent2654 : ℝ := (((-((8589 * 10^40
        + 7664598831197337581691451946139900081831) * 10^40
        + 1035426890814080362307585419128427089583)) : ℝ) /
        ((143 * 10^40
        + 6562456594209719941268871556743330661309) * 10^40
        + 5240806594726742546420345651302400000000))

theorem batchC02703MinusFourthP002ExpBound2654 :
    Real.exp batchC02703MinusFourthP002Exponent2654 ≤ batchC02703MinusFourthP002ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP002Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP002Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP002Input2654 6).1 =
      batchC02703MinusFourthP002Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP002Input2654 6).2 : ℝ) =
      batchC02703MinusFourthP002Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP002Input2654 6).2 =
        ((1408456071729877091 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP002Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP002Input2654 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02703MinusFourthP002Input2654 =
      (batchC02703MinusFourthP002Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP002Input2654,
        batchC02703MinusFourthP002Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP002Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP002Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP002Center2654))).trans
  norm_num [batchC02703MinusFourthP002Error2654, batchC02703MinusFourthP002ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP002Center2654]

theorem batchC02703MinusFourthP002Bound2654 : batchC02703MinusFourthCell2654 ⟨2, by omega⟩ ≤
    batchC02703MinusFourthP002Upper2654 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      batchC02703MinusFourthP002Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP002Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP002Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((382830487110454839629892540203794432 : ℝ) /
        535582378596426958724104076656640625) ((382988943437901219944308886453878784 : ℝ) /
        535582378596426958724104076656640625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP002ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP002Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((382830487110454839629892540203794432 : ℝ) /
        535582378596426958724104076656640625) ((382988943437901219944308886453878784 : ℝ) /
        535582378596426958724104076656640625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP002ExpUpper2654, batchC02703MinusFourthP002Frequency2654,
        batchC02703MinusFourthP002Upper2654]

def batchC02703MinusFourthP003Input2654 : RatPair2542 := ((((-((1123633 * 10^40
        + 8935120981975320257048497025616878211767) * 10^40
        + 6354069595364759253486690867300176097541)) : ℚ) /
        ((1663227 * 10^40
        + 7484979237186903090894426700705785431208) * 10^40
        + 1788951683019923183647716979507200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP003Center2654 : RatPair2542 := (((243958291043441923884192464487 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP003Error2654 : ℝ := ((8433999575351475730321511 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

noncomputable def batchC02703MinusFourthP003ExpUpper2654 : ℝ := (((6 * 10^40
        + 7058744423656506248906962637319341019239) : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

noncomputable def batchC02703MinusFourthP003Frequency2654 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02703MinusFourthP003Upper2654 : ℝ :=
    ((2030284916178128545284295231868840965 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP003Exponent2654 : ℝ := (((-((1123633 * 10^40
        + 8935120981975320257048497025616878211767) * 10^40
        + 6354069595364759253486690867300176097541)) : ℝ) /
        ((25987 * 10^40
        + 9335702800581045360795225417198527897362) * 10^40
        + 6277952370047186299744495577804800000000))

theorem batchC02703MinusFourthP003ExpBound2654 :
    Real.exp batchC02703MinusFourthP003Exponent2654 ≤ batchC02703MinusFourthP003ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP003Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP003Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP003Input2654 6).1 =
      batchC02703MinusFourthP003Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP003Input2654 6).2 : ℝ) =
      batchC02703MinusFourthP003Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP003Input2654 6).2 =
        ((8433999575351475730321511 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP003Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP003Input2654 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02703MinusFourthP003Input2654 =
      (batchC02703MinusFourthP003Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP003Input2654,
        batchC02703MinusFourthP003Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP003Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP003Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP003Center2654))).trans
  norm_num [batchC02703MinusFourthP003Error2654, batchC02703MinusFourthP003ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP003Center2654]

theorem batchC02703MinusFourthP003Bound2654 : batchC02703MinusFourthCell2654 ⟨3, by omega⟩ ≤
    batchC02703MinusFourthP003Upper2654 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      batchC02703MinusFourthP003Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP003Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP003Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP003ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP003Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP003ExpUpper2654, batchC02703MinusFourthP003Frequency2654,
        batchC02703MinusFourthP003Upper2654]

def batchC02703MinusFourthP004Input2654 : RatPair2542 := ((((-((19409 * 10^40
        + 5154249357390590641292158298147350541340) * 10^40
        + 5482807798905915655760463568542489589583)) : ℚ) /
        ((33531 * 10^40
        + 121249836105257007936565198170400154566) * 10^40
        + 1275913189804802970902121683353600000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP004Center2654 : RatPair2542 := (((29759004498903884151330533388825 : ℚ)
    /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP004Error2654 : ℝ := ((7471722082999437027531715609 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02703MinusFourthP004ExpUpper2654 : ℝ := (((6544 * 10^40
        + 742955166241213718809164551614087722009) : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02703MinusFourthP004Frequency2654 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02703MinusFourthP004Upper2654 : ℝ :=
    ((556137459305291809859287403337142504051 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP004Exponent2654 : ℝ := (((-((19409 * 10^40
        + 5154249357390590641292158298147350541340) * 10^40
        + 5482807798905915655760463568542489589583)) : ℝ) /
        ((523 * 10^40
        + 9220644528689144640749008831221412502415) * 10^40
        + 957436143590700046420345651302400000000))

theorem batchC02703MinusFourthP004ExpBound2654 :
    Real.exp batchC02703MinusFourthP004Exponent2654 ≤ batchC02703MinusFourthP004ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP004Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP004Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP004Input2654 6).1 =
      batchC02703MinusFourthP004Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP004Input2654 6).2 : ℝ) =
      batchC02703MinusFourthP004Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP004Input2654 6).2 =
        ((7471722082999437027531715609 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP004Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP004Input2654 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02703MinusFourthP004Input2654 =
      (batchC02703MinusFourthP004Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP004Input2654,
        batchC02703MinusFourthP004Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP004Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP004Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP004Center2654))).trans
  norm_num [batchC02703MinusFourthP004Error2654, batchC02703MinusFourthP004ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP004Center2654]

theorem batchC02703MinusFourthP004Bound2654 : batchC02703MinusFourthCell2654 ⟨4, by omega⟩ ≤
    batchC02703MinusFourthP004Upper2654 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      batchC02703MinusFourthP004Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP004Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP004Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((382830487110454839629892540203794432 : ℝ) /
        811296384146067132209863967375390625) ((382988943437901219944308886453878784 : ℝ) /
        811296384146067132209863967375390625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP004ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP004Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((382830487110454839629892540203794432 : ℝ) /
        811296384146067132209863967375390625) ((382988943437901219944308886453878784 : ℝ) /
        811296384146067132209863967375390625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP004ExpUpper2654, batchC02703MinusFourthP004Frequency2654,
        batchC02703MinusFourthP004Upper2654]

def batchC02703MinusFourthP006Input2654 : RatPair2542 := ((((-164292077059868249722411457815339) :
    ℚ) /
        287967140010748827834777600000000),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP006Center2654 : RatPair2542 := (((28155406605601761 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP006Error2654 : ℝ := ((4604744671393 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02703MinusFourthP006ExpUpper2654 : ℝ := ((15478598473810172143305728161 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02703MinusFourthP006Frequency2654 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02703MinusFourthP006Upper2654 : ℝ := ((420442240859989419040633 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02703MinusFourthP006Exponent2654 : ℝ :=
    (((-164292077059868249722411457815339) : ℝ) /
        2249743281333975217459200000000)

theorem batchC02703MinusFourthP006ExpBound2654 :
    Real.exp batchC02703MinusFourthP006Exponent2654 ≤ batchC02703MinusFourthP006ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP006Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP006Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP006Input2654 7).1 =
      batchC02703MinusFourthP006Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP006Input2654 7).2 : ℝ) =
      batchC02703MinusFourthP006Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP006Input2654 7).2 =
        ((4604744671393 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP006Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP006Input2654 hz 7
  rw [hc, he] at h
  have ha : (2 : ℂ)^7 * embedPair2542 batchC02703MinusFourthP006Input2654 =
      (batchC02703MinusFourthP006Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP006Input2654,
        batchC02703MinusFourthP006Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP006Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP006Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP006Center2654))).trans
  norm_num [batchC02703MinusFourthP006Error2654, batchC02703MinusFourthP006ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP006Center2654]

theorem batchC02703MinusFourthP006Bound2654 : batchC02703MinusFourthCell2654 ⟨6, by omega⟩ ≤
    batchC02703MinusFourthP006Upper2654 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      batchC02703MinusFourthP006Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP006Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP006Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) ((9895936151 : ℝ) /
        12800000000) ((158400514417 : ℝ) /
        204800000000) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP006ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP006Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) ((9895936151 : ℝ) /
        12800000000) ((158400514417 : ℝ) /
        204800000000) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP006ExpUpper2654, batchC02703MinusFourthP006Frequency2654,
        batchC02703MinusFourthP006Upper2654]

def batchC02703MinusFourthP007Input2654 : RatPair2542 := ((((-((1123633 * 10^40
        + 8935120981975320257048497025616878211767) * 10^40
        + 6354069595364759253486690867300176097541)) : ℚ) /
        ((1663227 * 10^40
        + 7484979237186903090894426700705785431208) * 10^40
        + 1788951683019923183647716979507200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP007Center2654 : RatPair2542 := (((243958291043441923884192464487 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP007Error2654 : ℝ := ((8433999575351475730321511 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

noncomputable def batchC02703MinusFourthP007ExpUpper2654 : ℝ := (((6 * 10^40
        + 7058744423656506248906962637319341019239) : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

noncomputable def batchC02703MinusFourthP007Frequency2654 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02703MinusFourthP007Upper2654 : ℝ := ((6591886785524944261352086977134097
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02703MinusFourthP007Exponent2654 : ℝ := (((-((1123633 * 10^40
        + 8935120981975320257048497025616878211767) * 10^40
        + 6354069595364759253486690867300176097541)) : ℝ) /
        ((25987 * 10^40
        + 9335702800581045360795225417198527897362) * 10^40
        + 6277952370047186299744495577804800000000))

theorem batchC02703MinusFourthP007ExpBound2654 :
    Real.exp batchC02703MinusFourthP007Exponent2654 ≤ batchC02703MinusFourthP007ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP007Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP007Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP007Input2654 6).1 =
      batchC02703MinusFourthP007Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP007Input2654 6).2 : ℝ) =
      batchC02703MinusFourthP007Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP007Input2654 6).2 =
        ((8433999575351475730321511 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP007Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP007Input2654 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02703MinusFourthP007Input2654 =
      (batchC02703MinusFourthP007Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP007Input2654,
        batchC02703MinusFourthP007Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP007Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP007Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP007Center2654))).trans
  norm_num [batchC02703MinusFourthP007Error2654, batchC02703MinusFourthP007ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP007Center2654]

theorem batchC02703MinusFourthP007Bound2654 : batchC02703MinusFourthCell2654 ⟨7, by omega⟩ ≤
    batchC02703MinusFourthP007Upper2654 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      batchC02703MinusFourthP007Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP007Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP007Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP007ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP007Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP007ExpUpper2654, batchC02703MinusFourthP007Frequency2654,
        batchC02703MinusFourthP007Upper2654]

def batchC02703MinusFourthP008Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP008Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP008Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP008ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP008Frequency2654 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def batchC02703MinusFourthP008Upper2654 : ℝ := ((23073923062811818183098067 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP008Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP008ExpBound2654 :
    Real.exp batchC02703MinusFourthP008Exponent2654 ≤ batchC02703MinusFourthP008ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP008Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP008Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP008Input2654 14).1 =
      batchC02703MinusFourthP008Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP008Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP008Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP008Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP008Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP008Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP008Input2654 =
      (batchC02703MinusFourthP008Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP008Input2654,
        batchC02703MinusFourthP008Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP008Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP008Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP008Center2654))).trans
  norm_num [batchC02703MinusFourthP008Error2654, batchC02703MinusFourthP008ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP008Center2654]

theorem batchC02703MinusFourthP008Bound2654 : batchC02703MinusFourthCell2654 ⟨8, by omega⟩ ≤
    batchC02703MinusFourthP008Upper2654 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      batchC02703MinusFourthP008Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP008Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP008Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP008ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP008Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP008ExpUpper2654, batchC02703MinusFourthP008Frequency2654,
        batchC02703MinusFourthP008Upper2654]

def batchC02703MinusFourthP009Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP009Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP009Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP009ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP009Frequency2654 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def batchC02703MinusFourthP009Upper2654 : ℝ := ((23074258730486614568225089 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP009Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP009ExpBound2654 :
    Real.exp batchC02703MinusFourthP009Exponent2654 ≤ batchC02703MinusFourthP009ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP009Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP009Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP009Input2654 14).1 =
      batchC02703MinusFourthP009Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP009Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP009Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP009Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP009Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP009Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP009Input2654 =
      (batchC02703MinusFourthP009Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP009Input2654,
        batchC02703MinusFourthP009Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP009Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP009Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP009Center2654))).trans
  norm_num [batchC02703MinusFourthP009Error2654, batchC02703MinusFourthP009ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP009Center2654]

theorem batchC02703MinusFourthP009Bound2654 : batchC02703MinusFourthCell2654 ⟨9, by omega⟩ ≤
    batchC02703MinusFourthP009Upper2654 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      batchC02703MinusFourthP009Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP009Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP009Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP009ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP009Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP009ExpUpper2654, batchC02703MinusFourthP009Frequency2654,
        batchC02703MinusFourthP009Upper2654]

def batchC02703MinusFourthP010Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP010Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP010Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP010ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP010Frequency2654 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def batchC02703MinusFourthP010Upper2654 : ℝ := ((5768613292775253273631599 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02703MinusFourthP010Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP010ExpBound2654 :
    Real.exp batchC02703MinusFourthP010Exponent2654 ≤ batchC02703MinusFourthP010ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP010Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP010Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP010Input2654 14).1 =
      batchC02703MinusFourthP010Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP010Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP010Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP010Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP010Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP010Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP010Input2654 =
      (batchC02703MinusFourthP010Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP010Input2654,
        batchC02703MinusFourthP010Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP010Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP010Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP010Center2654))).trans
  norm_num [batchC02703MinusFourthP010Error2654, batchC02703MinusFourthP010ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP010Center2654]

theorem batchC02703MinusFourthP010Bound2654 : batchC02703MinusFourthCell2654 ⟨10, by omega⟩ ≤
    batchC02703MinusFourthP010Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      batchC02703MinusFourthP010Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP010Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP010Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP010ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP010Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP010ExpUpper2654, batchC02703MinusFourthP010Frequency2654,
        batchC02703MinusFourthP010Upper2654]

def batchC02703MinusFourthP011Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP011Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP011Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP011ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP011Frequency2654 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def batchC02703MinusFourthP011Upper2654 : ℝ := ((11537291409285838155200985 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02703MinusFourthP011Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP011ExpBound2654 :
    Real.exp batchC02703MinusFourthP011Exponent2654 ≤ batchC02703MinusFourthP011ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP011Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP011Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP011Input2654 14).1 =
      batchC02703MinusFourthP011Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP011Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP011Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP011Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP011Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP011Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP011Input2654 =
      (batchC02703MinusFourthP011Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP011Input2654,
        batchC02703MinusFourthP011Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP011Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP011Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP011Center2654))).trans
  norm_num [batchC02703MinusFourthP011Error2654, batchC02703MinusFourthP011ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP011Center2654]

theorem batchC02703MinusFourthP011Bound2654 : batchC02703MinusFourthCell2654 ⟨11, by omega⟩ ≤
    batchC02703MinusFourthP011Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      batchC02703MinusFourthP011Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP011Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP011Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP011ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP011Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP011ExpUpper2654, batchC02703MinusFourthP011Frequency2654,
        batchC02703MinusFourthP011Upper2654]

def batchC02703MinusFourthP012Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP012Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP012Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP012ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP012Frequency2654 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def batchC02703MinusFourthP012Upper2654 : ℝ := ((23074717106517523729634123 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP012Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP012ExpBound2654 :
    Real.exp batchC02703MinusFourthP012Exponent2654 ≤ batchC02703MinusFourthP012ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP012Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP012Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP012Input2654 14).1 =
      batchC02703MinusFourthP012Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP012Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP012Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP012Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP012Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP012Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP012Input2654 =
      (batchC02703MinusFourthP012Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP012Input2654,
        batchC02703MinusFourthP012Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP012Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP012Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP012Center2654))).trans
  norm_num [batchC02703MinusFourthP012Error2654, batchC02703MinusFourthP012ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP012Center2654]

theorem batchC02703MinusFourthP012Bound2654 : batchC02703MinusFourthCell2654 ⟨12, by omega⟩ ≤
    batchC02703MinusFourthP012Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      batchC02703MinusFourthP012Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP012Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP012Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP012ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP012Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP012ExpUpper2654, batchC02703MinusFourthP012Frequency2654,
        batchC02703MinusFourthP012Upper2654]

def batchC02703MinusFourthP013Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP013Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP013Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP013ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP013Frequency2654 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def batchC02703MinusFourthP013Upper2654 : ℝ := ((23074839484602301766622563 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP013Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP013ExpBound2654 :
    Real.exp batchC02703MinusFourthP013Exponent2654 ≤ batchC02703MinusFourthP013ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP013Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP013Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP013Input2654 14).1 =
      batchC02703MinusFourthP013Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP013Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP013Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP013Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP013Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP013Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP013Input2654 =
      (batchC02703MinusFourthP013Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP013Input2654,
        batchC02703MinusFourthP013Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP013Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP013Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP013Center2654))).trans
  norm_num [batchC02703MinusFourthP013Error2654, batchC02703MinusFourthP013ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP013Center2654]

theorem batchC02703MinusFourthP013Bound2654 : batchC02703MinusFourthCell2654 ⟨13, by omega⟩ ≤
    batchC02703MinusFourthP013Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      batchC02703MinusFourthP013Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP013Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP013Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP013ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP013Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP013ExpUpper2654, batchC02703MinusFourthP013Frequency2654,
        batchC02703MinusFourthP013Upper2654]

def batchC02703MinusFourthP014Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP014Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP014Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP014ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP014Frequency2654 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def batchC02703MinusFourthP014Upper2654 : ℝ := ((23075066245346212233414543 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP014Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP014ExpBound2654 :
    Real.exp batchC02703MinusFourthP014Exponent2654 ≤ batchC02703MinusFourthP014ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP014Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP014Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP014Input2654 14).1 =
      batchC02703MinusFourthP014Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP014Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP014Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP014Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP014Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP014Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP014Input2654 =
      (batchC02703MinusFourthP014Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP014Input2654,
        batchC02703MinusFourthP014Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP014Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP014Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP014Center2654))).trans
  norm_num [batchC02703MinusFourthP014Error2654, batchC02703MinusFourthP014ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP014Center2654]

theorem batchC02703MinusFourthP014Bound2654 : batchC02703MinusFourthCell2654 ⟨14, by omega⟩ ≤
    batchC02703MinusFourthP014Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      batchC02703MinusFourthP014Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP014Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP014Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP014ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP014Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP014ExpUpper2654, batchC02703MinusFourthP014Frequency2654,
        batchC02703MinusFourthP014Upper2654]

def batchC02703MinusFourthP015Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP015Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP015Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP015ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP015Frequency2654 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def batchC02703MinusFourthP015Upper2654 : ℝ := ((23075228724428605552759153 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP015Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP015ExpBound2654 :
    Real.exp batchC02703MinusFourthP015Exponent2654 ≤ batchC02703MinusFourthP015ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP015Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP015Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP015Input2654 14).1 =
      batchC02703MinusFourthP015Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP015Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP015Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP015Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP015Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP015Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP015Input2654 =
      (batchC02703MinusFourthP015Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP015Input2654,
        batchC02703MinusFourthP015Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP015Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP015Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP015Center2654))).trans
  norm_num [batchC02703MinusFourthP015Error2654, batchC02703MinusFourthP015ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP015Center2654]

theorem batchC02703MinusFourthP015Bound2654 : batchC02703MinusFourthCell2654 ⟨15, by omega⟩ ≤
    batchC02703MinusFourthP015Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      batchC02703MinusFourthP015Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP015Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP015Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP015ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP015Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP015ExpUpper2654, batchC02703MinusFourthP015Frequency2654,
        batchC02703MinusFourthP015Upper2654]

def batchC02703MinusFourthP016Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP016Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP016Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP016ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP016Frequency2654 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def batchC02703MinusFourthP016Upper2654 : ℝ := ((721104567072041405836987 : ℝ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968))

noncomputable def batchC02703MinusFourthP016Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP016ExpBound2654 :
    Real.exp batchC02703MinusFourthP016Exponent2654 ≤ batchC02703MinusFourthP016ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP016Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP016Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP016Input2654 14).1 =
      batchC02703MinusFourthP016Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP016Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP016Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP016Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP016Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP016Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP016Input2654 =
      (batchC02703MinusFourthP016Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP016Input2654,
        batchC02703MinusFourthP016Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP016Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP016Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP016Center2654))).trans
  norm_num [batchC02703MinusFourthP016Error2654, batchC02703MinusFourthP016ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP016Center2654]

theorem batchC02703MinusFourthP016Bound2654 : batchC02703MinusFourthCell2654 ⟨16, by omega⟩ ≤
    batchC02703MinusFourthP016Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      batchC02703MinusFourthP016Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP016Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP016Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP016ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP016Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP016ExpUpper2654, batchC02703MinusFourthP016Frequency2654,
        batchC02703MinusFourthP016Upper2654]

def batchC02703MinusFourthP017Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP017Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP017Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP017ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP017Frequency2654 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def batchC02703MinusFourthP017Upper2654 : ℝ := ((23075574234625764344423857 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP017Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP017ExpBound2654 :
    Real.exp batchC02703MinusFourthP017Exponent2654 ≤ batchC02703MinusFourthP017ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP017Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP017Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP017Input2654 14).1 =
      batchC02703MinusFourthP017Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP017Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP017Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP017Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP017Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP017Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP017Input2654 =
      (batchC02703MinusFourthP017Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP017Input2654,
        batchC02703MinusFourthP017Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP017Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP017Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP017Center2654))).trans
  norm_num [batchC02703MinusFourthP017Error2654, batchC02703MinusFourthP017ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP017Center2654]

theorem batchC02703MinusFourthP017Bound2654 : batchC02703MinusFourthCell2654 ⟨17, by omega⟩ ≤
    batchC02703MinusFourthP017Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      batchC02703MinusFourthP017Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP017Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP017Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP017ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP017Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP017ExpUpper2654, batchC02703MinusFourthP017Frequency2654,
        batchC02703MinusFourthP017Upper2654]

def batchC02703MinusFourthP018Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP018Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP018Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP018ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP018Frequency2654 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def batchC02703MinusFourthP018Upper2654 : ℝ := ((5768915117770488676986747 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02703MinusFourthP018Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP018ExpBound2654 :
    Real.exp batchC02703MinusFourthP018Exponent2654 ≤ batchC02703MinusFourthP018ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP018Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP018Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP018Input2654 14).1 =
      batchC02703MinusFourthP018Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP018Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP018Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP018Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP018Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP018Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP018Input2654 =
      (batchC02703MinusFourthP018Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP018Input2654,
        batchC02703MinusFourthP018Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP018Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP018Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP018Center2654))).trans
  norm_num [batchC02703MinusFourthP018Error2654, batchC02703MinusFourthP018ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP018Center2654]

theorem batchC02703MinusFourthP018Bound2654 : batchC02703MinusFourthCell2654 ⟨18, by omega⟩ ≤
    batchC02703MinusFourthP018Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      batchC02703MinusFourthP018Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP018Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP018Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP018ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP018Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP018ExpUpper2654, batchC02703MinusFourthP018Frequency2654,
        batchC02703MinusFourthP018Upper2654]

def batchC02703MinusFourthP019Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP019Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP019Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP019ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP019Frequency2654 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def batchC02703MinusFourthP019Upper2654 : ℝ := ((23075816325210868548943065 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP019Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP019ExpBound2654 :
    Real.exp batchC02703MinusFourthP019Exponent2654 ≤ batchC02703MinusFourthP019ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP019Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP019Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP019Input2654 14).1 =
      batchC02703MinusFourthP019Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP019Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP019Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP019Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP019Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP019Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP019Input2654 =
      (batchC02703MinusFourthP019Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP019Input2654,
        batchC02703MinusFourthP019Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP019Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP019Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP019Center2654))).trans
  norm_num [batchC02703MinusFourthP019Error2654, batchC02703MinusFourthP019ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP019Center2654]

theorem batchC02703MinusFourthP019Bound2654 : batchC02703MinusFourthCell2654 ⟨19, by omega⟩ ≤
    batchC02703MinusFourthP019Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      batchC02703MinusFourthP019Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP019Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP019Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP019ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP019Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP019ExpUpper2654, batchC02703MinusFourthP019Frequency2654,
        batchC02703MinusFourthP019Upper2654]

def batchC02703MinusFourthP020Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP020Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP020Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP020ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP020Frequency2654 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def batchC02703MinusFourthP020Upper2654 : ℝ := ((23075985805969008877385803 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP020Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP020ExpBound2654 :
    Real.exp batchC02703MinusFourthP020Exponent2654 ≤ batchC02703MinusFourthP020ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP020Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP020Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP020Input2654 14).1 =
      batchC02703MinusFourthP020Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP020Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP020Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP020Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP020Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP020Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP020Input2654 =
      (batchC02703MinusFourthP020Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP020Input2654,
        batchC02703MinusFourthP020Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP020Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP020Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP020Center2654))).trans
  norm_num [batchC02703MinusFourthP020Error2654, batchC02703MinusFourthP020ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP020Center2654]

theorem batchC02703MinusFourthP020Bound2654 : batchC02703MinusFourthCell2654 ⟨20, by omega⟩ ≤
    batchC02703MinusFourthP020Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      batchC02703MinusFourthP020Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP020Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP020Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP020ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP020Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP020ExpUpper2654, batchC02703MinusFourthP020Frequency2654,
        batchC02703MinusFourthP020Upper2654]

def batchC02703MinusFourthP021Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP021Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP021Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP021ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP021Frequency2654 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def batchC02703MinusFourthP021Upper2654 : ℝ := ((11538063622821597001972511 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02703MinusFourthP021Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP021ExpBound2654 :
    Real.exp batchC02703MinusFourthP021Exponent2654 ≤ batchC02703MinusFourthP021ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP021Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP021Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP021Input2654 14).1 =
      batchC02703MinusFourthP021Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP021Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP021Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP021Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP021Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP021Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP021Input2654 =
      (batchC02703MinusFourthP021Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP021Input2654,
        batchC02703MinusFourthP021Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP021Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP021Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP021Center2654))).trans
  norm_num [batchC02703MinusFourthP021Error2654, batchC02703MinusFourthP021ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP021Center2654]

theorem batchC02703MinusFourthP021Bound2654 : batchC02703MinusFourthCell2654 ⟨21, by omega⟩ ≤
    batchC02703MinusFourthP021Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      batchC02703MinusFourthP021Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP021Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP021Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP021ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP021Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP021ExpUpper2654, batchC02703MinusFourthP021Frequency2654,
        batchC02703MinusFourthP021Upper2654]

def batchC02703MinusFourthP022Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP022Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP022Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP022ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP022Frequency2654 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def batchC02703MinusFourthP022Upper2654 : ℝ := ((11538099820066453750725863 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02703MinusFourthP022Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP022ExpBound2654 :
    Real.exp batchC02703MinusFourthP022Exponent2654 ≤ batchC02703MinusFourthP022ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP022Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP022Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP022Input2654 14).1 =
      batchC02703MinusFourthP022Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP022Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP022Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP022Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP022Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP022Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP022Input2654 =
      (batchC02703MinusFourthP022Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP022Input2654,
        batchC02703MinusFourthP022Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP022Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP022Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP022Center2654))).trans
  norm_num [batchC02703MinusFourthP022Error2654, batchC02703MinusFourthP022ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP022Center2654]

theorem batchC02703MinusFourthP022Bound2654 : batchC02703MinusFourthCell2654 ⟨22, by omega⟩ ≤
    batchC02703MinusFourthP022Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      batchC02703MinusFourthP022Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP022Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP022Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP022ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP022Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP022ExpUpper2654, batchC02703MinusFourthP022Frequency2654,
        batchC02703MinusFourthP022Upper2654]

def batchC02703MinusFourthP023Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP023Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP023Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP023ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP023Frequency2654 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def batchC02703MinusFourthP023Upper2654 : ℝ := ((1442275523031334860523205 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC02703MinusFourthP023Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP023ExpBound2654 :
    Real.exp batchC02703MinusFourthP023Exponent2654 ≤ batchC02703MinusFourthP023ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP023Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP023Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP023Input2654 14).1 =
      batchC02703MinusFourthP023Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP023Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP023Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP023Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP023Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP023Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP023Input2654 =
      (batchC02703MinusFourthP023Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP023Input2654,
        batchC02703MinusFourthP023Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP023Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP023Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP023Center2654))).trans
  norm_num [batchC02703MinusFourthP023Error2654, batchC02703MinusFourthP023ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP023Center2654]

theorem batchC02703MinusFourthP023Bound2654 : batchC02703MinusFourthCell2654 ⟨23, by omega⟩ ≤
    batchC02703MinusFourthP023Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      batchC02703MinusFourthP023Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP023Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP023Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP023ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP023Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP023ExpUpper2654, batchC02703MinusFourthP023Frequency2654,
        batchC02703MinusFourthP023Upper2654]

def batchC02703MinusFourthP024Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP024Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP024Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP024ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP024Frequency2654 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def batchC02703MinusFourthP024Upper2654 : ℝ := ((23076504292368023089133603 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP024Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP024ExpBound2654 :
    Real.exp batchC02703MinusFourthP024Exponent2654 ≤ batchC02703MinusFourthP024ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP024Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP024Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP024Input2654 14).1 =
      batchC02703MinusFourthP024Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP024Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP024Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP024Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP024Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP024Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP024Input2654 =
      (batchC02703MinusFourthP024Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP024Input2654,
        batchC02703MinusFourthP024Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP024Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP024Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP024Center2654))).trans
  norm_num [batchC02703MinusFourthP024Error2654, batchC02703MinusFourthP024ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP024Center2654]

theorem batchC02703MinusFourthP024Bound2654 : batchC02703MinusFourthCell2654 ⟨24, by omega⟩ ≤
    batchC02703MinusFourthP024Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      batchC02703MinusFourthP024Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP024Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP024Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP024ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP024Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP024ExpUpper2654, batchC02703MinusFourthP024Frequency2654,
        batchC02703MinusFourthP024Upper2654]

def batchC02703MinusFourthP025Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP025Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP025Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP025ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP025Frequency2654 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def batchC02703MinusFourthP025Upper2654 : ℝ := ((1442289035246310523519227 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC02703MinusFourthP025Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP025ExpBound2654 :
    Real.exp batchC02703MinusFourthP025Exponent2654 ≤ batchC02703MinusFourthP025ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP025Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP025Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP025Input2654 14).1 =
      batchC02703MinusFourthP025Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP025Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP025Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP025Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP025Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP025Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP025Input2654 =
      (batchC02703MinusFourthP025Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP025Input2654,
        batchC02703MinusFourthP025Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP025Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP025Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP025Center2654))).trans
  norm_num [batchC02703MinusFourthP025Error2654, batchC02703MinusFourthP025ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP025Center2654]

theorem batchC02703MinusFourthP025Bound2654 : batchC02703MinusFourthCell2654 ⟨25, by omega⟩ ≤
    batchC02703MinusFourthP025Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      batchC02703MinusFourthP025Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP025Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP025Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP025ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP025Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP025ExpUpper2654, batchC02703MinusFourthP025Frequency2654,
        batchC02703MinusFourthP025Upper2654]

def batchC02703MinusFourthP026Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP026Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP026Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP026ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP026Frequency2654 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def batchC02703MinusFourthP026Upper2654 : ℝ := ((23076747477319604714256117 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP026Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP026ExpBound2654 :
    Real.exp batchC02703MinusFourthP026Exponent2654 ≤ batchC02703MinusFourthP026ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP026Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP026Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP026Input2654 14).1 =
      batchC02703MinusFourthP026Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP026Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP026Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP026Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP026Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP026Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP026Input2654 =
      (batchC02703MinusFourthP026Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP026Input2654,
        batchC02703MinusFourthP026Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP026Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP026Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP026Center2654))).trans
  norm_num [batchC02703MinusFourthP026Error2654, batchC02703MinusFourthP026ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP026Center2654]

theorem batchC02703MinusFourthP026Bound2654 : batchC02703MinusFourthCell2654 ⟨26, by omega⟩ ≤
    batchC02703MinusFourthP026Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      batchC02703MinusFourthP026Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP026Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP026Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP026ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP026Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP026ExpUpper2654, batchC02703MinusFourthP026Frequency2654,
        batchC02703MinusFourthP026Upper2654]

def batchC02703MinusFourthP027Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP027Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP027Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP027ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP027Frequency2654 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def batchC02703MinusFourthP027Upper2654 : ℝ := ((23076924846564797241895801 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP027Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP027ExpBound2654 :
    Real.exp batchC02703MinusFourthP027Exponent2654 ≤ batchC02703MinusFourthP027ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP027Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP027Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP027Input2654 14).1 =
      batchC02703MinusFourthP027Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP027Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP027Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP027Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP027Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP027Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP027Input2654 =
      (batchC02703MinusFourthP027Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP027Input2654,
        batchC02703MinusFourthP027Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP027Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP027Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP027Center2654))).trans
  norm_num [batchC02703MinusFourthP027Error2654, batchC02703MinusFourthP027ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP027Center2654]

theorem batchC02703MinusFourthP027Bound2654 : batchC02703MinusFourthCell2654 ⟨27, by omega⟩ ≤
    batchC02703MinusFourthP027Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      batchC02703MinusFourthP027Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP027Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP027Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP027ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP027Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP027ExpUpper2654, batchC02703MinusFourthP027Frequency2654,
        batchC02703MinusFourthP027Upper2654]

def batchC02703MinusFourthP028Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP028Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP028Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP028ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP028Frequency2654 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def batchC02703MinusFourthP028Upper2654 : ℝ := ((5769248767470055402733371 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02703MinusFourthP028Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP028ExpBound2654 :
    Real.exp batchC02703MinusFourthP028Exponent2654 ≤ batchC02703MinusFourthP028ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP028Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP028Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP028Input2654 14).1 =
      batchC02703MinusFourthP028Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP028Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP028Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP028Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP028Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP028Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP028Input2654 =
      (batchC02703MinusFourthP028Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP028Input2654,
        batchC02703MinusFourthP028Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP028Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP028Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP028Center2654))).trans
  norm_num [batchC02703MinusFourthP028Error2654, batchC02703MinusFourthP028ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP028Center2654]

theorem batchC02703MinusFourthP028Bound2654 : batchC02703MinusFourthCell2654 ⟨28, by omega⟩ ≤
    batchC02703MinusFourthP028Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      batchC02703MinusFourthP028Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP028Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP028Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP028ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP028Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP028ExpUpper2654, batchC02703MinusFourthP028Frequency2654,
        batchC02703MinusFourthP028Upper2654]

def batchC02703MinusFourthP029Input2654 : RatPair2542 := ((((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℚ) /
        ((695344 * 10^40
        + 5411710447090082500665314113972683426479) * 10^40
        + 5859481230959407013815546753843200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusFourthP029Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusFourthP029Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP029ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703MinusFourthP029Frequency2654 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def batchC02703MinusFourthP029Upper2654 : ℝ := ((23077101980784601582614181 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703MinusFourthP029Exponent2654 : ℝ := (((-((385403 * 10^40
        + 6652758657439547149258474927709796594651) * 10^40
        + 5851698129706711973384956323843144847541)) : ℝ) /
        ((42 * 10^40
        + 4404627179592717900543253498175901653041) * 10^40
        + 1669669157789975549744495577804800000000))

theorem batchC02703MinusFourthP029ExpBound2654 :
    Real.exp batchC02703MinusFourthP029Exponent2654 ≤ batchC02703MinusFourthP029ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703MinusFourthP029Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusFourthP029Input2654]
  have hc : (compactExp2547 batchC02703MinusFourthP029Input2654 14).1 =
      batchC02703MinusFourthP029Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703MinusFourthP029Input2654 14).2 : ℝ) =
      batchC02703MinusFourthP029Error2654 := by
    have hq : (compactExp2547 batchC02703MinusFourthP029Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703MinusFourthP029Error2654]
  have h := compactExp_error2547 batchC02703MinusFourthP029Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703MinusFourthP029Input2654 =
      (batchC02703MinusFourthP029Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703MinusFourthP029Input2654,
        batchC02703MinusFourthP029Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703MinusFourthP029Exponent2654 : ℂ)) (embedPair2542
        batchC02703MinusFourthP029Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703MinusFourthP029Center2654))).trans
  norm_num [batchC02703MinusFourthP029Error2654, batchC02703MinusFourthP029ExpUpper2654,
      pairMagnitude2542,
      batchC02703MinusFourthP029Center2654]

theorem batchC02703MinusFourthP029Bound2654 : batchC02703MinusFourthCell2654 ⟨29, by omega⟩ ≤
    batchC02703MinusFourthP029Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      batchC02703MinusFourthP029Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703MinusFourthP029Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703MinusFourthP029Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703MinusFourthP029ExpBound2654 using 1; norm_num
        [batchC02703MinusFourthP029Exponent2654])
  have hid : batchC02703MinusFourthCell2654 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703MinusFourthCell2654, cellNearAbs2538, batchN02703MinusPosition2654,
      batchN02704MinusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703MinusFourthP029ExpUpper2654, batchC02703MinusFourthP029Frequency2654,
        batchC02703MinusFourthP029Upper2654]

noncomputable def batchC02703MinusFourthP000Upper2654 : ℝ := 0

theorem batchC02703MinusFourthP000Bound2654 :
    batchC02703MinusFourthCell2654 ⟨0, by omega⟩ ≤ batchC02703MinusFourthP000Upper2654 := by
  norm_num [batchC02703MinusFourthCell2654, batchC02703MinusFourthP000Upper2654, cellNearAbs2538,
    batchN02703MinusPosition2654, batchN02704MinusPosition2654, storedWidth]

noncomputable def batchC02703MinusFourthP005Upper2654 : ℝ := 0

theorem batchC02703MinusFourthP005Bound2654 :
    batchC02703MinusFourthCell2654 ⟨5, by omega⟩ ≤ batchC02703MinusFourthP005Upper2654 := by
  norm_num [batchC02703MinusFourthCell2654, batchC02703MinusFourthP005Upper2654, cellNearAbs2538,
    batchN02703MinusPosition2654, batchN02704MinusPosition2654, storedWidth]

noncomputable def batchC02703MinusFourthUpper2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02703MinusFourthP000Upper2654
  | 1 => batchC02703MinusFourthP001Upper2654
  | 2 => batchC02703MinusFourthP002Upper2654
  | 3 => batchC02703MinusFourthP003Upper2654
  | 4 => batchC02703MinusFourthP004Upper2654
  | 5 => batchC02703MinusFourthP005Upper2654
  | 6 => batchC02703MinusFourthP006Upper2654
  | 7 => batchC02703MinusFourthP007Upper2654
  | 8 => batchC02703MinusFourthP008Upper2654
  | 9 => batchC02703MinusFourthP009Upper2654
  | 10 => batchC02703MinusFourthP010Upper2654
  | 11 => batchC02703MinusFourthP011Upper2654
  | 12 => batchC02703MinusFourthP012Upper2654
  | 13 => batchC02703MinusFourthP013Upper2654
  | 14 => batchC02703MinusFourthP014Upper2654
  | 15 => batchC02703MinusFourthP015Upper2654
  | 16 => batchC02703MinusFourthP016Upper2654
  | 17 => batchC02703MinusFourthP017Upper2654
  | 18 => batchC02703MinusFourthP018Upper2654
  | 19 => batchC02703MinusFourthP019Upper2654
  | 20 => batchC02703MinusFourthP020Upper2654
  | 21 => batchC02703MinusFourthP021Upper2654
  | 22 => batchC02703MinusFourthP022Upper2654
  | 23 => batchC02703MinusFourthP023Upper2654
  | 24 => batchC02703MinusFourthP024Upper2654
  | 25 => batchC02703MinusFourthP025Upper2654
  | 26 => batchC02703MinusFourthP026Upper2654
  | 27 => batchC02703MinusFourthP027Upper2654
  | 28 => batchC02703MinusFourthP028Upper2654
  | 29 => batchC02703MinusFourthP029Upper2654
  | _ => 0

theorem batchC02703MinusFourthBound2654 (i : Fin 30) :
    batchC02703MinusFourthCell2654 i ≤ batchC02703MinusFourthUpper2654 i := by
  fin_cases i
  · exact batchC02703MinusFourthP000Bound2654
  · exact batchC02703MinusFourthP001Bound2654
  · exact batchC02703MinusFourthP002Bound2654
  · exact batchC02703MinusFourthP003Bound2654
  · exact batchC02703MinusFourthP004Bound2654
  · exact batchC02703MinusFourthP005Bound2654
  · exact batchC02703MinusFourthP006Bound2654
  · exact batchC02703MinusFourthP007Bound2654
  · exact batchC02703MinusFourthP008Bound2654
  · exact batchC02703MinusFourthP009Bound2654
  · exact batchC02703MinusFourthP010Bound2654
  · exact batchC02703MinusFourthP011Bound2654
  · exact batchC02703MinusFourthP012Bound2654
  · exact batchC02703MinusFourthP013Bound2654
  · exact batchC02703MinusFourthP014Bound2654
  · exact batchC02703MinusFourthP015Bound2654
  · exact batchC02703MinusFourthP016Bound2654
  · exact batchC02703MinusFourthP017Bound2654
  · exact batchC02703MinusFourthP018Bound2654
  · exact batchC02703MinusFourthP019Bound2654
  · exact batchC02703MinusFourthP020Bound2654
  · exact batchC02703MinusFourthP021Bound2654
  · exact batchC02703MinusFourthP022Bound2654
  · exact batchC02703MinusFourthP023Bound2654
  · exact batchC02703MinusFourthP024Bound2654
  · exact batchC02703MinusFourthP025Bound2654
  · exact batchC02703MinusFourthP026Bound2654
  · exact batchC02703MinusFourthP027Bound2654
  · exact batchC02703MinusFourthP028Bound2654
  · exact batchC02703MinusFourthP029Bound2654

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP001Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP002Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP003Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP004Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP006Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP007Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP008Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP009Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP010Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP011Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP012Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP013Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP014Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP015Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP016Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP017Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP018Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP019Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP020Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP021Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP022Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP023Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP024Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP025Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP026Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP027Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP028Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP029Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP000Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusFourthP005Bound2654
