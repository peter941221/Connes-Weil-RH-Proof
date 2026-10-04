import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteANeighborRight2557
import ConnesWeilRH.Dev.C1RouteABatchN02703Plus2558

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC02702PlusFourthCell2558 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 neighborRightPosition2557 batchN02703PlusPosition2558 < storedWidth i ^ 2
      then
    weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 neighborRightPosition2557 batchN02703PlusPosition2558 / (storedWidth i ^
          2))
      (min (max |neighborRightPosition2557| |batchN02703PlusPosition2558|) (storedWidth i ^ 2) /
        (storedWidth i ^ 2)) neighborRightPosition2557 batchN02703PlusPosition2558
  else 0


def batchC02702PlusFourthP001Input2558 : RatPair2542 := ((((-((340 * 10^40
        + 1342439253873258425104217711532251719251) * 10^40
        + 716821260981140458137600388969873699153)) : ℚ) /
        ((474 * 10^40
        + 7839386018522558480959354946109039389323) * 10^40
        + 5239039017036472922670581914009600000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP001Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP001Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP001ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP001Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02702PlusFourthP001Upper2558 : ℝ := ((362889182315 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702PlusFourthP001Exponent2558 : ℝ := (((-((340 * 10^40
        + 1342439253873258425104217711532251719251) * 10^40
        + 716821260981140458137600388969873699153)) : ℝ) /
        ((1 * 10^40
        + 8546247601634853744066247480258238435114) * 10^40
        + 5450152496160298722354181960601600000000))

theorem batchC02702PlusFourthP001ExpBound2558 :
    Real.exp batchC02702PlusFourthP001Exponent2558 ≤ batchC02702PlusFourthP001ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP001Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP001Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP001Input2558 8).1 =
      batchC02702PlusFourthP001Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP001Input2558 8).2 : ℝ) =
      batchC02702PlusFourthP001Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP001Input2558 8).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP001Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP001Input2558 hz 8
  rw [hc, he] at h
  have ha : (2 : ℂ)^8 * embedPair2542 batchC02702PlusFourthP001Input2558 =
      (batchC02702PlusFourthP001Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP001Input2558,
        batchC02702PlusFourthP001Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP001Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP001Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP001Center2558))).trans
  norm_num [batchC02702PlusFourthP001Error2558, batchC02702PlusFourthP001ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP001Center2558]

theorem batchC02702PlusFourthP001Bound2558 : batchC02702PlusFourthCell2558 ⟨1, by omega⟩ ≤
    batchC02702PlusFourthP001Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      batchC02702PlusFourthP001Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP001Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP001Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((95747235859475304986077221613469696 : ℝ) /
        104779244925114570282650713456640625) ((31928949980445633354893769391996928 : ℝ) /
        34926414975038190094216904485546875) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP001ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP001Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((95747235859475304986077221613469696 : ℝ) /
        104779244925114570282650713456640625) ((31928949980445633354893769391996928 : ℝ) /
        34926414975038190094216904485546875) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP001ExpUpper2558, batchC02702PlusFourthP001Frequency2558,
        batchC02702PlusFourthP001Upper2558]

def batchC02702PlusFourthP002Input2558 : RatPair2542 := ((((-((9034 * 10^40
        + 121958995836850665082431815495461739324) * 10^40
        + 1151769464373665887696246711951817077073)) : ℚ) /
        ((9186 * 10^40
        + 469984347109554737574495997004658714253) * 10^40
        + 8181107099162356690682327656038400000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP002Center2558 : RatPair2542 := (((84505410219980796999 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP002Error2558 : ℝ := ((127194533801862821 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP002ExpUpper2558 : ℝ := ((743317449174797825977192248616613
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP002Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02702PlusFourthP002Upper2558 : ℝ := ((7444270971472828367700988101 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02702PlusFourthP002Exponent2558 : ℝ := (((-((9034 * 10^40
        + 121958995836850665082431815495461739324) * 10^40
        + 1151769464373665887696246711951817077073)) : ℝ) /
        ((143 * 10^40
        + 5319843505423586792774601499953197792410) * 10^40
        + 2159079798424411823291911369625600000000))

theorem batchC02702PlusFourthP002ExpBound2558 :
    Real.exp batchC02702PlusFourthP002Exponent2558 ≤ batchC02702PlusFourthP002ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP002Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP002Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP002Input2558 6).1 =
      batchC02702PlusFourthP002Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP002Input2558 6).2 : ℝ) =
      batchC02702PlusFourthP002Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP002Input2558 6).2 =
        ((127194533801862821 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP002Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP002Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02702PlusFourthP002Input2558 =
      (batchC02702PlusFourthP002Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP002Input2558,
        batchC02702PlusFourthP002Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP002Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP002Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP002Center2558))).trans
  norm_num [batchC02702PlusFourthP002Error2558, batchC02702PlusFourthP002ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP002Center2558]

theorem batchC02702PlusFourthP002Bound2558 : batchC02702PlusFourthCell2558 ⟨2, by omega⟩ ≤
    batchC02702PlusFourthP002Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      batchC02702PlusFourthP002Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP002Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP002Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((382988943437901219944308886453878784 : ℝ) /
        535582378596426958724104076656640625) ((127715799921782533419575077567987712 : ℝ) /
        178527459532142319574701358885546875) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP002ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP002Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((382988943437901219944308886453878784 : ℝ) /
        535582378596426958724104076656640625) ((127715799921782533419575077567987712 : ℝ) /
        178527459532142319574701358885546875) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP002ExpUpper2558, batchC02702PlusFourthP002Frequency2558,
        batchC02702PlusFourthP002Upper2558]

def batchC02702PlusFourthP003Input2558 : RatPair2542 := ((((-((1204017 * 10^40
        + 9215552606038699152080738473326018463805) * 10^40
        + 4034063249232261059340317651547326123771)) : ℚ) /
        ((1662549 * 10^40
        + 1160697013185068114187556550860144082453) * 10^40
        + 1451674810557733938225293315276800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP003Center2558 : RatPair2542 := (((5429298343613002153233162827 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP003Error2558 : ℝ := ((1576411260228435144735031 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP003ExpUpper2558 : ℝ := (((1 * 10^40
        + 1939153318934946717410435910794392500535) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP003Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02702PlusFourthP003Upper2558 : ℝ := ((45243910607801792034903223732650881
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702PlusFourthP003Exponent2558 : ℝ := (((-((1204017 * 10^40
        + 9215552606038699152080738473326018463805) * 10^40
        + 4034063249232261059340317651547326123771)) : ℝ) /
        ((25977 * 10^40
        + 3299385890831016689284180571107189751288) * 10^40
        + 3303932418914964592784770208051200000000))

theorem batchC02702PlusFourthP003ExpBound2558 :
    Real.exp batchC02702PlusFourthP003Exponent2558 ≤ batchC02702PlusFourthP003ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP003Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP003Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP003Input2558 6).1 =
      batchC02702PlusFourthP003Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP003Input2558 6).2 : ℝ) =
      batchC02702PlusFourthP003Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP003Input2558 6).2 =
        ((1576411260228435144735031 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP003Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP003Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02702PlusFourthP003Input2558 =
      (batchC02702PlusFourthP003Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP003Input2558,
        batchC02702PlusFourthP003Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP003Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP003Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP003Center2558))).trans
  norm_num [batchC02702PlusFourthP003Error2558, batchC02702PlusFourthP003ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP003Center2558]

theorem batchC02702PlusFourthP003Bound2558 : batchC02702PlusFourthCell2558 ⟨3, by omega⟩ ≤
    batchC02702PlusFourthP003Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      batchC02702PlusFourthP003Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP003Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP003Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP003ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP003Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP003ExpUpper2558, batchC02702PlusFourthP003Frequency2558,
        batchC02702PlusFourthP003Upper2558]

def batchC02702PlusFourthP004Input2558 : RatPair2542 := ((((-((21030 * 10^40
        + 2123584538409079574289961932172921746148) * 10^40
        + 9702161488119280594243368562537754577073)) : ℚ) /
        ((33523 * 10^40
        + 594012153792735504303281563601896545010) * 10^40
        + 4045398226455636690682327656038400000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP004Center2558 : RatPair2542 := (((5346865452589795239392158194561 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP004Error2558 : ℝ := ((704575430340606075960108611 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP004ExpUpper2558 : ℝ := (((587 * 10^40
        + 8940737276265423046037793917538379834947) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP004Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02702PlusFourthP004Upper2558 : ℝ :=
    ((12497187888535478529027819990025760817 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702PlusFourthP004Exponent2558 : ℝ := (((-((21030 * 10^40
        + 2123584538409079574289961932172921746148) * 10^40
        + 9702161488119280594243368562537754577073)) : ℝ) /
        ((523 * 10^40
        + 7978031439903011492254738774431279633515) * 10^40
        + 7875709347288369323291911369625600000000))

theorem batchC02702PlusFourthP004ExpBound2558 :
    Real.exp batchC02702PlusFourthP004Exponent2558 ≤ batchC02702PlusFourthP004ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP004Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP004Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP004Input2558 6).1 =
      batchC02702PlusFourthP004Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP004Input2558 6).2 : ℝ) =
      batchC02702PlusFourthP004Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP004Input2558 6).2 =
        ((704575430340606075960108611 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP004Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP004Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02702PlusFourthP004Input2558 =
      (batchC02702PlusFourthP004Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP004Input2558,
        batchC02702PlusFourthP004Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP004Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP004Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP004Center2558))).trans
  norm_num [batchC02702PlusFourthP004Error2558, batchC02702PlusFourthP004ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP004Center2558]

theorem batchC02702PlusFourthP004Bound2558 : batchC02702PlusFourthCell2558 ⟨4, by omega⟩ ≤
    batchC02702PlusFourthP004Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      batchC02702PlusFourthP004Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP004Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP004Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((382988943437901219944308886453878784 : ℝ) /
        811296384146067132209863967375390625) ((127715799921782533419575077567987712 : ℝ) /
        270432128048689044069954655791796875) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP004ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP004Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((382988943437901219944308886453878784 : ℝ) /
        811296384146067132209863967375390625) ((127715799921782533419575077567987712 : ℝ) /
        270432128048689044069954655791796875) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP004ExpUpper2558, batchC02702PlusFourthP004Frequency2558,
        batchC02702PlusFourthP004Upper2558]

def batchC02702PlusFourthP006Input2558 : RatPair2542 := ((((-43839478189018415751735075264883429)
    : ℚ) /
        73628896602487849615844966400000000),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP006Center2558 : RatPair2542 := (((582152360891653 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP006Error2558 : ℝ := ((2496231124509 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP006ExpUpper2558 : ℝ := ((1280166579875248081833831965 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP006Frequency2558 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02702PlusFourthP006Upper2558 : ℝ := ((8793357323222247873923 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02702PlusFourthP006Exponent2558 : ℝ :=
    (((-43839478189018415751735075264883429) : ℝ)
    /
        575225754706936325123788800000000)

theorem batchC02702PlusFourthP006ExpBound2558 :
    Real.exp batchC02702PlusFourthP006Exponent2558 ≤ batchC02702PlusFourthP006ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP006Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP006Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP006Input2558 7).1 =
      batchC02702PlusFourthP006Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP006Input2558 7).2 : ℝ) =
      batchC02702PlusFourthP006Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP006Input2558 7).2 =
        ((2496231124509 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP006Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP006Input2558 hz 7
  rw [hc, he] at h
  have ha : (2 : ℂ)^7 * embedPair2542 batchC02702PlusFourthP006Input2558 =
      (batchC02702PlusFourthP006Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP006Input2558,
        batchC02702PlusFourthP006Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP006Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP006Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP006Center2558))).trans
  norm_num [batchC02702PlusFourthP006Error2558, batchC02702PlusFourthP006ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP006Center2558]

theorem batchC02702PlusFourthP006Bound2558 : batchC02702PlusFourthCell2558 ⟨6, by omega⟩ ≤
    batchC02702PlusFourthP006Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      batchC02702PlusFourthP006Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP006Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP006Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) ((158400514417 : ℝ) /
        204800000000) ((79233025209 : ℝ) /
        102400000000) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP006ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP006Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) ((158400514417 : ℝ) /
        204800000000) ((79233025209 : ℝ) /
        102400000000) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP006ExpUpper2558, batchC02702PlusFourthP006Frequency2558,
        batchC02702PlusFourthP006Upper2558]

def batchC02702PlusFourthP007Input2558 : RatPair2542 := ((((-((1204017 * 10^40
        + 9215552606038699152080738473326018463805) * 10^40
        + 4034063249232261059340317651547326123771)) : ℚ) /
        ((1662549 * 10^40
        + 1160697013185068114187556550860144082453) * 10^40
        + 1451674810557733938225293315276800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP007Center2558 : RatPair2542 := (((5429298343613002153233162827 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP007Error2558 : ℝ := ((1576411260228435144735031 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP007ExpUpper2558 : ℝ := (((1 * 10^40
        + 1939153318934946717410435910794392500535) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP007Frequency2558 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02702PlusFourthP007Upper2558 : ℝ := ((294770669928524686083353059643999 :
    ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702PlusFourthP007Exponent2558 : ℝ := (((-((1204017 * 10^40
        + 9215552606038699152080738473326018463805) * 10^40
        + 4034063249232261059340317651547326123771)) : ℝ) /
        ((25977 * 10^40
        + 3299385890831016689284180571107189751288) * 10^40
        + 3303932418914964592784770208051200000000))

theorem batchC02702PlusFourthP007ExpBound2558 :
    Real.exp batchC02702PlusFourthP007Exponent2558 ≤ batchC02702PlusFourthP007ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP007Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP007Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP007Input2558 6).1 =
      batchC02702PlusFourthP007Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP007Input2558 6).2 : ℝ) =
      batchC02702PlusFourthP007Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP007Input2558 6).2 =
        ((1576411260228435144735031 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP007Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP007Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02702PlusFourthP007Input2558 =
      (batchC02702PlusFourthP007Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP007Input2558,
        batchC02702PlusFourthP007Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP007Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP007Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP007Center2558))).trans
  norm_num [batchC02702PlusFourthP007Error2558, batchC02702PlusFourthP007ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP007Center2558]

theorem batchC02702PlusFourthP007Bound2558 : batchC02702PlusFourthCell2558 ⟨7, by omega⟩ ≤
    batchC02702PlusFourthP007Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      batchC02702PlusFourthP007Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP007Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP007Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP007ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP007Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP007ExpUpper2558, batchC02702PlusFourthP007Frequency2558,
        batchC02702PlusFourthP007Upper2558]

def batchC02702PlusFourthP008Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP008Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP008Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP008ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP008Frequency2558 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def batchC02702PlusFourthP008Upper2558 : ℝ := ((230519614231944883708648147 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702PlusFourthP008Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP008ExpBound2558 :
    Real.exp batchC02702PlusFourthP008Exponent2558 ≤ batchC02702PlusFourthP008ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP008Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP008Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP008Input2558 14).1 =
      batchC02702PlusFourthP008Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP008Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP008Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP008Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP008Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP008Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP008Input2558 =
      (batchC02702PlusFourthP008Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP008Input2558,
        batchC02702PlusFourthP008Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP008Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP008Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP008Center2558))).trans
  norm_num [batchC02702PlusFourthP008Error2558, batchC02702PlusFourthP008ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP008Center2558]

theorem batchC02702PlusFourthP008Bound2558 : batchC02702PlusFourthCell2558 ⟨8, by omega⟩ ≤
    batchC02702PlusFourthP008Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      batchC02702PlusFourthP008Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP008Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP008Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP008ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP008Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP008ExpUpper2558, batchC02702PlusFourthP008Frequency2558,
        batchC02702PlusFourthP008Upper2558]

def batchC02702PlusFourthP009Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP009Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP009Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP009ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP009Frequency2558 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def batchC02702PlusFourthP009Upper2558 : ℝ := ((230521500397028855372170471 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702PlusFourthP009Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP009ExpBound2558 :
    Real.exp batchC02702PlusFourthP009Exponent2558 ≤ batchC02702PlusFourthP009ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP009Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP009Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP009Input2558 14).1 =
      batchC02702PlusFourthP009Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP009Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP009Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP009Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP009Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP009Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP009Input2558 =
      (batchC02702PlusFourthP009Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP009Input2558,
        batchC02702PlusFourthP009Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP009Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP009Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP009Center2558))).trans
  norm_num [batchC02702PlusFourthP009Error2558, batchC02702PlusFourthP009ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP009Center2558]

theorem batchC02702PlusFourthP009Bound2558 : batchC02702PlusFourthCell2558 ⟨9, by omega⟩ ≤
    batchC02702PlusFourthP009Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      batchC02702PlusFourthP009Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP009Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP009Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP009ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP009Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP009ExpUpper2558, batchC02702PlusFourthP009Frequency2558,
        batchC02702PlusFourthP009Upper2558]

def batchC02702PlusFourthP010Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP010Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP010Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP010ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP010Frequency2558 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def batchC02702PlusFourthP010Upper2558 : ℝ := ((115261296491366427178456109 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702PlusFourthP010Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP010ExpBound2558 :
    Real.exp batchC02702PlusFourthP010Exponent2558 ≤ batchC02702PlusFourthP010ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP010Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP010Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP010Input2558 14).1 =
      batchC02702PlusFourthP010Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP010Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP010Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP010Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP010Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP010Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP010Input2558 =
      (batchC02702PlusFourthP010Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP010Input2558,
        batchC02702PlusFourthP010Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP010Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP010Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP010Center2558))).trans
  norm_num [batchC02702PlusFourthP010Error2558, batchC02702PlusFourthP010ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP010Center2558]

theorem batchC02702PlusFourthP010Bound2558 : batchC02702PlusFourthCell2558 ⟨10, by omega⟩ ≤
    batchC02702PlusFourthP010Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      batchC02702PlusFourthP010Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP010Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP010Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP010ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP010Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP010ExpUpper2558, batchC02702PlusFourthP010Frequency2558,
        batchC02702PlusFourthP010Upper2558]

def batchC02702PlusFourthP011Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP011Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP011Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP011ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP011Frequency2558 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def batchC02702PlusFourthP011Upper2558 : ℝ := ((230523321486106722745214547 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702PlusFourthP011Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP011ExpBound2558 :
    Real.exp batchC02702PlusFourthP011Exponent2558 ≤ batchC02702PlusFourthP011ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP011Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP011Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP011Input2558 14).1 =
      batchC02702PlusFourthP011Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP011Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP011Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP011Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP011Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP011Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP011Input2558 =
      (batchC02702PlusFourthP011Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP011Input2558,
        batchC02702PlusFourthP011Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP011Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP011Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP011Center2558))).trans
  norm_num [batchC02702PlusFourthP011Error2558, batchC02702PlusFourthP011ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP011Center2558]

theorem batchC02702PlusFourthP011Bound2558 : batchC02702PlusFourthCell2558 ⟨11, by omega⟩ ≤
    batchC02702PlusFourthP011Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      batchC02702PlusFourthP011Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP011Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP011Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP011ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP011Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP011ExpUpper2558, batchC02702PlusFourthP011Frequency2558,
        batchC02702PlusFourthP011Upper2558]

def batchC02702PlusFourthP012Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP012Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP012Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP012ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP012Frequency2558 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def batchC02702PlusFourthP012Upper2558 : ℝ := ((230524076063391183204327605 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702PlusFourthP012Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP012ExpBound2558 :
    Real.exp batchC02702PlusFourthP012Exponent2558 ≤ batchC02702PlusFourthP012ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP012Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP012Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP012Input2558 14).1 =
      batchC02702PlusFourthP012Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP012Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP012Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP012Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP012Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP012Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP012Input2558 =
      (batchC02702PlusFourthP012Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP012Input2558,
        batchC02702PlusFourthP012Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP012Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP012Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP012Center2558))).trans
  norm_num [batchC02702PlusFourthP012Error2558, batchC02702PlusFourthP012ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP012Center2558]

theorem batchC02702PlusFourthP012Bound2558 : batchC02702PlusFourthCell2558 ⟨12, by omega⟩ ≤
    batchC02702PlusFourthP012Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      batchC02702PlusFourthP012Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP012Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP012Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP012ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP012Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP012ExpUpper2558, batchC02702PlusFourthP012Frequency2558,
        batchC02702PlusFourthP012Upper2558]

def batchC02702PlusFourthP013Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP013Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP013Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP013ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP013Frequency2558 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def batchC02702PlusFourthP013Upper2558 : ℝ := ((230524763716718838376568479 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702PlusFourthP013Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP013ExpBound2558 :
    Real.exp batchC02702PlusFourthP013Exponent2558 ≤ batchC02702PlusFourthP013ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP013Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP013Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP013Input2558 14).1 =
      batchC02702PlusFourthP013Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP013Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP013Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP013Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP013Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP013Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP013Input2558 =
      (batchC02702PlusFourthP013Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP013Input2558,
        batchC02702PlusFourthP013Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP013Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP013Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP013Center2558))).trans
  norm_num [batchC02702PlusFourthP013Error2558, batchC02702PlusFourthP013ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP013Center2558]

theorem batchC02702PlusFourthP013Bound2558 : batchC02702PlusFourthCell2558 ⟨13, by omega⟩ ≤
    batchC02702PlusFourthP013Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      batchC02702PlusFourthP013Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP013Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP013Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP013ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP013Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP013ExpUpper2558, batchC02702PlusFourthP013Frequency2558,
        batchC02702PlusFourthP013Upper2558]

def batchC02702PlusFourthP014Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP014Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP014Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP014ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP014Frequency2558 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def batchC02702PlusFourthP014Upper2558 : ℝ := ((28815754737785892410657553 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC02702PlusFourthP014Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP014ExpBound2558 :
    Real.exp batchC02702PlusFourthP014Exponent2558 ≤ batchC02702PlusFourthP014ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP014Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP014Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP014Input2558 14).1 =
      batchC02702PlusFourthP014Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP014Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP014Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP014Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP014Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP014Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP014Input2558 =
      (batchC02702PlusFourthP014Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP014Input2558,
        batchC02702PlusFourthP014Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP014Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP014Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP014Center2558))).trans
  norm_num [batchC02702PlusFourthP014Error2558, batchC02702PlusFourthP014ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP014Center2558]

theorem batchC02702PlusFourthP014Bound2558 : batchC02702PlusFourthCell2558 ⟨14, by omega⟩ ≤
    batchC02702PlusFourthP014Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      batchC02702PlusFourthP014Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP014Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP014Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP014ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP014Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP014ExpUpper2558, batchC02702PlusFourthP014Frequency2558,
        batchC02702PlusFourthP014Upper2558]

def batchC02702PlusFourthP015Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP015Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP015Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP015ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP015Frequency2558 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def batchC02702PlusFourthP015Upper2558 : ℝ := ((115263475440922554739804001 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702PlusFourthP015Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP015ExpBound2558 :
    Real.exp batchC02702PlusFourthP015Exponent2558 ≤ batchC02702PlusFourthP015ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP015Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP015Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP015Input2558 14).1 =
      batchC02702PlusFourthP015Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP015Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP015Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP015Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP015Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP015Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP015Input2558 =
      (batchC02702PlusFourthP015Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP015Input2558,
        batchC02702PlusFourthP015Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP015Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP015Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP015Center2558))).trans
  norm_num [batchC02702PlusFourthP015Error2558, batchC02702PlusFourthP015ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP015Center2558]

theorem batchC02702PlusFourthP015Bound2558 : batchC02702PlusFourthCell2558 ⟨15, by omega⟩ ≤
    batchC02702PlusFourthP015Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      batchC02702PlusFourthP015Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP015Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP015Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP015ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP015Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP015ExpUpper2558, batchC02702PlusFourthP015Frequency2558,
        batchC02702PlusFourthP015Upper2558]

def batchC02702PlusFourthP016Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP016Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP016Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP016ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP016Frequency2558 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def batchC02702PlusFourthP016Upper2558 : ℝ := ((230527610680978800329024055 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702PlusFourthP016Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP016ExpBound2558 :
    Real.exp batchC02702PlusFourthP016Exponent2558 ≤ batchC02702PlusFourthP016ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP016Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP016Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP016Input2558 14).1 =
      batchC02702PlusFourthP016Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP016Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP016Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP016Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP016Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP016Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP016Input2558 =
      (batchC02702PlusFourthP016Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP016Input2558,
        batchC02702PlusFourthP016Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP016Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP016Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP016Center2558))).trans
  norm_num [batchC02702PlusFourthP016Error2558, batchC02702PlusFourthP016ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP016Center2558]

theorem batchC02702PlusFourthP016Bound2558 : batchC02702PlusFourthCell2558 ⟨16, by omega⟩ ≤
    batchC02702PlusFourthP016Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      batchC02702PlusFourthP016Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP016Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP016Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP016ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP016Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP016ExpUpper2558, batchC02702PlusFourthP016Frequency2558,
        batchC02702PlusFourthP016Upper2558]

def batchC02702PlusFourthP017Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP017Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP017Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP017ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP017Frequency2558 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def batchC02702PlusFourthP017Upper2558 : ℝ := ((230528892316968280645513857 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702PlusFourthP017Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP017ExpBound2558 :
    Real.exp batchC02702PlusFourthP017Exponent2558 ≤ batchC02702PlusFourthP017ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP017Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP017Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP017Input2558 14).1 =
      batchC02702PlusFourthP017Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP017Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP017Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP017Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP017Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP017Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP017Input2558 =
      (batchC02702PlusFourthP017Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP017Input2558,
        batchC02702PlusFourthP017Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP017Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP017Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP017Center2558))).trans
  norm_num [batchC02702PlusFourthP017Error2558, batchC02702PlusFourthP017ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP017Center2558]

theorem batchC02702PlusFourthP017Bound2558 : batchC02702PlusFourthCell2558 ⟨17, by omega⟩ ≤
    batchC02702PlusFourthP017Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      batchC02702PlusFourthP017Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP017Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP017Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP017ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP017Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP017ExpUpper2558, batchC02702PlusFourthP017Frequency2558,
        batchC02702PlusFourthP017Upper2558]

def batchC02702PlusFourthP018Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP018Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP018Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP018ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP018Frequency2558 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def batchC02702PlusFourthP018Upper2558 : ℝ := ((115264688440720219750511661 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702PlusFourthP018Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP018ExpBound2558 :
    Real.exp batchC02702PlusFourthP018Exponent2558 ≤ batchC02702PlusFourthP018ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP018Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP018Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP018Input2558 14).1 =
      batchC02702PlusFourthP018Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP018Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP018Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP018Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP018Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP018Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP018Input2558 =
      (batchC02702PlusFourthP018Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP018Input2558,
        batchC02702PlusFourthP018Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP018Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP018Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP018Center2558))).trans
  norm_num [batchC02702PlusFourthP018Error2558, batchC02702PlusFourthP018ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP018Center2558]

theorem batchC02702PlusFourthP018Bound2558 : batchC02702PlusFourthCell2558 ⟨18, by omega⟩ ≤
    batchC02702PlusFourthP018Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      batchC02702PlusFourthP018Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP018Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP018Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP018ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP018Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP018ExpUpper2558, batchC02702PlusFourthP018Frequency2558,
        batchC02702PlusFourthP018Upper2558]

def batchC02702PlusFourthP019Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP019Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP019Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP019ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP019Frequency2558 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def batchC02702PlusFourthP019Upper2558 : ℝ := ((57632563156891911197349453 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02702PlusFourthP019Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP019ExpBound2558 :
    Real.exp batchC02702PlusFourthP019Exponent2558 ≤ batchC02702PlusFourthP019ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP019Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP019Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP019Input2558 14).1 =
      batchC02702PlusFourthP019Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP019Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP019Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP019Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP019Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP019Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP019Input2558 =
      (batchC02702PlusFourthP019Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP019Input2558,
        batchC02702PlusFourthP019Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP019Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP019Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP019Center2558))).trans
  norm_num [batchC02702PlusFourthP019Error2558, batchC02702PlusFourthP019ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP019Center2558]

theorem batchC02702PlusFourthP019Bound2558 : batchC02702PlusFourthCell2558 ⟨19, by omega⟩ ≤
    batchC02702PlusFourthP019Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      batchC02702PlusFourthP019Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP019Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP019Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP019ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP019Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP019ExpUpper2558, batchC02702PlusFourthP019Frequency2558,
        batchC02702PlusFourthP019Upper2558]

def batchC02702PlusFourthP020Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP020Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP020Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP020ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP020Frequency2558 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def batchC02702PlusFourthP020Upper2558 : ℝ := ((57632801234914228725317759 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02702PlusFourthP020Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP020ExpBound2558 :
    Real.exp batchC02702PlusFourthP020Exponent2558 ≤ batchC02702PlusFourthP020ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP020Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP020Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP020Input2558 14).1 =
      batchC02702PlusFourthP020Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP020Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP020Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP020Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP020Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP020Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP020Input2558 =
      (batchC02702PlusFourthP020Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP020Input2558,
        batchC02702PlusFourthP020Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP020Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP020Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP020Center2558))).trans
  norm_num [batchC02702PlusFourthP020Error2558, batchC02702PlusFourthP020ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP020Center2558]

theorem batchC02702PlusFourthP020Bound2558 : batchC02702PlusFourthCell2558 ⟨20, by omega⟩ ≤
    batchC02702PlusFourthP020Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      batchC02702PlusFourthP020Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP020Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP020Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP020ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP020Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP020ExpUpper2558, batchC02702PlusFourthP020Frequency2558,
        batchC02702PlusFourthP020Upper2558]

def batchC02702PlusFourthP021Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP021Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP021Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP021ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP021Frequency2558 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def batchC02702PlusFourthP021Upper2558 : ℝ := ((230531999687170628724906351 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702PlusFourthP021Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP021ExpBound2558 :
    Real.exp batchC02702PlusFourthP021Exponent2558 ≤ batchC02702PlusFourthP021ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP021Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP021Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP021Input2558 14).1 =
      batchC02702PlusFourthP021Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP021Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP021Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP021Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP021Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP021Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP021Input2558 =
      (batchC02702PlusFourthP021Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP021Input2558,
        batchC02702PlusFourthP021Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP021Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP021Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP021Center2558))).trans
  norm_num [batchC02702PlusFourthP021Error2558, batchC02702PlusFourthP021ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP021Center2558]

theorem batchC02702PlusFourthP021Bound2558 : batchC02702PlusFourthCell2558 ⟨21, by omega⟩ ≤
    batchC02702PlusFourthP021Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      batchC02702PlusFourthP021Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP021Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP021Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP021ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP021Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP021ExpUpper2558, batchC02702PlusFourthP021Frequency2558,
        batchC02702PlusFourthP021Upper2558]

def batchC02702PlusFourthP022Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP022Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP022Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP022ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP022Frequency2558 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def batchC02702PlusFourthP022Upper2558 : ℝ := ((115266203235076305292278543 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702PlusFourthP022Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP022ExpBound2558 :
    Real.exp batchC02702PlusFourthP022Exponent2558 ≤ batchC02702PlusFourthP022ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP022Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP022Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP022Input2558 14).1 =
      batchC02702PlusFourthP022Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP022Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP022Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP022Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP022Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP022Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP022Input2558 =
      (batchC02702PlusFourthP022Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP022Input2558,
        batchC02702PlusFourthP022Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP022Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP022Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP022Center2558))).trans
  norm_num [batchC02702PlusFourthP022Error2558, batchC02702PlusFourthP022ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP022Center2558]

theorem batchC02702PlusFourthP022Bound2558 : batchC02702PlusFourthCell2558 ⟨22, by omega⟩ ≤
    batchC02702PlusFourthP022Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      batchC02702PlusFourthP022Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP022Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP022Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP022ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP022Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP022ExpUpper2558, batchC02702PlusFourthP022Frequency2558,
        batchC02702PlusFourthP022Upper2558]

def batchC02702PlusFourthP023Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP023Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP023Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP023ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP023Frequency2558 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def batchC02702PlusFourthP023Upper2558 : ℝ := ((57633394826928893941978997 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02702PlusFourthP023Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP023ExpBound2558 :
    Real.exp batchC02702PlusFourthP023Exponent2558 ≤ batchC02702PlusFourthP023ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP023Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP023Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP023Input2558 14).1 =
      batchC02702PlusFourthP023Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP023Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP023Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP023Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP023Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP023Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP023Input2558 =
      (batchC02702PlusFourthP023Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP023Input2558,
        batchC02702PlusFourthP023Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP023Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP023Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP023Center2558))).trans
  norm_num [batchC02702PlusFourthP023Error2558, batchC02702PlusFourthP023ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP023Center2558]

theorem batchC02702PlusFourthP023Bound2558 : batchC02702PlusFourthCell2558 ⟨23, by omega⟩ ≤
    batchC02702PlusFourthP023Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      batchC02702PlusFourthP023Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP023Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP023Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP023ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP023Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP023ExpUpper2558, batchC02702PlusFourthP023Frequency2558,
        batchC02702PlusFourthP023Upper2558]

def batchC02702PlusFourthP024Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP024Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP024Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP024ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP024Frequency2558 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def batchC02702PlusFourthP024Upper2558 : ℝ := ((230534118299463269759698121 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702PlusFourthP024Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP024ExpBound2558 :
    Real.exp batchC02702PlusFourthP024Exponent2558 ≤ batchC02702PlusFourthP024ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP024Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP024Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP024Input2558 14).1 =
      batchC02702PlusFourthP024Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP024Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP024Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP024Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP024Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP024Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP024Input2558 =
      (batchC02702PlusFourthP024Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP024Input2558,
        batchC02702PlusFourthP024Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP024Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP024Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP024Center2558))).trans
  norm_num [batchC02702PlusFourthP024Error2558, batchC02702PlusFourthP024ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP024Center2558]

theorem batchC02702PlusFourthP024Bound2558 : batchC02702PlusFourthCell2558 ⟨24, by omega⟩ ≤
    batchC02702PlusFourthP024Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      batchC02702PlusFourthP024Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP024Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP024Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP024ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP024Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP024ExpUpper2558, batchC02702PlusFourthP024Frequency2558,
        batchC02702PlusFourthP024Upper2558]

def batchC02702PlusFourthP025Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP025Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP025Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP025ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP025Frequency2558 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def batchC02702PlusFourthP025Upper2558 : ℝ := ((115267397049396243035567933 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702PlusFourthP025Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP025ExpBound2558 :
    Real.exp batchC02702PlusFourthP025Exponent2558 ≤ batchC02702PlusFourthP025ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP025Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP025Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP025Input2558 14).1 =
      batchC02702PlusFourthP025Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP025Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP025Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP025Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP025Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP025Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP025Input2558 =
      (batchC02702PlusFourthP025Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP025Input2558,
        batchC02702PlusFourthP025Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP025Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP025Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP025Center2558))).trans
  norm_num [batchC02702PlusFourthP025Error2558, batchC02702PlusFourthP025ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP025Center2558]

theorem batchC02702PlusFourthP025Bound2558 : batchC02702PlusFourthCell2558 ⟨25, by omega⟩ ≤
    batchC02702PlusFourthP025Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      batchC02702PlusFourthP025Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP025Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP025Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP025ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP025Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP025ExpUpper2558, batchC02702PlusFourthP025Frequency2558,
        batchC02702PlusFourthP025Upper2558]

def batchC02702PlusFourthP026Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP026Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP026Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP026ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP026Frequency2558 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def batchC02702PlusFourthP026Upper2558 : ℝ := ((230535484741077055216212369 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702PlusFourthP026Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP026ExpBound2558 :
    Real.exp batchC02702PlusFourthP026Exponent2558 ≤ batchC02702PlusFourthP026ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP026Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP026Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP026Input2558 14).1 =
      batchC02702PlusFourthP026Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP026Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP026Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP026Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP026Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP026Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP026Input2558 =
      (batchC02702PlusFourthP026Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP026Input2558,
        batchC02702PlusFourthP026Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP026Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP026Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP026Center2558))).trans
  norm_num [batchC02702PlusFourthP026Error2558, batchC02702PlusFourthP026ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP026Center2558]

theorem batchC02702PlusFourthP026Bound2558 : batchC02702PlusFourthCell2558 ⟨26, by omega⟩ ≤
    batchC02702PlusFourthP026Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      batchC02702PlusFourthP026Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP026Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP026Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP026ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP026Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP026ExpUpper2558, batchC02702PlusFourthP026Frequency2558,
        batchC02702PlusFourthP026Upper2558]

def batchC02702PlusFourthP027Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP027Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP027Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP027ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP027Frequency2558 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def batchC02702PlusFourthP027Upper2558 : ℝ := ((115268240682594395794266497 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702PlusFourthP027Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP027ExpBound2558 :
    Real.exp batchC02702PlusFourthP027Exponent2558 ≤ batchC02702PlusFourthP027ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP027Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP027Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP027Input2558 14).1 =
      batchC02702PlusFourthP027Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP027Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP027Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP027Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP027Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP027Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP027Input2558 =
      (batchC02702PlusFourthP027Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP027Input2558,
        batchC02702PlusFourthP027Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP027Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP027Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP027Center2558))).trans
  norm_num [batchC02702PlusFourthP027Error2558, batchC02702PlusFourthP027ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP027Center2558]

theorem batchC02702PlusFourthP027Bound2558 : batchC02702PlusFourthCell2558 ⟨27, by omega⟩ ≤
    batchC02702PlusFourthP027Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      batchC02702PlusFourthP027Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP027Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP027Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP027ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP027Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP027ExpUpper2558, batchC02702PlusFourthP027Frequency2558,
        batchC02702PlusFourthP027Upper2558]

def batchC02702PlusFourthP028Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP028Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP028Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP028ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP028Frequency2558 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def batchC02702PlusFourthP028Upper2558 : ℝ := ((230536875943882311015916487 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702PlusFourthP028Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP028ExpBound2558 :
    Real.exp batchC02702PlusFourthP028Exponent2558 ≤ batchC02702PlusFourthP028ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP028Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP028Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP028Input2558 14).1 =
      batchC02702PlusFourthP028Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP028Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP028Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP028Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP028Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP028Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP028Input2558 =
      (batchC02702PlusFourthP028Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP028Input2558,
        batchC02702PlusFourthP028Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP028Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP028Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP028Center2558))).trans
  norm_num [batchC02702PlusFourthP028Error2558, batchC02702PlusFourthP028ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP028Center2558]

theorem batchC02702PlusFourthP028Bound2558 : batchC02702PlusFourthCell2558 ⟨28, by omega⟩ ≤
    batchC02702PlusFourthP028Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      batchC02702PlusFourthP028Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP028Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP028Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP028ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP028Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP028ExpUpper2558, batchC02702PlusFourthP028Frequency2558,
        batchC02702PlusFourthP028Upper2558]

def batchC02702PlusFourthP029Input2558 : RatPair2542 := ((((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusFourthP029Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusFourthP029Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP029ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702PlusFourthP029Frequency2558 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def batchC02702PlusFourthP029Upper2558 : ℝ := ((28817184583272447241363359 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC02702PlusFourthP029Exponent2558 : ℝ := (((-((385518 * 10^40
        + 5633377671274824644752445429875525421633) * 10^40
        + 8039441979457663339442052195004357373771)) : ℝ) /
        ((31 * 10^40
        + 8368310269842689229032208652084563506966) * 10^40
        + 8695649206657753842784770208051200000000))

theorem batchC02702PlusFourthP029ExpBound2558 :
    Real.exp batchC02702PlusFourthP029Exponent2558 ≤ batchC02702PlusFourthP029ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702PlusFourthP029Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusFourthP029Input2558]
  have hc : (compactExp2547 batchC02702PlusFourthP029Input2558 14).1 =
      batchC02702PlusFourthP029Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702PlusFourthP029Input2558 14).2 : ℝ) =
      batchC02702PlusFourthP029Error2558 := by
    have hq : (compactExp2547 batchC02702PlusFourthP029Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702PlusFourthP029Error2558]
  have h := compactExp_error2547 batchC02702PlusFourthP029Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702PlusFourthP029Input2558 =
      (batchC02702PlusFourthP029Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702PlusFourthP029Input2558,
        batchC02702PlusFourthP029Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702PlusFourthP029Exponent2558 : ℂ)) (embedPair2542
        batchC02702PlusFourthP029Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702PlusFourthP029Center2558))).trans
  norm_num [batchC02702PlusFourthP029Error2558, batchC02702PlusFourthP029ExpUpper2558,
      pairMagnitude2542,
      batchC02702PlusFourthP029Center2558]

theorem batchC02702PlusFourthP029Bound2558 : batchC02702PlusFourthCell2558 ⟨29, by omega⟩ ≤
    batchC02702PlusFourthP029Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      batchC02702PlusFourthP029Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702PlusFourthP029Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702PlusFourthP029Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702PlusFourthP029ExpBound2558 using 1; norm_num
        [batchC02702PlusFourthP029Exponent2558])
  have hid : batchC02702PlusFourthCell2558 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702PlusFourthCell2558, cellNearAbs2538, neighborRightPosition2557,
      batchN02703PlusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702PlusFourthP029ExpUpper2558, batchC02702PlusFourthP029Frequency2558,
        batchC02702PlusFourthP029Upper2558]

noncomputable def batchC02702PlusFourthP000Upper2558 : ℝ := 0

theorem batchC02702PlusFourthP000Bound2558 :
    batchC02702PlusFourthCell2558 ⟨0, by omega⟩ ≤ batchC02702PlusFourthP000Upper2558 := by
  norm_num [batchC02702PlusFourthCell2558, batchC02702PlusFourthP000Upper2558, cellNearAbs2538,
    neighborRightPosition2557, batchN02703PlusPosition2558, storedWidth]

noncomputable def batchC02702PlusFourthP005Upper2558 : ℝ := 0

theorem batchC02702PlusFourthP005Bound2558 :
    batchC02702PlusFourthCell2558 ⟨5, by omega⟩ ≤ batchC02702PlusFourthP005Upper2558 := by
  norm_num [batchC02702PlusFourthCell2558, batchC02702PlusFourthP005Upper2558, cellNearAbs2538,
    neighborRightPosition2557, batchN02703PlusPosition2558, storedWidth]

noncomputable def batchC02702PlusFourthUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02702PlusFourthP000Upper2558
  | 1 => batchC02702PlusFourthP001Upper2558
  | 2 => batchC02702PlusFourthP002Upper2558
  | 3 => batchC02702PlusFourthP003Upper2558
  | 4 => batchC02702PlusFourthP004Upper2558
  | 5 => batchC02702PlusFourthP005Upper2558
  | 6 => batchC02702PlusFourthP006Upper2558
  | 7 => batchC02702PlusFourthP007Upper2558
  | 8 => batchC02702PlusFourthP008Upper2558
  | 9 => batchC02702PlusFourthP009Upper2558
  | 10 => batchC02702PlusFourthP010Upper2558
  | 11 => batchC02702PlusFourthP011Upper2558
  | 12 => batchC02702PlusFourthP012Upper2558
  | 13 => batchC02702PlusFourthP013Upper2558
  | 14 => batchC02702PlusFourthP014Upper2558
  | 15 => batchC02702PlusFourthP015Upper2558
  | 16 => batchC02702PlusFourthP016Upper2558
  | 17 => batchC02702PlusFourthP017Upper2558
  | 18 => batchC02702PlusFourthP018Upper2558
  | 19 => batchC02702PlusFourthP019Upper2558
  | 20 => batchC02702PlusFourthP020Upper2558
  | 21 => batchC02702PlusFourthP021Upper2558
  | 22 => batchC02702PlusFourthP022Upper2558
  | 23 => batchC02702PlusFourthP023Upper2558
  | 24 => batchC02702PlusFourthP024Upper2558
  | 25 => batchC02702PlusFourthP025Upper2558
  | 26 => batchC02702PlusFourthP026Upper2558
  | 27 => batchC02702PlusFourthP027Upper2558
  | 28 => batchC02702PlusFourthP028Upper2558
  | 29 => batchC02702PlusFourthP029Upper2558
  | _ => 0

theorem batchC02702PlusFourthBound2558 (i : Fin 30) :
    batchC02702PlusFourthCell2558 i ≤ batchC02702PlusFourthUpper2558 i := by
  fin_cases i
  · exact batchC02702PlusFourthP000Bound2558
  · exact batchC02702PlusFourthP001Bound2558
  · exact batchC02702PlusFourthP002Bound2558
  · exact batchC02702PlusFourthP003Bound2558
  · exact batchC02702PlusFourthP004Bound2558
  · exact batchC02702PlusFourthP005Bound2558
  · exact batchC02702PlusFourthP006Bound2558
  · exact batchC02702PlusFourthP007Bound2558
  · exact batchC02702PlusFourthP008Bound2558
  · exact batchC02702PlusFourthP009Bound2558
  · exact batchC02702PlusFourthP010Bound2558
  · exact batchC02702PlusFourthP011Bound2558
  · exact batchC02702PlusFourthP012Bound2558
  · exact batchC02702PlusFourthP013Bound2558
  · exact batchC02702PlusFourthP014Bound2558
  · exact batchC02702PlusFourthP015Bound2558
  · exact batchC02702PlusFourthP016Bound2558
  · exact batchC02702PlusFourthP017Bound2558
  · exact batchC02702PlusFourthP018Bound2558
  · exact batchC02702PlusFourthP019Bound2558
  · exact batchC02702PlusFourthP020Bound2558
  · exact batchC02702PlusFourthP021Bound2558
  · exact batchC02702PlusFourthP022Bound2558
  · exact batchC02702PlusFourthP023Bound2558
  · exact batchC02702PlusFourthP024Bound2558
  · exact batchC02702PlusFourthP025Bound2558
  · exact batchC02702PlusFourthP026Bound2558
  · exact batchC02702PlusFourthP027Bound2558
  · exact batchC02702PlusFourthP028Bound2558
  · exact batchC02702PlusFourthP029Bound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP001Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP002Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP003Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP004Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP006Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP007Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP008Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP009Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP010Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP011Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP012Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP013Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP014Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP015Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP016Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP017Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP018Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP019Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP020Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP021Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP022Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP023Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP024Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP025Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP026Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP027Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP028Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP029Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP000Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusFourthP005Bound2558
