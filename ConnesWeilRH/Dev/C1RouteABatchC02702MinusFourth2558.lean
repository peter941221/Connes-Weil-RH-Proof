import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteABatchN02702Minus2558
import ConnesWeilRH.Dev.C1RouteABatchN02703Minus2558

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC02702MinusFourthCell2558 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 batchN02702MinusPosition2558 batchN02703MinusPosition2558 < storedWidth i ^ 2
      then
    weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 batchN02702MinusPosition2558 batchN02703MinusPosition2558 / (storedWidth i
          ^ 2))
      (min (max |batchN02702MinusPosition2558| |batchN02703MinusPosition2558|) (storedWidth i ^ 2)
          /
        (storedWidth i ^ 2)) batchN02702MinusPosition2558 batchN02703MinusPosition2558
  else 0


def batchC02702MinusFourthP001Input2558 : RatPair2542 := ((((-((167 * 10^40
        + 1976464899839980599808407177355957443399) * 10^40
        + 4034254081734640621354888758682425609319)) : ℚ) /
        ((237 * 10^40
        + 3919693009261279240479677473054519694661) * 10^40
        + 7619519508518236461335290957004800000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP001Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP001Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP001ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP001Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02702MinusFourthP001Upper2558 : ℝ := ((362889182315 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702MinusFourthP001Exponent2558 : ℝ := (((-((167 * 10^40
        + 1976464899839980599808407177355957443399) * 10^40
        + 4034254081734640621354888758682425609319)) : ℝ) /
        (9273123800817426872033123740129119217557 * 10^40
        + 2725076248080149361177090980300800000000))

theorem batchC02702MinusFourthP001ExpBound2558 :
    Real.exp batchC02702MinusFourthP001Exponent2558 ≤ batchC02702MinusFourthP001ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP001Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP001Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP001Input2558 8).1 =
      batchC02702MinusFourthP001Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP001Input2558 8).2 : ℝ) =
      batchC02702MinusFourthP001Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP001Input2558 8).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP001Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP001Input2558 hz 8
  rw [hc, he] at h
  have ha : (2 : ℂ)^8 * embedPair2542 batchC02702MinusFourthP001Input2558 =
      (batchC02702MinusFourthP001Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP001Input2558,
        batchC02702MinusFourthP001Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP001Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP001Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP001Center2558))).trans
  norm_num [batchC02702MinusFourthP001Error2558, batchC02702MinusFourthP001ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP001Center2558]

theorem batchC02702MinusFourthP001Bound2558 : batchC02702MinusFourthCell2558 ⟨1, by omega⟩ ≤
    batchC02702MinusFourthP001Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      batchC02702MinusFourthP001Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP001Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP001Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((95747235859475304986077221613469696 : ℝ) /
        104779244925114570282650713456640625) ((31928949980445633354893769391996928 : ℝ) /
        34926414975038190094216904485546875) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP001ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP001Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((95747235859475304986077221613469696 : ℝ) /
        104779244925114570282650713456640625) ((31928949980445633354893769391996928 : ℝ) /
        34926414975038190094216904485546875) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP001ExpUpper2558, batchC02702MinusFourthP001Frequency2558,
        batchC02702MinusFourthP001Upper2558]

def batchC02702MinusFourthP002Input2558 : RatPair2542 := ((((-((4294 * 10^40
        + 9334083740724301120573623252834604904064) * 10^40
        + 7404501810158573081290179034029893733479)) : ℚ) /
        ((4593 * 10^40
        + 234992173554777368787247998502329357126) * 10^40
        + 9090553549581178345341163828019200000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP002Center2558 : RatPair2542 := (((14922973460224111462585 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP002Error2558 : ℝ := ((1337562325061955927 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02702MinusFourthP002ExpUpper2558 : ℝ :=
    ((8203991420254531329557371797336407 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02702MinusFourthP002Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02702MinusFourthP002Upper2558 : ℝ := ((10270298250063537528653873257 : ℝ)
    /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984))

noncomputable def batchC02702MinusFourthP002Exponent2558 : ℝ := (((-((4294 * 10^40
        + 9334083740724301120573623252834604904064) * 10^40
        + 7404501810158573081290179034029893733479)) : ℝ) /
        ((71 * 10^40
        + 7659921752711793396387300749976598896205) * 10^40
        + 1079539899212205911645955684812800000000))

theorem batchC02702MinusFourthP002ExpBound2558 :
    Real.exp batchC02702MinusFourthP002Exponent2558 ≤ batchC02702MinusFourthP002ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP002Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP002Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP002Input2558 6).1 =
      batchC02702MinusFourthP002Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP002Input2558 6).2 : ℝ) =
      batchC02702MinusFourthP002Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP002Input2558 6).2 =
        ((1337562325061955927 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP002Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP002Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02702MinusFourthP002Input2558 =
      (batchC02702MinusFourthP002Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP002Input2558,
        batchC02702MinusFourthP002Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP002Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP002Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP002Center2558))).trans
  norm_num [batchC02702MinusFourthP002Error2558, batchC02702MinusFourthP002ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP002Center2558]

theorem batchC02702MinusFourthP002Bound2558 : batchC02702MinusFourthCell2558 ⟨2, by omega⟩ ≤
    batchC02702MinusFourthP002Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      batchC02702MinusFourthP002Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP002Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP002Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((382988943437901219944308886453878784 : ℝ) /
        535582378596426958724104076656640625) ((127715799921782533419575077567987712 : ℝ) /
        178527459532142319574701358885546875) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP002ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP002Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((382988943437901219944308886453878784 : ℝ) /
        535582378596426958724104076656640625) ((127715799921782533419575077567987712 : ℝ) /
        178527459532142319574701358885546875) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP002ExpUpper2558, batchC02702MinusFourthP002Frequency2558,
        batchC02702MinusFourthP002Upper2558]

def batchC02702MinusFourthP003Input2558 : RatPair2542 := ((((-((561816 * 10^40
        + 8352833621170274469575365073212893660314) * 10^40
        + 5607494071742219355395916822209053668333)) : ℚ) /
        ((831274 * 10^40
        + 5580348506592534057093778275430072041226) * 10^40
        + 5725837405278866969112646657638400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP003Center2558 : RatPair2542 := (((59923141961018019929683668723 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP003Error2558 : ℝ := ((16577623021621913626370905 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02702MinusFourthP003ExpUpper2558 : ℝ := (((13 * 10^40
        + 1772382718022520239532820938692164871001) : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02702MinusFourthP003Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02702MinusFourthP003Upper2558 : ℝ :=
    ((499356842567383855723343134863188837 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02702MinusFourthP003Exponent2558 : ℝ := (((-((561816 * 10^40
        + 8352833621170274469575365073212893660314) * 10^40
        + 5607494071742219355395916822209053668333)) : ℝ) /
        ((12988 * 10^40
        + 6649692945415508344642090285553594875644) * 10^40
        + 1651966209457482296392385104025600000000))

theorem batchC02702MinusFourthP003ExpBound2558 :
    Real.exp batchC02702MinusFourthP003Exponent2558 ≤ batchC02702MinusFourthP003ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP003Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP003Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP003Input2558 6).1 =
      batchC02702MinusFourthP003Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP003Input2558 6).2 : ℝ) =
      batchC02702MinusFourthP003Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP003Input2558 6).2 =
        ((16577623021621913626370905 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP003Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP003Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02702MinusFourthP003Input2558 =
      (batchC02702MinusFourthP003Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP003Input2558,
        batchC02702MinusFourthP003Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP003Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP003Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP003Center2558))).trans
  norm_num [batchC02702MinusFourthP003Error2558, batchC02702MinusFourthP003ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP003Center2558]

theorem batchC02702MinusFourthP003Bound2558 : batchC02702MinusFourthCell2558 ⟨3, by omega⟩ ≤
    batchC02702MinusFourthP003Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      batchC02702MinusFourthP003Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP003Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP003Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP003ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP003Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP003ExpUpper2558, batchC02702MinusFourthP003Frequency2558,
        batchC02702MinusFourthP003Upper2558]

def batchC02702MinusFourthP004Input2558 : RatPair2542 := ((((-((9704 * 10^40
        + 6862058365114227301196317468995066789844) * 10^40
        + 7715273045015862906397555816256456233479)) : ℚ) /
        ((16761 * 10^40
        + 5297006076896367752151640781800948272505) * 10^40
        + 2022699113227818345341163828019200000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP004Center2558 : RatPair2542 := (((29506665252510868206072986756895 : ℚ)
    /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP004Error2558 : ℝ := ((14818703937456683425662970803 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP004ExpUpper2558 : ℝ := (((12977 * 10^40
        + 1686168119065908265196167626276229032883) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP004Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02702MinusFourthP004Upper2558 : ℝ :=
    ((551725631242345798244149017546071092677 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702MinusFourthP004Exponent2558 : ℝ := (((-((9704 * 10^40
        + 6862058365114227301196317468995066789844) * 10^40
        + 7715273045015862906397555816256456233479)) : ℝ) /
        ((261 * 10^40
        + 8989015719951505746127369387215639816757) * 10^40
        + 8937854673644184661645955684812800000000))

theorem batchC02702MinusFourthP004ExpBound2558 :
    Real.exp batchC02702MinusFourthP004Exponent2558 ≤ batchC02702MinusFourthP004ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP004Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP004Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP004Input2558 6).1 =
      batchC02702MinusFourthP004Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP004Input2558 6).2 : ℝ) =
      batchC02702MinusFourthP004Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP004Input2558 6).2 =
        ((14818703937456683425662970803 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP004Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP004Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02702MinusFourthP004Input2558 =
      (batchC02702MinusFourthP004Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP004Input2558,
        batchC02702MinusFourthP004Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP004Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP004Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP004Center2558))).trans
  norm_num [batchC02702MinusFourthP004Error2558, batchC02702MinusFourthP004ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP004Center2558]

theorem batchC02702MinusFourthP004Bound2558 : batchC02702MinusFourthCell2558 ⟨4, by omega⟩ ≤
    batchC02702MinusFourthP004Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      batchC02702MinusFourthP004Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP004Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP004Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((382988943437901219944308886453878784 : ℝ) /
        811296384146067132209863967375390625) ((127715799921782533419575077567987712 : ℝ) /
        270432128048689044069954655791796875) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP004ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP004Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((382988943437901219944308886453878784 : ℝ) /
        811296384146067132209863967375390625) ((127715799921782533419575077567987712 : ℝ) /
        270432128048689044069954655791796875) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP004ExpUpper2558, batchC02702MinusFourthP004Frequency2558,
        batchC02702MinusFourthP004Upper2558]

def batchC02702MinusFourthP006Input2558 : RatPair2542 := ((((-21029749793246477185003017792617267)
    : ℚ) /
        36814448301243924807922483200000000),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP006Center2558 : RatPair2542 := (((25700852196262263 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP006Error2558 : ℝ := ((8602887250115 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP006ExpUpper2558 : ℝ := ((28258385833542714017018667203 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP006Frequency2558 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02702MinusFourthP006Upper2558 : ℝ := ((12131530767075912361079 : ℝ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984))

noncomputable def batchC02702MinusFourthP006Exponent2558 : ℝ :=
    (((-21029749793246477185003017792617267) : ℝ)
    /
        287612877353468162561894400000000)

theorem batchC02702MinusFourthP006ExpBound2558 :
    Real.exp batchC02702MinusFourthP006Exponent2558 ≤ batchC02702MinusFourthP006ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP006Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP006Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP006Input2558 7).1 =
      batchC02702MinusFourthP006Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP006Input2558 7).2 : ℝ) =
      batchC02702MinusFourthP006Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP006Input2558 7).2 =
        ((8602887250115 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP006Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP006Input2558 hz 7
  rw [hc, he] at h
  have ha : (2 : ℂ)^7 * embedPair2542 batchC02702MinusFourthP006Input2558 =
      (batchC02702MinusFourthP006Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP006Input2558,
        batchC02702MinusFourthP006Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP006Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP006Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP006Center2558))).trans
  norm_num [batchC02702MinusFourthP006Error2558, batchC02702MinusFourthP006ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP006Center2558]

theorem batchC02702MinusFourthP006Bound2558 : batchC02702MinusFourthCell2558 ⟨6, by omega⟩ ≤
    batchC02702MinusFourthP006Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      batchC02702MinusFourthP006Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP006Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP006Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) ((158400514417 : ℝ) /
        204800000000) ((79233025209 : ℝ) /
        102400000000) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP006ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP006Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) ((158400514417 : ℝ) /
        204800000000) ((79233025209 : ℝ) /
        102400000000) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP006ExpUpper2558, batchC02702MinusFourthP006Frequency2558,
        batchC02702MinusFourthP006Upper2558]

def batchC02702MinusFourthP007Input2558 : RatPair2542 := ((((-((561816 * 10^40
        + 8352833621170274469575365073212893660314) * 10^40
        + 5607494071742219355395916822209053668333)) : ℚ) /
        ((831274 * 10^40
        + 5580348506592534057093778275430072041226) * 10^40
        + 5725837405278866969112646657638400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP007Center2558 : RatPair2542 := (((59923141961018019929683668723 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP007Error2558 : ℝ := ((16577623021621913626370905 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02702MinusFourthP007ExpUpper2558 : ℝ := (((13 * 10^40
        + 1772382718022520239532820938692164871001) : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02702MinusFourthP007Frequency2558 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02702MinusFourthP007Upper2558 : ℝ := ((3253382588718985707054756018811957
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02702MinusFourthP007Exponent2558 : ℝ := (((-((561816 * 10^40
        + 8352833621170274469575365073212893660314) * 10^40
        + 5607494071742219355395916822209053668333)) : ℝ) /
        ((12988 * 10^40
        + 6649692945415508344642090285553594875644) * 10^40
        + 1651966209457482296392385104025600000000))

theorem batchC02702MinusFourthP007ExpBound2558 :
    Real.exp batchC02702MinusFourthP007Exponent2558 ≤ batchC02702MinusFourthP007ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP007Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP007Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP007Input2558 6).1 =
      batchC02702MinusFourthP007Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP007Input2558 6).2 : ℝ) =
      batchC02702MinusFourthP007Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP007Input2558 6).2 =
        ((16577623021621913626370905 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP007Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP007Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02702MinusFourthP007Input2558 =
      (batchC02702MinusFourthP007Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP007Input2558,
        batchC02702MinusFourthP007Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP007Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP007Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP007Center2558))).trans
  norm_num [batchC02702MinusFourthP007Error2558, batchC02702MinusFourthP007ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP007Center2558]

theorem batchC02702MinusFourthP007Bound2558 : batchC02702MinusFourthCell2558 ⟨7, by omega⟩ ≤
    batchC02702MinusFourthP007Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      batchC02702MinusFourthP007Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP007Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP007Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP007ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP007Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP007ExpUpper2558, batchC02702MinusFourthP007Frequency2558,
        batchC02702MinusFourthP007Upper2558]

def batchC02702MinusFourthP008Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP008Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP008Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP008ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP008Frequency2558 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def batchC02702MinusFourthP008Upper2558 : ℝ := ((230519614231944883708648147 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702MinusFourthP008Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP008ExpBound2558 :
    Real.exp batchC02702MinusFourthP008Exponent2558 ≤ batchC02702MinusFourthP008ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP008Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP008Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP008Input2558 14).1 =
      batchC02702MinusFourthP008Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP008Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP008Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP008Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP008Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP008Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP008Input2558 =
      (batchC02702MinusFourthP008Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP008Input2558,
        batchC02702MinusFourthP008Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP008Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP008Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP008Center2558))).trans
  norm_num [batchC02702MinusFourthP008Error2558, batchC02702MinusFourthP008ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP008Center2558]

theorem batchC02702MinusFourthP008Bound2558 : batchC02702MinusFourthCell2558 ⟨8, by omega⟩ ≤
    batchC02702MinusFourthP008Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      batchC02702MinusFourthP008Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP008Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP008Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP008ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP008Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP008ExpUpper2558, batchC02702MinusFourthP008Frequency2558,
        batchC02702MinusFourthP008Upper2558]

def batchC02702MinusFourthP009Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP009Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP009Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP009ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP009Frequency2558 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def batchC02702MinusFourthP009Upper2558 : ℝ := ((230521500397028855372170471 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702MinusFourthP009Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP009ExpBound2558 :
    Real.exp batchC02702MinusFourthP009Exponent2558 ≤ batchC02702MinusFourthP009ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP009Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP009Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP009Input2558 14).1 =
      batchC02702MinusFourthP009Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP009Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP009Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP009Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP009Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP009Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP009Input2558 =
      (batchC02702MinusFourthP009Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP009Input2558,
        batchC02702MinusFourthP009Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP009Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP009Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP009Center2558))).trans
  norm_num [batchC02702MinusFourthP009Error2558, batchC02702MinusFourthP009ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP009Center2558]

theorem batchC02702MinusFourthP009Bound2558 : batchC02702MinusFourthCell2558 ⟨9, by omega⟩ ≤
    batchC02702MinusFourthP009Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      batchC02702MinusFourthP009Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP009Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP009Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP009ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP009Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP009ExpUpper2558, batchC02702MinusFourthP009Frequency2558,
        batchC02702MinusFourthP009Upper2558]

def batchC02702MinusFourthP010Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP010Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP010Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP010ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP010Frequency2558 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def batchC02702MinusFourthP010Upper2558 : ℝ := ((115261296491366427178456109 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702MinusFourthP010Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP010ExpBound2558 :
    Real.exp batchC02702MinusFourthP010Exponent2558 ≤ batchC02702MinusFourthP010ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP010Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP010Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP010Input2558 14).1 =
      batchC02702MinusFourthP010Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP010Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP010Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP010Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP010Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP010Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP010Input2558 =
      (batchC02702MinusFourthP010Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP010Input2558,
        batchC02702MinusFourthP010Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP010Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP010Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP010Center2558))).trans
  norm_num [batchC02702MinusFourthP010Error2558, batchC02702MinusFourthP010ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP010Center2558]

theorem batchC02702MinusFourthP010Bound2558 : batchC02702MinusFourthCell2558 ⟨10, by omega⟩ ≤
    batchC02702MinusFourthP010Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      batchC02702MinusFourthP010Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP010Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP010Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP010ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP010Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP010ExpUpper2558, batchC02702MinusFourthP010Frequency2558,
        batchC02702MinusFourthP010Upper2558]

def batchC02702MinusFourthP011Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP011Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP011Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP011ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP011Frequency2558 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def batchC02702MinusFourthP011Upper2558 : ℝ := ((230523321486106722745214547 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702MinusFourthP011Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP011ExpBound2558 :
    Real.exp batchC02702MinusFourthP011Exponent2558 ≤ batchC02702MinusFourthP011ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP011Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP011Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP011Input2558 14).1 =
      batchC02702MinusFourthP011Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP011Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP011Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP011Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP011Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP011Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP011Input2558 =
      (batchC02702MinusFourthP011Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP011Input2558,
        batchC02702MinusFourthP011Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP011Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP011Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP011Center2558))).trans
  norm_num [batchC02702MinusFourthP011Error2558, batchC02702MinusFourthP011ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP011Center2558]

theorem batchC02702MinusFourthP011Bound2558 : batchC02702MinusFourthCell2558 ⟨11, by omega⟩ ≤
    batchC02702MinusFourthP011Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      batchC02702MinusFourthP011Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP011Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP011Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP011ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP011Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP011ExpUpper2558, batchC02702MinusFourthP011Frequency2558,
        batchC02702MinusFourthP011Upper2558]

def batchC02702MinusFourthP012Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP012Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP012Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP012ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP012Frequency2558 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def batchC02702MinusFourthP012Upper2558 : ℝ := ((230524076063391183204327605 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702MinusFourthP012Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP012ExpBound2558 :
    Real.exp batchC02702MinusFourthP012Exponent2558 ≤ batchC02702MinusFourthP012ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP012Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP012Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP012Input2558 14).1 =
      batchC02702MinusFourthP012Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP012Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP012Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP012Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP012Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP012Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP012Input2558 =
      (batchC02702MinusFourthP012Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP012Input2558,
        batchC02702MinusFourthP012Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP012Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP012Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP012Center2558))).trans
  norm_num [batchC02702MinusFourthP012Error2558, batchC02702MinusFourthP012ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP012Center2558]

theorem batchC02702MinusFourthP012Bound2558 : batchC02702MinusFourthCell2558 ⟨12, by omega⟩ ≤
    batchC02702MinusFourthP012Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      batchC02702MinusFourthP012Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP012Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP012Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP012ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP012Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP012ExpUpper2558, batchC02702MinusFourthP012Frequency2558,
        batchC02702MinusFourthP012Upper2558]

def batchC02702MinusFourthP013Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP013Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP013Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP013ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP013Frequency2558 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def batchC02702MinusFourthP013Upper2558 : ℝ := ((230524763716718838376568479 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702MinusFourthP013Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP013ExpBound2558 :
    Real.exp batchC02702MinusFourthP013Exponent2558 ≤ batchC02702MinusFourthP013ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP013Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP013Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP013Input2558 14).1 =
      batchC02702MinusFourthP013Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP013Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP013Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP013Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP013Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP013Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP013Input2558 =
      (batchC02702MinusFourthP013Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP013Input2558,
        batchC02702MinusFourthP013Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP013Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP013Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP013Center2558))).trans
  norm_num [batchC02702MinusFourthP013Error2558, batchC02702MinusFourthP013ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP013Center2558]

theorem batchC02702MinusFourthP013Bound2558 : batchC02702MinusFourthCell2558 ⟨13, by omega⟩ ≤
    batchC02702MinusFourthP013Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      batchC02702MinusFourthP013Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP013Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP013Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP013ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP013Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP013ExpUpper2558, batchC02702MinusFourthP013Frequency2558,
        batchC02702MinusFourthP013Upper2558]

def batchC02702MinusFourthP014Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP014Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP014Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP014ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP014Frequency2558 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def batchC02702MinusFourthP014Upper2558 : ℝ := ((28815754737785892410657553 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC02702MinusFourthP014Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP014ExpBound2558 :
    Real.exp batchC02702MinusFourthP014Exponent2558 ≤ batchC02702MinusFourthP014ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP014Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP014Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP014Input2558 14).1 =
      batchC02702MinusFourthP014Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP014Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP014Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP014Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP014Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP014Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP014Input2558 =
      (batchC02702MinusFourthP014Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP014Input2558,
        batchC02702MinusFourthP014Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP014Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP014Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP014Center2558))).trans
  norm_num [batchC02702MinusFourthP014Error2558, batchC02702MinusFourthP014ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP014Center2558]

theorem batchC02702MinusFourthP014Bound2558 : batchC02702MinusFourthCell2558 ⟨14, by omega⟩ ≤
    batchC02702MinusFourthP014Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      batchC02702MinusFourthP014Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP014Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP014Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP014ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP014Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP014ExpUpper2558, batchC02702MinusFourthP014Frequency2558,
        batchC02702MinusFourthP014Upper2558]

def batchC02702MinusFourthP015Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP015Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP015Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP015ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP015Frequency2558 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def batchC02702MinusFourthP015Upper2558 : ℝ := ((115263475440922554739804001 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702MinusFourthP015Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP015ExpBound2558 :
    Real.exp batchC02702MinusFourthP015Exponent2558 ≤ batchC02702MinusFourthP015ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP015Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP015Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP015Input2558 14).1 =
      batchC02702MinusFourthP015Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP015Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP015Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP015Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP015Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP015Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP015Input2558 =
      (batchC02702MinusFourthP015Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP015Input2558,
        batchC02702MinusFourthP015Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP015Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP015Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP015Center2558))).trans
  norm_num [batchC02702MinusFourthP015Error2558, batchC02702MinusFourthP015ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP015Center2558]

theorem batchC02702MinusFourthP015Bound2558 : batchC02702MinusFourthCell2558 ⟨15, by omega⟩ ≤
    batchC02702MinusFourthP015Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      batchC02702MinusFourthP015Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP015Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP015Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP015ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP015Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP015ExpUpper2558, batchC02702MinusFourthP015Frequency2558,
        batchC02702MinusFourthP015Upper2558]

def batchC02702MinusFourthP016Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP016Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP016Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP016ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP016Frequency2558 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def batchC02702MinusFourthP016Upper2558 : ℝ := ((230527610680978800329024055 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702MinusFourthP016Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP016ExpBound2558 :
    Real.exp batchC02702MinusFourthP016Exponent2558 ≤ batchC02702MinusFourthP016ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP016Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP016Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP016Input2558 14).1 =
      batchC02702MinusFourthP016Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP016Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP016Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP016Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP016Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP016Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP016Input2558 =
      (batchC02702MinusFourthP016Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP016Input2558,
        batchC02702MinusFourthP016Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP016Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP016Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP016Center2558))).trans
  norm_num [batchC02702MinusFourthP016Error2558, batchC02702MinusFourthP016ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP016Center2558]

theorem batchC02702MinusFourthP016Bound2558 : batchC02702MinusFourthCell2558 ⟨16, by omega⟩ ≤
    batchC02702MinusFourthP016Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      batchC02702MinusFourthP016Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP016Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP016Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP016ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP016Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP016ExpUpper2558, batchC02702MinusFourthP016Frequency2558,
        batchC02702MinusFourthP016Upper2558]

def batchC02702MinusFourthP017Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP017Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP017Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP017ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP017Frequency2558 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def batchC02702MinusFourthP017Upper2558 : ℝ := ((230528892316968280645513857 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702MinusFourthP017Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP017ExpBound2558 :
    Real.exp batchC02702MinusFourthP017Exponent2558 ≤ batchC02702MinusFourthP017ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP017Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP017Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP017Input2558 14).1 =
      batchC02702MinusFourthP017Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP017Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP017Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP017Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP017Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP017Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP017Input2558 =
      (batchC02702MinusFourthP017Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP017Input2558,
        batchC02702MinusFourthP017Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP017Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP017Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP017Center2558))).trans
  norm_num [batchC02702MinusFourthP017Error2558, batchC02702MinusFourthP017ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP017Center2558]

theorem batchC02702MinusFourthP017Bound2558 : batchC02702MinusFourthCell2558 ⟨17, by omega⟩ ≤
    batchC02702MinusFourthP017Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      batchC02702MinusFourthP017Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP017Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP017Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP017ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP017Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP017ExpUpper2558, batchC02702MinusFourthP017Frequency2558,
        batchC02702MinusFourthP017Upper2558]

def batchC02702MinusFourthP018Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP018Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP018Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP018ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP018Frequency2558 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def batchC02702MinusFourthP018Upper2558 : ℝ := ((115264688440720219750511661 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702MinusFourthP018Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP018ExpBound2558 :
    Real.exp batchC02702MinusFourthP018Exponent2558 ≤ batchC02702MinusFourthP018ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP018Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP018Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP018Input2558 14).1 =
      batchC02702MinusFourthP018Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP018Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP018Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP018Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP018Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP018Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP018Input2558 =
      (batchC02702MinusFourthP018Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP018Input2558,
        batchC02702MinusFourthP018Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP018Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP018Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP018Center2558))).trans
  norm_num [batchC02702MinusFourthP018Error2558, batchC02702MinusFourthP018ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP018Center2558]

theorem batchC02702MinusFourthP018Bound2558 : batchC02702MinusFourthCell2558 ⟨18, by omega⟩ ≤
    batchC02702MinusFourthP018Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      batchC02702MinusFourthP018Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP018Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP018Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP018ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP018Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP018ExpUpper2558, batchC02702MinusFourthP018Frequency2558,
        batchC02702MinusFourthP018Upper2558]

def batchC02702MinusFourthP019Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP019Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP019Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP019ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP019Frequency2558 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def batchC02702MinusFourthP019Upper2558 : ℝ := ((57632563156891911197349453 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02702MinusFourthP019Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP019ExpBound2558 :
    Real.exp batchC02702MinusFourthP019Exponent2558 ≤ batchC02702MinusFourthP019ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP019Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP019Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP019Input2558 14).1 =
      batchC02702MinusFourthP019Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP019Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP019Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP019Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP019Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP019Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP019Input2558 =
      (batchC02702MinusFourthP019Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP019Input2558,
        batchC02702MinusFourthP019Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP019Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP019Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP019Center2558))).trans
  norm_num [batchC02702MinusFourthP019Error2558, batchC02702MinusFourthP019ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP019Center2558]

theorem batchC02702MinusFourthP019Bound2558 : batchC02702MinusFourthCell2558 ⟨19, by omega⟩ ≤
    batchC02702MinusFourthP019Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      batchC02702MinusFourthP019Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP019Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP019Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP019ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP019Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP019ExpUpper2558, batchC02702MinusFourthP019Frequency2558,
        batchC02702MinusFourthP019Upper2558]

def batchC02702MinusFourthP020Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP020Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP020Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP020ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP020Frequency2558 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def batchC02702MinusFourthP020Upper2558 : ℝ := ((57632801234914228725317759 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02702MinusFourthP020Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP020ExpBound2558 :
    Real.exp batchC02702MinusFourthP020Exponent2558 ≤ batchC02702MinusFourthP020ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP020Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP020Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP020Input2558 14).1 =
      batchC02702MinusFourthP020Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP020Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP020Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP020Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP020Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP020Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP020Input2558 =
      (batchC02702MinusFourthP020Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP020Input2558,
        batchC02702MinusFourthP020Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP020Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP020Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP020Center2558))).trans
  norm_num [batchC02702MinusFourthP020Error2558, batchC02702MinusFourthP020ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP020Center2558]

theorem batchC02702MinusFourthP020Bound2558 : batchC02702MinusFourthCell2558 ⟨20, by omega⟩ ≤
    batchC02702MinusFourthP020Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      batchC02702MinusFourthP020Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP020Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP020Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP020ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP020Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP020ExpUpper2558, batchC02702MinusFourthP020Frequency2558,
        batchC02702MinusFourthP020Upper2558]

def batchC02702MinusFourthP021Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP021Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP021Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP021ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP021Frequency2558 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def batchC02702MinusFourthP021Upper2558 : ℝ := ((230531999687170628724906351 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702MinusFourthP021Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP021ExpBound2558 :
    Real.exp batchC02702MinusFourthP021Exponent2558 ≤ batchC02702MinusFourthP021ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP021Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP021Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP021Input2558 14).1 =
      batchC02702MinusFourthP021Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP021Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP021Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP021Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP021Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP021Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP021Input2558 =
      (batchC02702MinusFourthP021Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP021Input2558,
        batchC02702MinusFourthP021Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP021Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP021Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP021Center2558))).trans
  norm_num [batchC02702MinusFourthP021Error2558, batchC02702MinusFourthP021ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP021Center2558]

theorem batchC02702MinusFourthP021Bound2558 : batchC02702MinusFourthCell2558 ⟨21, by omega⟩ ≤
    batchC02702MinusFourthP021Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      batchC02702MinusFourthP021Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP021Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP021Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP021ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP021Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP021ExpUpper2558, batchC02702MinusFourthP021Frequency2558,
        batchC02702MinusFourthP021Upper2558]

def batchC02702MinusFourthP022Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP022Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP022Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP022ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP022Frequency2558 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def batchC02702MinusFourthP022Upper2558 : ℝ := ((115266203235076305292278543 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702MinusFourthP022Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP022ExpBound2558 :
    Real.exp batchC02702MinusFourthP022Exponent2558 ≤ batchC02702MinusFourthP022ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP022Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP022Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP022Input2558 14).1 =
      batchC02702MinusFourthP022Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP022Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP022Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP022Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP022Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP022Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP022Input2558 =
      (batchC02702MinusFourthP022Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP022Input2558,
        batchC02702MinusFourthP022Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP022Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP022Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP022Center2558))).trans
  norm_num [batchC02702MinusFourthP022Error2558, batchC02702MinusFourthP022ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP022Center2558]

theorem batchC02702MinusFourthP022Bound2558 : batchC02702MinusFourthCell2558 ⟨22, by omega⟩ ≤
    batchC02702MinusFourthP022Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      batchC02702MinusFourthP022Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP022Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP022Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP022ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP022Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP022ExpUpper2558, batchC02702MinusFourthP022Frequency2558,
        batchC02702MinusFourthP022Upper2558]

def batchC02702MinusFourthP023Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP023Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP023Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP023ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP023Frequency2558 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def batchC02702MinusFourthP023Upper2558 : ℝ := ((57633394826928893941978997 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02702MinusFourthP023Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP023ExpBound2558 :
    Real.exp batchC02702MinusFourthP023Exponent2558 ≤ batchC02702MinusFourthP023ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP023Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP023Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP023Input2558 14).1 =
      batchC02702MinusFourthP023Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP023Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP023Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP023Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP023Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP023Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP023Input2558 =
      (batchC02702MinusFourthP023Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP023Input2558,
        batchC02702MinusFourthP023Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP023Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP023Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP023Center2558))).trans
  norm_num [batchC02702MinusFourthP023Error2558, batchC02702MinusFourthP023ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP023Center2558]

theorem batchC02702MinusFourthP023Bound2558 : batchC02702MinusFourthCell2558 ⟨23, by omega⟩ ≤
    batchC02702MinusFourthP023Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      batchC02702MinusFourthP023Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP023Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP023Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP023ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP023Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP023ExpUpper2558, batchC02702MinusFourthP023Frequency2558,
        batchC02702MinusFourthP023Upper2558]

def batchC02702MinusFourthP024Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP024Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP024Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP024ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP024Frequency2558 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def batchC02702MinusFourthP024Upper2558 : ℝ := ((230534118299463269759698121 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702MinusFourthP024Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP024ExpBound2558 :
    Real.exp batchC02702MinusFourthP024Exponent2558 ≤ batchC02702MinusFourthP024ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP024Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP024Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP024Input2558 14).1 =
      batchC02702MinusFourthP024Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP024Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP024Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP024Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP024Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP024Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP024Input2558 =
      (batchC02702MinusFourthP024Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP024Input2558,
        batchC02702MinusFourthP024Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP024Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP024Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP024Center2558))).trans
  norm_num [batchC02702MinusFourthP024Error2558, batchC02702MinusFourthP024ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP024Center2558]

theorem batchC02702MinusFourthP024Bound2558 : batchC02702MinusFourthCell2558 ⟨24, by omega⟩ ≤
    batchC02702MinusFourthP024Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      batchC02702MinusFourthP024Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP024Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP024Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP024ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP024Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP024ExpUpper2558, batchC02702MinusFourthP024Frequency2558,
        batchC02702MinusFourthP024Upper2558]

def batchC02702MinusFourthP025Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP025Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP025Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP025ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP025Frequency2558 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def batchC02702MinusFourthP025Upper2558 : ℝ := ((115267397049396243035567933 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702MinusFourthP025Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP025ExpBound2558 :
    Real.exp batchC02702MinusFourthP025Exponent2558 ≤ batchC02702MinusFourthP025ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP025Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP025Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP025Input2558 14).1 =
      batchC02702MinusFourthP025Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP025Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP025Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP025Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP025Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP025Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP025Input2558 =
      (batchC02702MinusFourthP025Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP025Input2558,
        batchC02702MinusFourthP025Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP025Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP025Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP025Center2558))).trans
  norm_num [batchC02702MinusFourthP025Error2558, batchC02702MinusFourthP025ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP025Center2558]

theorem batchC02702MinusFourthP025Bound2558 : batchC02702MinusFourthCell2558 ⟨25, by omega⟩ ≤
    batchC02702MinusFourthP025Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      batchC02702MinusFourthP025Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP025Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP025Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP025ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP025Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP025ExpUpper2558, batchC02702MinusFourthP025Frequency2558,
        batchC02702MinusFourthP025Upper2558]

def batchC02702MinusFourthP026Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP026Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP026Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP026ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP026Frequency2558 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def batchC02702MinusFourthP026Upper2558 : ℝ := ((230535484741077055216212369 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702MinusFourthP026Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP026ExpBound2558 :
    Real.exp batchC02702MinusFourthP026Exponent2558 ≤ batchC02702MinusFourthP026ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP026Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP026Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP026Input2558 14).1 =
      batchC02702MinusFourthP026Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP026Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP026Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP026Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP026Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP026Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP026Input2558 =
      (batchC02702MinusFourthP026Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP026Input2558,
        batchC02702MinusFourthP026Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP026Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP026Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP026Center2558))).trans
  norm_num [batchC02702MinusFourthP026Error2558, batchC02702MinusFourthP026ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP026Center2558]

theorem batchC02702MinusFourthP026Bound2558 : batchC02702MinusFourthCell2558 ⟨26, by omega⟩ ≤
    batchC02702MinusFourthP026Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      batchC02702MinusFourthP026Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP026Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP026Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP026ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP026Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP026ExpUpper2558, batchC02702MinusFourthP026Frequency2558,
        batchC02702MinusFourthP026Upper2558]

def batchC02702MinusFourthP027Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP027Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP027Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP027ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP027Frequency2558 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def batchC02702MinusFourthP027Upper2558 : ℝ := ((115268240682594395794266497 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02702MinusFourthP027Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP027ExpBound2558 :
    Real.exp batchC02702MinusFourthP027Exponent2558 ≤ batchC02702MinusFourthP027ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP027Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP027Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP027Input2558 14).1 =
      batchC02702MinusFourthP027Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP027Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP027Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP027Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP027Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP027Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP027Input2558 =
      (batchC02702MinusFourthP027Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP027Input2558,
        batchC02702MinusFourthP027Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP027Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP027Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP027Center2558))).trans
  norm_num [batchC02702MinusFourthP027Error2558, batchC02702MinusFourthP027ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP027Center2558]

theorem batchC02702MinusFourthP027Bound2558 : batchC02702MinusFourthCell2558 ⟨27, by omega⟩ ≤
    batchC02702MinusFourthP027Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      batchC02702MinusFourthP027Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP027Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP027Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP027ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP027Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP027ExpUpper2558, batchC02702MinusFourthP027Frequency2558,
        batchC02702MinusFourthP027Upper2558]

def batchC02702MinusFourthP028Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP028Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP028Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP028ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP028Frequency2558 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def batchC02702MinusFourthP028Upper2558 : ℝ := ((230536875943882311015916487 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02702MinusFourthP028Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP028ExpBound2558 :
    Real.exp batchC02702MinusFourthP028Exponent2558 ≤ batchC02702MinusFourthP028ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP028Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP028Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP028Input2558 14).1 =
      batchC02702MinusFourthP028Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP028Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP028Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP028Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP028Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP028Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP028Input2558 =
      (batchC02702MinusFourthP028Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP028Input2558,
        batchC02702MinusFourthP028Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP028Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP028Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP028Center2558))).trans
  norm_num [batchC02702MinusFourthP028Error2558, batchC02702MinusFourthP028ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP028Center2558]

theorem batchC02702MinusFourthP028Bound2558 : batchC02702MinusFourthCell2558 ⟨28, by omega⟩ ≤
    batchC02702MinusFourthP028Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      batchC02702MinusFourthP028Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP028Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP028Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP028ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP028Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP028ExpUpper2558, batchC02702MinusFourthP028Frequency2558,
        batchC02702MinusFourthP028Upper2558]

def batchC02702MinusFourthP029Input2558 : RatPair2542 := ((((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℚ) /
        ((260807 * 10^40
        + 3197730551310164231853277876744249072595) * 10^40
        + 4758300940319480092837544355430400000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusFourthP029Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusFourthP029Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP029ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02702MinusFourthP029Frequency2558 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def batchC02702MinusFourthP029Upper2558 : ℝ := ((28817184583272447241363359 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC02702MinusFourthP029Exponent2558 : ℝ := (((-((192710 * 10^40
        + 237231669970884823148241722950451673790) * 10^40
        + 5711655075549947530657399212345772418333)) : ℝ) /
        ((15 * 10^40
        + 9184155134921344614516104326042281753483) * 10^40
        + 4347824603328876921392385104025600000000))

theorem batchC02702MinusFourthP029ExpBound2558 :
    Real.exp batchC02702MinusFourthP029Exponent2558 ≤ batchC02702MinusFourthP029ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02702MinusFourthP029Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusFourthP029Input2558]
  have hc : (compactExp2547 batchC02702MinusFourthP029Input2558 14).1 =
      batchC02702MinusFourthP029Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02702MinusFourthP029Input2558 14).2 : ℝ) =
      batchC02702MinusFourthP029Error2558 := by
    have hq : (compactExp2547 batchC02702MinusFourthP029Input2558 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02702MinusFourthP029Error2558]
  have h := compactExp_error2547 batchC02702MinusFourthP029Input2558 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02702MinusFourthP029Input2558 =
      (batchC02702MinusFourthP029Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02702MinusFourthP029Input2558,
        batchC02702MinusFourthP029Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02702MinusFourthP029Exponent2558 : ℂ)) (embedPair2542
        batchC02702MinusFourthP029Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02702MinusFourthP029Center2558))).trans
  norm_num [batchC02702MinusFourthP029Error2558, batchC02702MinusFourthP029ExpUpper2558,
      pairMagnitude2542,
      batchC02702MinusFourthP029Center2558]

theorem batchC02702MinusFourthP029Bound2558 : batchC02702MinusFourthCell2558 ⟨29, by omega⟩ ≤
    batchC02702MinusFourthP029Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      batchC02702MinusFourthP029Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02702MinusFourthP029Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02702MinusFourthP029Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02702MinusFourthP029ExpBound2558 using 1; norm_num
        [batchC02702MinusFourthP029Exponent2558])
  have hid : batchC02702MinusFourthCell2558 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) (((-79233025209) : ℝ) /
        25600000000) (((-158400514417) : ℝ) /
        51200000000) := by
    norm_num [batchC02702MinusFourthCell2558, cellNearAbs2538, batchN02702MinusPosition2558,
      batchN02703MinusPosition2558, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02702MinusFourthP029ExpUpper2558, batchC02702MinusFourthP029Frequency2558,
        batchC02702MinusFourthP029Upper2558]

noncomputable def batchC02702MinusFourthP000Upper2558 : ℝ := 0

theorem batchC02702MinusFourthP000Bound2558 :
    batchC02702MinusFourthCell2558 ⟨0, by omega⟩ ≤ batchC02702MinusFourthP000Upper2558 := by
  norm_num [batchC02702MinusFourthCell2558, batchC02702MinusFourthP000Upper2558, cellNearAbs2538,
    batchN02702MinusPosition2558, batchN02703MinusPosition2558, storedWidth]

noncomputable def batchC02702MinusFourthP005Upper2558 : ℝ := 0

theorem batchC02702MinusFourthP005Bound2558 :
    batchC02702MinusFourthCell2558 ⟨5, by omega⟩ ≤ batchC02702MinusFourthP005Upper2558 := by
  norm_num [batchC02702MinusFourthCell2558, batchC02702MinusFourthP005Upper2558, cellNearAbs2538,
    batchN02702MinusPosition2558, batchN02703MinusPosition2558, storedWidth]

noncomputable def batchC02702MinusFourthUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02702MinusFourthP000Upper2558
  | 1 => batchC02702MinusFourthP001Upper2558
  | 2 => batchC02702MinusFourthP002Upper2558
  | 3 => batchC02702MinusFourthP003Upper2558
  | 4 => batchC02702MinusFourthP004Upper2558
  | 5 => batchC02702MinusFourthP005Upper2558
  | 6 => batchC02702MinusFourthP006Upper2558
  | 7 => batchC02702MinusFourthP007Upper2558
  | 8 => batchC02702MinusFourthP008Upper2558
  | 9 => batchC02702MinusFourthP009Upper2558
  | 10 => batchC02702MinusFourthP010Upper2558
  | 11 => batchC02702MinusFourthP011Upper2558
  | 12 => batchC02702MinusFourthP012Upper2558
  | 13 => batchC02702MinusFourthP013Upper2558
  | 14 => batchC02702MinusFourthP014Upper2558
  | 15 => batchC02702MinusFourthP015Upper2558
  | 16 => batchC02702MinusFourthP016Upper2558
  | 17 => batchC02702MinusFourthP017Upper2558
  | 18 => batchC02702MinusFourthP018Upper2558
  | 19 => batchC02702MinusFourthP019Upper2558
  | 20 => batchC02702MinusFourthP020Upper2558
  | 21 => batchC02702MinusFourthP021Upper2558
  | 22 => batchC02702MinusFourthP022Upper2558
  | 23 => batchC02702MinusFourthP023Upper2558
  | 24 => batchC02702MinusFourthP024Upper2558
  | 25 => batchC02702MinusFourthP025Upper2558
  | 26 => batchC02702MinusFourthP026Upper2558
  | 27 => batchC02702MinusFourthP027Upper2558
  | 28 => batchC02702MinusFourthP028Upper2558
  | 29 => batchC02702MinusFourthP029Upper2558
  | _ => 0

theorem batchC02702MinusFourthBound2558 (i : Fin 30) :
    batchC02702MinusFourthCell2558 i ≤ batchC02702MinusFourthUpper2558 i := by
  fin_cases i
  · exact batchC02702MinusFourthP000Bound2558
  · exact batchC02702MinusFourthP001Bound2558
  · exact batchC02702MinusFourthP002Bound2558
  · exact batchC02702MinusFourthP003Bound2558
  · exact batchC02702MinusFourthP004Bound2558
  · exact batchC02702MinusFourthP005Bound2558
  · exact batchC02702MinusFourthP006Bound2558
  · exact batchC02702MinusFourthP007Bound2558
  · exact batchC02702MinusFourthP008Bound2558
  · exact batchC02702MinusFourthP009Bound2558
  · exact batchC02702MinusFourthP010Bound2558
  · exact batchC02702MinusFourthP011Bound2558
  · exact batchC02702MinusFourthP012Bound2558
  · exact batchC02702MinusFourthP013Bound2558
  · exact batchC02702MinusFourthP014Bound2558
  · exact batchC02702MinusFourthP015Bound2558
  · exact batchC02702MinusFourthP016Bound2558
  · exact batchC02702MinusFourthP017Bound2558
  · exact batchC02702MinusFourthP018Bound2558
  · exact batchC02702MinusFourthP019Bound2558
  · exact batchC02702MinusFourthP020Bound2558
  · exact batchC02702MinusFourthP021Bound2558
  · exact batchC02702MinusFourthP022Bound2558
  · exact batchC02702MinusFourthP023Bound2558
  · exact batchC02702MinusFourthP024Bound2558
  · exact batchC02702MinusFourthP025Bound2558
  · exact batchC02702MinusFourthP026Bound2558
  · exact batchC02702MinusFourthP027Bound2558
  · exact batchC02702MinusFourthP028Bound2558
  · exact batchC02702MinusFourthP029Bound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP001Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP002Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP003Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP004Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP006Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP007Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP008Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP009Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP010Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP011Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP012Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP013Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP014Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP015Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP016Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP017Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP018Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP019Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP020Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP021Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP022Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP023Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP024Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP025Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP026Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP027Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP028Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP029Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP000Bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusFourthP005Bound2558
