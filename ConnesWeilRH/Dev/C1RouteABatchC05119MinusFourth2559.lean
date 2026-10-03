import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteABatchN05119Minus2559
import ConnesWeilRH.Dev.C1RouteABatchN05120Minus2559

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC05119MinusFourthCell2559 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 batchN05119MinusPosition2559 batchN05120MinusPosition2559 < storedWidth i ^ 2
      then
    weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 batchN05119MinusPosition2559 batchN05120MinusPosition2559 / (storedWidth i
          ^ 2))
      (min (max |batchN05119MinusPosition2559| |batchN05120MinusPosition2559|) (storedWidth i ^ 2)
          /
        (storedWidth i ^ 2)) batchN05119MinusPosition2559 batchN05120MinusPosition2559
  else 0


def batchC05119MinusFourthP000Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP000Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP000Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP000ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP000Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05119MinusFourthP000Upper2559 : ℝ := (((33 * 10^40
        + 6986667562287158807786285610076744399539) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119MinusFourthP000Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP000ExpBound2559 :
    Real.exp batchC05119MinusFourthP000Exponent2559 ≤ batchC05119MinusFourthP000ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP000Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP000Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP000Input2559 5).1 =
      batchC05119MinusFourthP000Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP000Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP000Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP000Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP000Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP000Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP000Input2559 =
      (batchC05119MinusFourthP000Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP000Input2559,
        batchC05119MinusFourthP000Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP000Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP000Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP000Center2559))).trans
  norm_num [batchC05119MinusFourthP000Error2559, batchC05119MinusFourthP000ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP000Center2559]

theorem batchC05119MinusFourthP000Bound2559 : batchC05119MinusFourthCell2559 ⟨0, by omega⟩ ≤
    batchC05119MinusFourthP000Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨0, by omega⟩)‖ ≤
      batchC05119MinusFourthP000Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP000Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP000Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    ((12980742146337070512478121581609 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5070602400912918168936766242816015625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP000ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP000Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨0, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
        ((12980742146337070512478121581609 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5070602400912918168936766242816015625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP000ExpUpper2559, batchC05119MinusFourthP000Frequency2559,
        batchC05119MinusFourthP000Upper2559]

def batchC05119MinusFourthP001Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP001Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP001Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP001ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP001Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05119MinusFourthP001Upper2559 : ℝ := (((33 * 10^40
        + 1833474729917330533191289284912655034549) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119MinusFourthP001Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP001ExpBound2559 :
    Real.exp batchC05119MinusFourthP001Exponent2559 ≤ batchC05119MinusFourthP001ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP001Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP001Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP001Input2559 5).1 =
      batchC05119MinusFourthP001Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP001Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP001Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP001Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP001Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP001Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP001Input2559 =
      (batchC05119MinusFourthP001Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP001Input2559,
        batchC05119MinusFourthP001Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP001Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP001Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP001Center2559))).trans
  norm_num [batchC05119MinusFourthP001Error2559, batchC05119MinusFourthP001ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP001Center2559]

theorem batchC05119MinusFourthP001Bound2559 : batchC05119MinusFourthCell2559 ⟨1, by omega⟩ ≤
    batchC05119MinusFourthP001Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      batchC05119MinusFourthP001Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP001Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP001Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) (0 : ℝ) ((39614081861595078604086562521088 : ℝ) /
        104779244925114570282650713456640625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP001ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP001Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) (0 : ℝ) ((39614081861595078604086562521088 : ℝ) /
        104779244925114570282650713456640625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP001ExpUpper2559, batchC05119MinusFourthP001Frequency2559,
        batchC05119MinusFourthP001Upper2559]

def batchC05119MinusFourthP002Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP002Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP002Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP002ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP002Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05119MinusFourthP002Upper2559 : ℝ := (((4 * 10^40
        + 1146523020945426661499737898776266695759) : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC05119MinusFourthP002Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP002ExpBound2559 :
    Real.exp batchC05119MinusFourthP002Exponent2559 ≤ batchC05119MinusFourthP002ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP002Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP002Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP002Input2559 5).1 =
      batchC05119MinusFourthP002Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP002Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP002Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP002Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP002Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP002Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP002Input2559 =
      (batchC05119MinusFourthP002Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP002Input2559,
        batchC05119MinusFourthP002Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP002Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP002Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP002Center2559))).trans
  norm_num [batchC05119MinusFourthP002Error2559, batchC05119MinusFourthP002ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP002Center2559]

theorem batchC05119MinusFourthP002Bound2559 : batchC05119MinusFourthCell2559 ⟨2, by omega⟩ ≤
    batchC05119MinusFourthP002Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      batchC05119MinusFourthP002Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP002Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP002Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        535582378596426958724104076656640625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP002ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP002Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        535582378596426958724104076656640625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP002ExpUpper2559, batchC05119MinusFourthP002Frequency2559,
        batchC05119MinusFourthP002Upper2559]

def batchC05119MinusFourthP003Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP003Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP003Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP003ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP003Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05119MinusFourthP003Upper2559 : ℝ := (((8 * 10^40
        + 1921483116806704097682079725814672354279) : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC05119MinusFourthP003Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP003ExpBound2559 :
    Real.exp batchC05119MinusFourthP003Exponent2559 ≤ batchC05119MinusFourthP003ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP003Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP003Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP003Input2559 5).1 =
      batchC05119MinusFourthP003Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP003Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP003Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP003Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP003Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP003Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP003Input2559 =
      (batchC05119MinusFourthP003Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP003Input2559,
        batchC05119MinusFourthP003Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP003Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP003Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP003Center2559))).trans
  norm_num [batchC05119MinusFourthP003Error2559, batchC05119MinusFourthP003ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP003Center2559]

theorem batchC05119MinusFourthP003Bound2559 : batchC05119MinusFourthCell2559 ⟨3, by omega⟩ ≤
    batchC05119MinusFourthP003Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      batchC05119MinusFourthP003Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP003Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP003Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP003ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP003Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP003ExpUpper2559, batchC05119MinusFourthP003Frequency2559,
        batchC05119MinusFourthP003Upper2559]

def batchC05119MinusFourthP004Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP004Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP004Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP004ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP004Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05119MinusFourthP004Upper2559 : ℝ :=
    ((319143869165444825792235041685295711561 : ℝ) /
        (142724 * 10^40
        + 7692705959881058285969449495136382746624))

noncomputable def batchC05119MinusFourthP004Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP004ExpBound2559 :
    Real.exp batchC05119MinusFourthP004Exponent2559 ≤ batchC05119MinusFourthP004ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP004Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP004Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP004Input2559 5).1 =
      batchC05119MinusFourthP004Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP004Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP004Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP004Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP004Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP004Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP004Input2559 =
      (batchC05119MinusFourthP004Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP004Input2559,
        batchC05119MinusFourthP004Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP004Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP004Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP004Center2559))).trans
  norm_num [batchC05119MinusFourthP004Error2559, batchC05119MinusFourthP004ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP004Center2559]

theorem batchC05119MinusFourthP004Bound2559 : batchC05119MinusFourthCell2559 ⟨4, by omega⟩ ≤
    batchC05119MinusFourthP004Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      batchC05119MinusFourthP004Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP004Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP004Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        811296384146067132209863967375390625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP004ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP004Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        811296384146067132209863967375390625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP004ExpUpper2559, batchC05119MinusFourthP004Frequency2559,
        batchC05119MinusFourthP004Upper2559]

def batchC05119MinusFourthP005Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP005Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP005Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP005ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP005Frequency2559 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC05119MinusFourthP005Upper2559 : ℝ :=
    ((11674988018847392277171221784072946191 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119MinusFourthP005Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP005ExpBound2559 :
    Real.exp batchC05119MinusFourthP005Exponent2559 ≤ batchC05119MinusFourthP005ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP005Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP005Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP005Input2559 5).1 =
      batchC05119MinusFourthP005Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP005Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP005Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP005Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP005Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP005Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP005Input2559 =
      (batchC05119MinusFourthP005Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP005Input2559,
        batchC05119MinusFourthP005Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP005Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP005Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP005Center2559))).trans
  norm_num [batchC05119MinusFourthP005Error2559, batchC05119MinusFourthP005ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP005Center2559]

theorem batchC05119MinusFourthP005Bound2559 : batchC05119MinusFourthCell2559 ⟨5, by omega⟩ ≤
    batchC05119MinusFourthP005Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨5, by omega⟩)‖ ≤
      batchC05119MinusFourthP005Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP005Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP005Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    ((14311268216336621374914235141089 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5590339147006492724575873101987890625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP005ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP005Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨5, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
        ((14311268216336621374914235141089 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5590339147006492724575873101987890625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP005ExpUpper2559, batchC05119MinusFourthP005Frequency2559,
        batchC05119MinusFourthP005Upper2559]

def batchC05119MinusFourthP006Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP006Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP006Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP006ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP006Frequency2559 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC05119MinusFourthP006Upper2559 : ℝ :=
    ((1545240379027766584475271547307092303 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC05119MinusFourthP006Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP006ExpBound2559 :
    Real.exp batchC05119MinusFourthP006Exponent2559 ≤ batchC05119MinusFourthP006ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP006Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP006Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP006Input2559 5).1 =
      batchC05119MinusFourthP006Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP006Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP006Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP006Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP006Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP006Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP006Input2559 =
      (batchC05119MinusFourthP006Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP006Input2559,
        batchC05119MinusFourthP006Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP006Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP006Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP006Center2559))).trans
  norm_num [batchC05119MinusFourthP006Error2559, batchC05119MinusFourthP006ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP006Center2559]

theorem batchC05119MinusFourthP006Bound2559 : batchC05119MinusFourthCell2559 ⟨6, by omega⟩ ≤
    batchC05119MinusFourthP006Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      batchC05119MinusFourthP006Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP006Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP006Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) (0 : ℝ) ((65536001 : ℝ) /
        204800000000) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP006ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP006Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) (0 : ℝ) ((65536001 : ℝ) /
        204800000000) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP006ExpUpper2559, batchC05119MinusFourthP006Frequency2559,
        batchC05119MinusFourthP006Upper2559]

def batchC05119MinusFourthP007Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP007Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP007Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP007ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP007Frequency2559 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC05119MinusFourthP007Upper2559 : ℝ := ((65053358101589633320478942525855053
    : ℝ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968))

noncomputable def batchC05119MinusFourthP007Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP007ExpBound2559 :
    Real.exp batchC05119MinusFourthP007Exponent2559 ≤ batchC05119MinusFourthP007ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP007Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP007Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP007Input2559 5).1 =
      batchC05119MinusFourthP007Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP007Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP007Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP007Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP007Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP007Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP007Input2559 =
      (batchC05119MinusFourthP007Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP007Input2559,
        batchC05119MinusFourthP007Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP007Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP007Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP007Center2559))).trans
  norm_num [batchC05119MinusFourthP007Error2559, batchC05119MinusFourthP007ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP007Center2559]

theorem batchC05119MinusFourthP007Bound2559 : batchC05119MinusFourthCell2559 ⟨7, by omega⟩ ≤
    batchC05119MinusFourthP007Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      batchC05119MinusFourthP007Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP007Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP007Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP007ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP007Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP007ExpUpper2559, batchC05119MinusFourthP007Frequency2559,
        batchC05119MinusFourthP007Upper2559]

def batchC05119MinusFourthP008Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP008Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP008Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP008ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP008Frequency2559 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def batchC05119MinusFourthP008Upper2559 : ℝ :=
    ((1632940905703249210481260534584507374399 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC05119MinusFourthP008Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP008ExpBound2559 :
    Real.exp batchC05119MinusFourthP008Exponent2559 ≤ batchC05119MinusFourthP008ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP008Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP008Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP008Input2559 5).1 =
      batchC05119MinusFourthP008Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP008Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP008Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP008Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP008Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP008Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP008Input2559 =
      (batchC05119MinusFourthP008Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP008Input2559,
        batchC05119MinusFourthP008Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP008Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP008Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP008Center2559))).trans
  norm_num [batchC05119MinusFourthP008Error2559, batchC05119MinusFourthP008ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP008Center2559]

theorem batchC05119MinusFourthP008Bound2559 : batchC05119MinusFourthCell2559 ⟨8, by omega⟩ ≤
    batchC05119MinusFourthP008Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      batchC05119MinusFourthP008Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP008Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP008Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP008ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP008Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP008ExpUpper2559, batchC05119MinusFourthP008Frequency2559,
        batchC05119MinusFourthP008Upper2559]

def batchC05119MinusFourthP009Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP009Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP009Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP009ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP009Frequency2559 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def batchC05119MinusFourthP009Upper2559 : ℝ := (((1 * 10^40
        + 4542223335602797445439734824814323504963) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119MinusFourthP009Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP009ExpBound2559 :
    Real.exp batchC05119MinusFourthP009Exponent2559 ≤ batchC05119MinusFourthP009ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP009Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP009Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP009Input2559 5).1 =
      batchC05119MinusFourthP009Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP009Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP009Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP009Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP009Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP009Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP009Input2559 =
      (batchC05119MinusFourthP009Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP009Input2559,
        batchC05119MinusFourthP009Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP009Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP009Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP009Center2559))).trans
  norm_num [batchC05119MinusFourthP009Error2559, batchC05119MinusFourthP009ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP009Center2559]

theorem batchC05119MinusFourthP009Bound2559 : batchC05119MinusFourthCell2559 ⟨9, by omega⟩ ≤
    batchC05119MinusFourthP009Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      batchC05119MinusFourthP009Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP009Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP009Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP009ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP009Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP009ExpUpper2559, batchC05119MinusFourthP009Frequency2559,
        batchC05119MinusFourthP009Upper2559]

def batchC05119MinusFourthP010Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP010Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP010Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP010ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP010Frequency2559 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def batchC05119MinusFourthP010Upper2559 : ℝ := (((2 * 10^40
        + 8445577044430899163613284817764845464241) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119MinusFourthP010Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP010ExpBound2559 :
    Real.exp batchC05119MinusFourthP010Exponent2559 ≤ batchC05119MinusFourthP010ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP010Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP010Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP010Input2559 5).1 =
      batchC05119MinusFourthP010Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP010Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP010Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP010Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP010Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP010Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP010Input2559 =
      (batchC05119MinusFourthP010Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP010Input2559,
        batchC05119MinusFourthP010Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP010Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP010Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP010Center2559))).trans
  norm_num [batchC05119MinusFourthP010Error2559, batchC05119MinusFourthP010ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP010Center2559]

theorem batchC05119MinusFourthP010Bound2559 : batchC05119MinusFourthCell2559 ⟨10, by omega⟩ ≤
    batchC05119MinusFourthP010Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      batchC05119MinusFourthP010Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP010Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP010Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP010ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP010Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP010ExpUpper2559, batchC05119MinusFourthP010Frequency2559,
        batchC05119MinusFourthP010Upper2559]

def batchC05119MinusFourthP011Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP011Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP011Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP011ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP011Frequency2559 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def batchC05119MinusFourthP011Upper2559 : ℝ := (((8 * 10^40
        + 4318014266247539741551097150765614777993) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119MinusFourthP011Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP011ExpBound2559 :
    Real.exp batchC05119MinusFourthP011Exponent2559 ≤ batchC05119MinusFourthP011ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP011Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP011Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP011Input2559 5).1 =
      batchC05119MinusFourthP011Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP011Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP011Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP011Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP011Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP011Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP011Input2559 =
      (batchC05119MinusFourthP011Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP011Input2559,
        batchC05119MinusFourthP011Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP011Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP011Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP011Center2559))).trans
  norm_num [batchC05119MinusFourthP011Error2559, batchC05119MinusFourthP011ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP011Center2559]

theorem batchC05119MinusFourthP011Bound2559 : batchC05119MinusFourthCell2559 ⟨11, by omega⟩ ≤
    batchC05119MinusFourthP011Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      batchC05119MinusFourthP011Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP011Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP011Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP011ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP011Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP011ExpUpper2559, batchC05119MinusFourthP011Frequency2559,
        batchC05119MinusFourthP011Upper2559]

def batchC05119MinusFourthP012Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP012Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP012Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP012ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP012Frequency2559 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def batchC05119MinusFourthP012Upper2559 : ℝ := (((1 * 10^40
        + 5277560075846031619885527329175232759707) : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC05119MinusFourthP012Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP012ExpBound2559 :
    Real.exp batchC05119MinusFourthP012Exponent2559 ≤ batchC05119MinusFourthP012ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP012Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP012Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP012Input2559 5).1 =
      batchC05119MinusFourthP012Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP012Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP012Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP012Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP012Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP012Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP012Input2559 =
      (batchC05119MinusFourthP012Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP012Input2559,
        batchC05119MinusFourthP012Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP012Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP012Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP012Center2559))).trans
  norm_num [batchC05119MinusFourthP012Error2559, batchC05119MinusFourthP012ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP012Center2559]

theorem batchC05119MinusFourthP012Bound2559 : batchC05119MinusFourthCell2559 ⟨12, by omega⟩ ≤
    batchC05119MinusFourthP012Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      batchC05119MinusFourthP012Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP012Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP012Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP012ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP012Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP012ExpUpper2559, batchC05119MinusFourthP012Frequency2559,
        batchC05119MinusFourthP012Upper2559]

def batchC05119MinusFourthP013Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP013Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP013Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP013ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP013Frequency2559 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def batchC05119MinusFourthP013Upper2559 : ℝ := (((16 * 10^40
        + 6837949523115563859000360871046890931297) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119MinusFourthP013Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP013ExpBound2559 :
    Real.exp batchC05119MinusFourthP013Exponent2559 ≤ batchC05119MinusFourthP013ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP013Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP013Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP013Input2559 5).1 =
      batchC05119MinusFourthP013Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP013Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP013Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP013Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP013Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP013Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP013Input2559 =
      (batchC05119MinusFourthP013Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP013Input2559,
        batchC05119MinusFourthP013Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP013Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP013Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP013Center2559))).trans
  norm_num [batchC05119MinusFourthP013Error2559, batchC05119MinusFourthP013ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP013Center2559]

theorem batchC05119MinusFourthP013Bound2559 : batchC05119MinusFourthCell2559 ⟨13, by omega⟩ ≤
    batchC05119MinusFourthP013Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      batchC05119MinusFourthP013Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP013Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP013Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP013ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP013Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP013ExpUpper2559, batchC05119MinusFourthP013Frequency2559,
        batchC05119MinusFourthP013Upper2559]

def batchC05119MinusFourthP014Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP014Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP014Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP014ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP014Frequency2559 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def batchC05119MinusFourthP014Upper2559 : ℝ := (((14 * 10^40
        + 361698572858198437249921517049598220201) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119MinusFourthP014Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP014ExpBound2559 :
    Real.exp batchC05119MinusFourthP014Exponent2559 ≤ batchC05119MinusFourthP014ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP014Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP014Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP014Input2559 5).1 =
      batchC05119MinusFourthP014Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP014Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP014Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP014Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP014Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP014Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP014Input2559 =
      (batchC05119MinusFourthP014Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP014Input2559,
        batchC05119MinusFourthP014Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP014Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP014Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP014Center2559))).trans
  norm_num [batchC05119MinusFourthP014Error2559, batchC05119MinusFourthP014ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP014Center2559]

theorem batchC05119MinusFourthP014Bound2559 : batchC05119MinusFourthCell2559 ⟨14, by omega⟩ ≤
    batchC05119MinusFourthP014Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      batchC05119MinusFourthP014Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP014Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP014Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP014ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP014Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP014ExpUpper2559, batchC05119MinusFourthP014Frequency2559,
        batchC05119MinusFourthP014Upper2559]

def batchC05119MinusFourthP015Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP015Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP015Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP015ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP015Frequency2559 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def batchC05119MinusFourthP015Upper2559 : ℝ := (((39 * 10^40
        + 2677361324008412817987528877049788573141) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119MinusFourthP015Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP015ExpBound2559 :
    Real.exp batchC05119MinusFourthP015Exponent2559 ≤ batchC05119MinusFourthP015ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP015Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP015Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP015Input2559 5).1 =
      batchC05119MinusFourthP015Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP015Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP015Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP015Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP015Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP015Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP015Input2559 =
      (batchC05119MinusFourthP015Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP015Input2559,
        batchC05119MinusFourthP015Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP015Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP015Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP015Center2559))).trans
  norm_num [batchC05119MinusFourthP015Error2559, batchC05119MinusFourthP015ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP015Center2559]

theorem batchC05119MinusFourthP015Bound2559 : batchC05119MinusFourthCell2559 ⟨15, by omega⟩ ≤
    batchC05119MinusFourthP015Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      batchC05119MinusFourthP015Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP015Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP015Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP015ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP015Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP015ExpUpper2559, batchC05119MinusFourthP015Frequency2559,
        batchC05119MinusFourthP015Upper2559]

def batchC05119MinusFourthP016Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP016Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP016Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP016ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP016Frequency2559 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def batchC05119MinusFourthP016Upper2559 : ℝ := (((24 * 10^40
        + 6201010231334217657786310680889075551089) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119MinusFourthP016Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP016ExpBound2559 :
    Real.exp batchC05119MinusFourthP016Exponent2559 ≤ batchC05119MinusFourthP016ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP016Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP016Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP016Input2559 5).1 =
      batchC05119MinusFourthP016Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP016Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP016Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP016Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP016Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP016Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP016Input2559 =
      (batchC05119MinusFourthP016Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP016Input2559,
        batchC05119MinusFourthP016Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP016Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP016Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP016Center2559))).trans
  norm_num [batchC05119MinusFourthP016Error2559, batchC05119MinusFourthP016ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP016Center2559]

theorem batchC05119MinusFourthP016Bound2559 : batchC05119MinusFourthCell2559 ⟨16, by omega⟩ ≤
    batchC05119MinusFourthP016Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      batchC05119MinusFourthP016Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP016Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP016Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP016ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP016Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP016ExpUpper2559, batchC05119MinusFourthP016Frequency2559,
        batchC05119MinusFourthP016Upper2559]

def batchC05119MinusFourthP017Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP017Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP017Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP017ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP017Frequency2559 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def batchC05119MinusFourthP017Upper2559 : ℝ := (((73 * 10^40
        + 9260124292652928899991279722425775921803) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119MinusFourthP017Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP017ExpBound2559 :
    Real.exp batchC05119MinusFourthP017Exponent2559 ≤ batchC05119MinusFourthP017ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP017Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP017Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP017Input2559 5).1 =
      batchC05119MinusFourthP017Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP017Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP017Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP017Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP017Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP017Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP017Input2559 =
      (batchC05119MinusFourthP017Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP017Input2559,
        batchC05119MinusFourthP017Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP017Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP017Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP017Center2559))).trans
  norm_num [batchC05119MinusFourthP017Error2559, batchC05119MinusFourthP017ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP017Center2559]

theorem batchC05119MinusFourthP017Bound2559 : batchC05119MinusFourthCell2559 ⟨17, by omega⟩ ≤
    batchC05119MinusFourthP017Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      batchC05119MinusFourthP017Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP017Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP017Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP017ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP017Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP017ExpUpper2559, batchC05119MinusFourthP017Frequency2559,
        batchC05119MinusFourthP017Upper2559]

def batchC05119MinusFourthP018Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP018Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP018Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP018ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP018Frequency2559 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def batchC05119MinusFourthP018Upper2559 : ℝ :=
    ((6667095131675882463601446325266484992903 : ℝ) /
        (1141798 * 10^40
        + 1541647679048466287755595961091061972992))

noncomputable def batchC05119MinusFourthP018Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP018ExpBound2559 :
    Real.exp batchC05119MinusFourthP018Exponent2559 ≤ batchC05119MinusFourthP018ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP018Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP018Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP018Input2559 5).1 =
      batchC05119MinusFourthP018Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP018Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP018Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP018Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP018Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP018Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP018Input2559 =
      (batchC05119MinusFourthP018Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP018Input2559,
        batchC05119MinusFourthP018Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP018Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP018Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP018Center2559))).trans
  norm_num [batchC05119MinusFourthP018Error2559, batchC05119MinusFourthP018ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP018Center2559]

theorem batchC05119MinusFourthP018Bound2559 : batchC05119MinusFourthCell2559 ⟨18, by omega⟩ ≤
    batchC05119MinusFourthP018Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      batchC05119MinusFourthP018Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP018Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP018Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP018ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP018Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP018ExpUpper2559, batchC05119MinusFourthP018Frequency2559,
        batchC05119MinusFourthP018Upper2559]

def batchC05119MinusFourthP019Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP019Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP019Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP019ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP019Frequency2559 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def batchC05119MinusFourthP019Upper2559 : ℝ := (((109 * 10^40
        + 2661023715143872465616857530169628556751) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119MinusFourthP019Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP019ExpBound2559 :
    Real.exp batchC05119MinusFourthP019Exponent2559 ≤ batchC05119MinusFourthP019ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP019Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP019Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP019Input2559 5).1 =
      batchC05119MinusFourthP019Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP019Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP019Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP019Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP019Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP019Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP019Input2559 =
      (batchC05119MinusFourthP019Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP019Input2559,
        batchC05119MinusFourthP019Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP019Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP019Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP019Center2559))).trans
  norm_num [batchC05119MinusFourthP019Error2559, batchC05119MinusFourthP019ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP019Center2559]

theorem batchC05119MinusFourthP019Bound2559 : batchC05119MinusFourthCell2559 ⟨19, by omega⟩ ≤
    batchC05119MinusFourthP019Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      batchC05119MinusFourthP019Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP019Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP019Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP019ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP019Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP019ExpUpper2559, batchC05119MinusFourthP019Frequency2559,
        batchC05119MinusFourthP019Upper2559]

def batchC05119MinusFourthP020Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP020Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP020Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP020ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP020Frequency2559 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def batchC05119MinusFourthP020Upper2559 : ℝ := (((140 * 10^40
        + 6644802555729554046236806182008087307495) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119MinusFourthP020Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP020ExpBound2559 :
    Real.exp batchC05119MinusFourthP020Exponent2559 ≤ batchC05119MinusFourthP020ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP020Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP020Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP020Input2559 5).1 =
      batchC05119MinusFourthP020Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP020Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP020Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP020Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP020Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP020Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP020Input2559 =
      (batchC05119MinusFourthP020Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP020Input2559,
        batchC05119MinusFourthP020Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP020Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP020Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP020Center2559))).trans
  norm_num [batchC05119MinusFourthP020Error2559, batchC05119MinusFourthP020ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP020Center2559]

theorem batchC05119MinusFourthP020Bound2559 : batchC05119MinusFourthCell2559 ⟨20, by omega⟩ ≤
    batchC05119MinusFourthP020Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      batchC05119MinusFourthP020Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP020Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP020Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP020ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP020Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP020ExpUpper2559, batchC05119MinusFourthP020Frequency2559,
        batchC05119MinusFourthP020Upper2559]

def batchC05119MinusFourthP021Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP021Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP021Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP021ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP021Frequency2559 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def batchC05119MinusFourthP021Upper2559 : ℝ := (((171 * 10^40
        + 6876705691398468410181972270403907439335) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119MinusFourthP021Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP021ExpBound2559 :
    Real.exp batchC05119MinusFourthP021Exponent2559 ≤ batchC05119MinusFourthP021ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP021Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP021Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP021Input2559 5).1 =
      batchC05119MinusFourthP021Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP021Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP021Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP021Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP021Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP021Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP021Input2559 =
      (batchC05119MinusFourthP021Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP021Input2559,
        batchC05119MinusFourthP021Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP021Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP021Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP021Center2559))).trans
  norm_num [batchC05119MinusFourthP021Error2559, batchC05119MinusFourthP021ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP021Center2559]

theorem batchC05119MinusFourthP021Bound2559 : batchC05119MinusFourthCell2559 ⟨21, by omega⟩ ≤
    batchC05119MinusFourthP021Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      batchC05119MinusFourthP021Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP021Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP021Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP021ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP021Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP021ExpUpper2559, batchC05119MinusFourthP021Frequency2559,
        batchC05119MinusFourthP021Upper2559]

def batchC05119MinusFourthP022Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP022Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP022Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP022ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP022Frequency2559 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def batchC05119MinusFourthP022Upper2559 : ℝ := (((11 * 10^40
        + 8390024648421759098177739345588519914343) : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC05119MinusFourthP022Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP022ExpBound2559 :
    Real.exp batchC05119MinusFourthP022Exponent2559 ≤ batchC05119MinusFourthP022ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP022Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP022Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP022Input2559 5).1 =
      batchC05119MinusFourthP022Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP022Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP022Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP022Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP022Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP022Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP022Input2559 =
      (batchC05119MinusFourthP022Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP022Input2559,
        batchC05119MinusFourthP022Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP022Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP022Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP022Center2559))).trans
  norm_num [batchC05119MinusFourthP022Error2559, batchC05119MinusFourthP022ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP022Center2559]

theorem batchC05119MinusFourthP022Bound2559 : batchC05119MinusFourthCell2559 ⟨22, by omega⟩ ≤
    batchC05119MinusFourthP022Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      batchC05119MinusFourthP022Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP022Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP022Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP022ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP022Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP022ExpUpper2559, batchC05119MinusFourthP022Frequency2559,
        batchC05119MinusFourthP022Upper2559]

def batchC05119MinusFourthP023Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP023Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP023Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP023ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP023Frequency2559 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def batchC05119MinusFourthP023Upper2559 : ℝ := (((15 * 10^40
        + 5193678309755299690946883652748096356343) : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC05119MinusFourthP023Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP023ExpBound2559 :
    Real.exp batchC05119MinusFourthP023Exponent2559 ≤ batchC05119MinusFourthP023ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP023Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP023Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP023Input2559 5).1 =
      batchC05119MinusFourthP023Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP023Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP023Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP023Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP023Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP023Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP023Input2559 =
      (batchC05119MinusFourthP023Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP023Input2559,
        batchC05119MinusFourthP023Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP023Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP023Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP023Center2559))).trans
  norm_num [batchC05119MinusFourthP023Error2559, batchC05119MinusFourthP023ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP023Center2559]

theorem batchC05119MinusFourthP023Bound2559 : batchC05119MinusFourthCell2559 ⟨23, by omega⟩ ≤
    batchC05119MinusFourthP023Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      batchC05119MinusFourthP023Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP023Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP023Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP023ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP023Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP023ExpUpper2559, batchC05119MinusFourthP023Frequency2559,
        batchC05119MinusFourthP023Upper2559]

def batchC05119MinusFourthP024Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP024Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP024Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP024ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP024Frequency2559 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def batchC05119MinusFourthP024Upper2559 : ℝ := (((279 * 10^40
        + 5587095792064239473786804694736326254441) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119MinusFourthP024Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP024ExpBound2559 :
    Real.exp batchC05119MinusFourthP024Exponent2559 ≤ batchC05119MinusFourthP024ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP024Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP024Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP024Input2559 5).1 =
      batchC05119MinusFourthP024Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP024Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP024Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP024Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP024Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP024Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP024Input2559 =
      (batchC05119MinusFourthP024Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP024Input2559,
        batchC05119MinusFourthP024Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP024Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP024Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP024Center2559))).trans
  norm_num [batchC05119MinusFourthP024Error2559, batchC05119MinusFourthP024ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP024Center2559]

theorem batchC05119MinusFourthP024Bound2559 : batchC05119MinusFourthCell2559 ⟨24, by omega⟩ ≤
    batchC05119MinusFourthP024Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      batchC05119MinusFourthP024Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP024Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP024Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP024ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP024Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP024ExpUpper2559, batchC05119MinusFourthP024Frequency2559,
        batchC05119MinusFourthP024Upper2559]

def batchC05119MinusFourthP025Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP025Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP025Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP025ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP025Frequency2559 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def batchC05119MinusFourthP025Upper2559 : ℝ := (((10 * 10^40
        + 877241788646568162588014988192168350981) : ℝ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968))

noncomputable def batchC05119MinusFourthP025Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP025ExpBound2559 :
    Real.exp batchC05119MinusFourthP025Exponent2559 ≤ batchC05119MinusFourthP025ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP025Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP025Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP025Input2559 5).1 =
      batchC05119MinusFourthP025Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP025Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP025Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP025Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP025Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP025Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP025Input2559 =
      (batchC05119MinusFourthP025Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP025Input2559,
        batchC05119MinusFourthP025Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP025Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP025Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP025Center2559))).trans
  norm_num [batchC05119MinusFourthP025Error2559, batchC05119MinusFourthP025ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP025Center2559]

theorem batchC05119MinusFourthP025Bound2559 : batchC05119MinusFourthCell2559 ⟨25, by omega⟩ ≤
    batchC05119MinusFourthP025Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      batchC05119MinusFourthP025Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP025Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP025Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP025ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP025Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP025ExpUpper2559, batchC05119MinusFourthP025Frequency2559,
        batchC05119MinusFourthP025Upper2559]

def batchC05119MinusFourthP026Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP026Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP026Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP026ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP026Frequency2559 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def batchC05119MinusFourthP026Upper2559 : ℝ := (((372 * 10^40
        + 94954765079138679024202679818126715375) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119MinusFourthP026Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP026ExpBound2559 :
    Real.exp batchC05119MinusFourthP026Exponent2559 ≤ batchC05119MinusFourthP026ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP026Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP026Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP026Input2559 5).1 =
      batchC05119MinusFourthP026Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP026Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP026Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP026Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP026Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP026Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP026Input2559 =
      (batchC05119MinusFourthP026Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP026Input2559,
        batchC05119MinusFourthP026Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP026Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP026Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP026Center2559))).trans
  norm_num [batchC05119MinusFourthP026Error2559, batchC05119MinusFourthP026ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP026Center2559]

theorem batchC05119MinusFourthP026Bound2559 : batchC05119MinusFourthCell2559 ⟨26, by omega⟩ ≤
    batchC05119MinusFourthP026Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      batchC05119MinusFourthP026Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP026Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP026Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP026ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP026Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP026ExpUpper2559, batchC05119MinusFourthP026Frequency2559,
        batchC05119MinusFourthP026Upper2559]

def batchC05119MinusFourthP027Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP027Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP027Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP027ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP027Frequency2559 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def batchC05119MinusFourthP027Upper2559 : ℝ := (((452 * 10^40
        + 6786345091539698329946814744907837875095) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119MinusFourthP027Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP027ExpBound2559 :
    Real.exp batchC05119MinusFourthP027Exponent2559 ≤ batchC05119MinusFourthP027ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP027Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP027Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP027Input2559 5).1 =
      batchC05119MinusFourthP027Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP027Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP027Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP027Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP027Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP027Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP027Input2559 =
      (batchC05119MinusFourthP027Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP027Input2559,
        batchC05119MinusFourthP027Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP027Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP027Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP027Center2559))).trans
  norm_num [batchC05119MinusFourthP027Error2559, batchC05119MinusFourthP027ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP027Center2559]

theorem batchC05119MinusFourthP027Bound2559 : batchC05119MinusFourthCell2559 ⟨27, by omega⟩ ≤
    batchC05119MinusFourthP027Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      batchC05119MinusFourthP027Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP027Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP027Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP027ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP027Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP027ExpUpper2559, batchC05119MinusFourthP027Frequency2559,
        batchC05119MinusFourthP027Upper2559]

def batchC05119MinusFourthP028Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP028Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP028Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP028ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP028Frequency2559 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def batchC05119MinusFourthP028Upper2559 : ℝ := (((487 * 10^40
        + 9968220192092433092611214835795700831131) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119MinusFourthP028Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP028ExpBound2559 :
    Real.exp batchC05119MinusFourthP028Exponent2559 ≤ batchC05119MinusFourthP028ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP028Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP028Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP028Input2559 5).1 =
      batchC05119MinusFourthP028Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP028Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP028Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP028Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP028Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP028Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP028Input2559 =
      (batchC05119MinusFourthP028Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP028Input2559,
        batchC05119MinusFourthP028Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP028Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP028Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP028Center2559))).trans
  norm_num [batchC05119MinusFourthP028Error2559, batchC05119MinusFourthP028ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP028Center2559]

theorem batchC05119MinusFourthP028Bound2559 : batchC05119MinusFourthCell2559 ⟨28, by omega⟩ ≤
    batchC05119MinusFourthP028Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      batchC05119MinusFourthP028Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP028Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP028Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP028ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP028Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP028ExpUpper2559, batchC05119MinusFourthP028Frequency2559,
        batchC05119MinusFourthP028Upper2559]

def batchC05119MinusFourthP029Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusFourthP029Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusFourthP029Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP029ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119MinusFourthP029Frequency2559 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def batchC05119MinusFourthP029Upper2559 : ℝ := (((272 * 10^40
        + 8446216373049208469554252443189200902565) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119MinusFourthP029Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05119MinusFourthP029ExpBound2559 :
    Real.exp batchC05119MinusFourthP029Exponent2559 ≤ batchC05119MinusFourthP029ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119MinusFourthP029Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusFourthP029Input2559]
  have hc : (compactExp2547 batchC05119MinusFourthP029Input2559 5).1 =
      batchC05119MinusFourthP029Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119MinusFourthP029Input2559 5).2 : ℝ) =
      batchC05119MinusFourthP029Error2559 := by
    have hq : (compactExp2547 batchC05119MinusFourthP029Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119MinusFourthP029Error2559]
  have h := compactExp_error2547 batchC05119MinusFourthP029Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119MinusFourthP029Input2559 =
      (batchC05119MinusFourthP029Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119MinusFourthP029Input2559,
        batchC05119MinusFourthP029Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119MinusFourthP029Exponent2559 : ℂ)) (embedPair2542
        batchC05119MinusFourthP029Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119MinusFourthP029Center2559))).trans
  norm_num [batchC05119MinusFourthP029Error2559, batchC05119MinusFourthP029ExpUpper2559,
      pairMagnitude2542,
      batchC05119MinusFourthP029Center2559]

theorem batchC05119MinusFourthP029Bound2559 : batchC05119MinusFourthCell2559 ⟨29, by omega⟩ ≤
    batchC05119MinusFourthP029Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      batchC05119MinusFourthP029Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119MinusFourthP029Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119MinusFourthP029Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119MinusFourthP029ExpBound2559 using 1; norm_num
        [batchC05119MinusFourthP029Exponent2559])
  have hid : batchC05119MinusFourthCell2559 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119MinusFourthCell2559, cellNearAbs2538, batchN05119MinusPosition2559,
      batchN05120MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119MinusFourthP029ExpUpper2559, batchC05119MinusFourthP029Frequency2559,
        batchC05119MinusFourthP029Upper2559]

noncomputable def batchC05119MinusFourthUpper2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05119MinusFourthP000Upper2559
  | 1 => batchC05119MinusFourthP001Upper2559
  | 2 => batchC05119MinusFourthP002Upper2559
  | 3 => batchC05119MinusFourthP003Upper2559
  | 4 => batchC05119MinusFourthP004Upper2559
  | 5 => batchC05119MinusFourthP005Upper2559
  | 6 => batchC05119MinusFourthP006Upper2559
  | 7 => batchC05119MinusFourthP007Upper2559
  | 8 => batchC05119MinusFourthP008Upper2559
  | 9 => batchC05119MinusFourthP009Upper2559
  | 10 => batchC05119MinusFourthP010Upper2559
  | 11 => batchC05119MinusFourthP011Upper2559
  | 12 => batchC05119MinusFourthP012Upper2559
  | 13 => batchC05119MinusFourthP013Upper2559
  | 14 => batchC05119MinusFourthP014Upper2559
  | 15 => batchC05119MinusFourthP015Upper2559
  | 16 => batchC05119MinusFourthP016Upper2559
  | 17 => batchC05119MinusFourthP017Upper2559
  | 18 => batchC05119MinusFourthP018Upper2559
  | 19 => batchC05119MinusFourthP019Upper2559
  | 20 => batchC05119MinusFourthP020Upper2559
  | 21 => batchC05119MinusFourthP021Upper2559
  | 22 => batchC05119MinusFourthP022Upper2559
  | 23 => batchC05119MinusFourthP023Upper2559
  | 24 => batchC05119MinusFourthP024Upper2559
  | 25 => batchC05119MinusFourthP025Upper2559
  | 26 => batchC05119MinusFourthP026Upper2559
  | 27 => batchC05119MinusFourthP027Upper2559
  | 28 => batchC05119MinusFourthP028Upper2559
  | 29 => batchC05119MinusFourthP029Upper2559
  | _ => 0

theorem batchC05119MinusFourthBound2559 (i : Fin 30) :
    batchC05119MinusFourthCell2559 i ≤ batchC05119MinusFourthUpper2559 i := by
  fin_cases i
  · exact batchC05119MinusFourthP000Bound2559
  · exact batchC05119MinusFourthP001Bound2559
  · exact batchC05119MinusFourthP002Bound2559
  · exact batchC05119MinusFourthP003Bound2559
  · exact batchC05119MinusFourthP004Bound2559
  · exact batchC05119MinusFourthP005Bound2559
  · exact batchC05119MinusFourthP006Bound2559
  · exact batchC05119MinusFourthP007Bound2559
  · exact batchC05119MinusFourthP008Bound2559
  · exact batchC05119MinusFourthP009Bound2559
  · exact batchC05119MinusFourthP010Bound2559
  · exact batchC05119MinusFourthP011Bound2559
  · exact batchC05119MinusFourthP012Bound2559
  · exact batchC05119MinusFourthP013Bound2559
  · exact batchC05119MinusFourthP014Bound2559
  · exact batchC05119MinusFourthP015Bound2559
  · exact batchC05119MinusFourthP016Bound2559
  · exact batchC05119MinusFourthP017Bound2559
  · exact batchC05119MinusFourthP018Bound2559
  · exact batchC05119MinusFourthP019Bound2559
  · exact batchC05119MinusFourthP020Bound2559
  · exact batchC05119MinusFourthP021Bound2559
  · exact batchC05119MinusFourthP022Bound2559
  · exact batchC05119MinusFourthP023Bound2559
  · exact batchC05119MinusFourthP024Bound2559
  · exact batchC05119MinusFourthP025Bound2559
  · exact batchC05119MinusFourthP026Bound2559
  · exact batchC05119MinusFourthP027Bound2559
  · exact batchC05119MinusFourthP028Bound2559
  · exact batchC05119MinusFourthP029Bound2559

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP000Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP001Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP002Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP003Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP004Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP005Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP006Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP007Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP008Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP009Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP010Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP011Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP012Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP013Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP014Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP015Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP016Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP017Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP018Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP019Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP020Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP021Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP022Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP023Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP024Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP025Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP026Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP027Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP028Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthP029Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusFourthBound2559
