import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteABatchN05120Plus2559
import ConnesWeilRH.Dev.C1RouteABatchN05121Plus2559

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC05120PlusFourthCell2559 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 batchN05120PlusPosition2559 batchN05121PlusPosition2559 < storedWidth i ^ 2
      then
    weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 batchN05120PlusPosition2559 batchN05121PlusPosition2559 / (storedWidth i ^
          2))
      (min (max |batchN05120PlusPosition2559| |batchN05121PlusPosition2559|) (storedWidth i ^ 2) /
        (storedWidth i ^ 2)) batchN05120PlusPosition2559 batchN05121PlusPosition2559
  else 0


def batchC05120PlusFourthP000Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP000Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP000Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP000ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP000Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05120PlusFourthP000Upper2559 : ℝ := (((33 * 10^40
        + 6986667562287158807786285610076744399539) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120PlusFourthP000Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP000ExpBound2559 :
    Real.exp batchC05120PlusFourthP000Exponent2559 ≤ batchC05120PlusFourthP000ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP000Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP000Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP000Input2559 5).1 =
      batchC05120PlusFourthP000Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP000Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP000Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP000Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP000Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP000Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP000Input2559 =
      (batchC05120PlusFourthP000Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP000Input2559,
        batchC05120PlusFourthP000Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP000Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP000Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP000Center2559))).trans
  norm_num [batchC05120PlusFourthP000Error2559, batchC05120PlusFourthP000ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP000Center2559]

theorem batchC05120PlusFourthP000Bound2559 : batchC05120PlusFourthCell2559 ⟨0, by omega⟩ ≤
    batchC05120PlusFourthP000Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨0, by omega⟩)‖ ≤
      batchC05120PlusFourthP000Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP000Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP000Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    ((12980742146337070512478121581609 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5070602400912918168936766242816015625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP000ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP000Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨0, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨0, by omega⟩)
        ((12980742146337070512478121581609 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5070602400912918168936766242816015625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP000ExpUpper2559, batchC05120PlusFourthP000Frequency2559,
        batchC05120PlusFourthP000Upper2559]

def batchC05120PlusFourthP001Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP001Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP001Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP001ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP001Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05120PlusFourthP001Upper2559 : ℝ := (((33 * 10^40
        + 1833474729917330533191289284912655034549) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120PlusFourthP001Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP001ExpBound2559 :
    Real.exp batchC05120PlusFourthP001Exponent2559 ≤ batchC05120PlusFourthP001ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP001Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP001Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP001Input2559 5).1 =
      batchC05120PlusFourthP001Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP001Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP001Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP001Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP001Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP001Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP001Input2559 =
      (batchC05120PlusFourthP001Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP001Input2559,
        batchC05120PlusFourthP001Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP001Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP001Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP001Center2559))).trans
  norm_num [batchC05120PlusFourthP001Error2559, batchC05120PlusFourthP001ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP001Center2559]

theorem batchC05120PlusFourthP001Bound2559 : batchC05120PlusFourthCell2559 ⟨1, by omega⟩ ≤
    batchC05120PlusFourthP001Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      batchC05120PlusFourthP001Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP001Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP001Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) (0 : ℝ) ((39614081861595078604086562521088 : ℝ) /
        104779244925114570282650713456640625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP001ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP001Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) (0 : ℝ) ((39614081861595078604086562521088 : ℝ) /
        104779244925114570282650713456640625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP001ExpUpper2559, batchC05120PlusFourthP001Frequency2559,
        batchC05120PlusFourthP001Upper2559]

def batchC05120PlusFourthP002Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP002Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP002Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP002ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP002Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05120PlusFourthP002Upper2559 : ℝ := (((4 * 10^40
        + 1146523020945426661499737898776266695759) : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC05120PlusFourthP002Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP002ExpBound2559 :
    Real.exp batchC05120PlusFourthP002Exponent2559 ≤ batchC05120PlusFourthP002ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP002Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP002Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP002Input2559 5).1 =
      batchC05120PlusFourthP002Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP002Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP002Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP002Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP002Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP002Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP002Input2559 =
      (batchC05120PlusFourthP002Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP002Input2559,
        batchC05120PlusFourthP002Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP002Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP002Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP002Center2559))).trans
  norm_num [batchC05120PlusFourthP002Error2559, batchC05120PlusFourthP002ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP002Center2559]

theorem batchC05120PlusFourthP002Bound2559 : batchC05120PlusFourthCell2559 ⟨2, by omega⟩ ≤
    batchC05120PlusFourthP002Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      batchC05120PlusFourthP002Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP002Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP002Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        535582378596426958724104076656640625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP002ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP002Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        535582378596426958724104076656640625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP002ExpUpper2559, batchC05120PlusFourthP002Frequency2559,
        batchC05120PlusFourthP002Upper2559]

def batchC05120PlusFourthP003Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP003Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP003Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP003ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP003Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05120PlusFourthP003Upper2559 : ℝ := (((8 * 10^40
        + 1921483116806704097682079725814672354279) : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC05120PlusFourthP003Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP003ExpBound2559 :
    Real.exp batchC05120PlusFourthP003Exponent2559 ≤ batchC05120PlusFourthP003ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP003Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP003Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP003Input2559 5).1 =
      batchC05120PlusFourthP003Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP003Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP003Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP003Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP003Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP003Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP003Input2559 =
      (batchC05120PlusFourthP003Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP003Input2559,
        batchC05120PlusFourthP003Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP003Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP003Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP003Center2559))).trans
  norm_num [batchC05120PlusFourthP003Error2559, batchC05120PlusFourthP003ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP003Center2559]

theorem batchC05120PlusFourthP003Bound2559 : batchC05120PlusFourthCell2559 ⟨3, by omega⟩ ≤
    batchC05120PlusFourthP003Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      batchC05120PlusFourthP003Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP003Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP003Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP003ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP003Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP003ExpUpper2559, batchC05120PlusFourthP003Frequency2559,
        batchC05120PlusFourthP003Upper2559]

def batchC05120PlusFourthP004Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP004Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP004Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP004ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP004Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05120PlusFourthP004Upper2559 : ℝ :=
    ((319143869165444825792235041685295711561 : ℝ) /
        (142724 * 10^40
        + 7692705959881058285969449495136382746624))

noncomputable def batchC05120PlusFourthP004Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP004ExpBound2559 :
    Real.exp batchC05120PlusFourthP004Exponent2559 ≤ batchC05120PlusFourthP004ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP004Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP004Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP004Input2559 5).1 =
      batchC05120PlusFourthP004Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP004Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP004Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP004Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP004Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP004Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP004Input2559 =
      (batchC05120PlusFourthP004Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP004Input2559,
        batchC05120PlusFourthP004Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP004Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP004Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP004Center2559))).trans
  norm_num [batchC05120PlusFourthP004Error2559, batchC05120PlusFourthP004ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP004Center2559]

theorem batchC05120PlusFourthP004Bound2559 : batchC05120PlusFourthCell2559 ⟨4, by omega⟩ ≤
    batchC05120PlusFourthP004Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      batchC05120PlusFourthP004Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP004Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP004Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        811296384146067132209863967375390625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP004ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP004Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        811296384146067132209863967375390625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP004ExpUpper2559, batchC05120PlusFourthP004Frequency2559,
        batchC05120PlusFourthP004Upper2559]

def batchC05120PlusFourthP005Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP005Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP005Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP005ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP005Frequency2559 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC05120PlusFourthP005Upper2559 : ℝ :=
    ((11674988018847392277171221784072946191 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120PlusFourthP005Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP005ExpBound2559 :
    Real.exp batchC05120PlusFourthP005Exponent2559 ≤ batchC05120PlusFourthP005ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP005Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP005Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP005Input2559 5).1 =
      batchC05120PlusFourthP005Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP005Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP005Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP005Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP005Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP005Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP005Input2559 =
      (batchC05120PlusFourthP005Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP005Input2559,
        batchC05120PlusFourthP005Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP005Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP005Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP005Center2559))).trans
  norm_num [batchC05120PlusFourthP005Error2559, batchC05120PlusFourthP005ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP005Center2559]

theorem batchC05120PlusFourthP005Bound2559 : batchC05120PlusFourthCell2559 ⟨5, by omega⟩ ≤
    batchC05120PlusFourthP005Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨5, by omega⟩)‖ ≤
      batchC05120PlusFourthP005Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP005Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP005Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    ((14311268216336621374914235141089 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5590339147006492724575873101987890625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP005ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP005Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨5, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨5, by omega⟩)
        ((14311268216336621374914235141089 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5590339147006492724575873101987890625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP005ExpUpper2559, batchC05120PlusFourthP005Frequency2559,
        batchC05120PlusFourthP005Upper2559]

def batchC05120PlusFourthP006Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP006Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP006Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP006ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP006Frequency2559 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC05120PlusFourthP006Upper2559 : ℝ :=
    ((1545240379027766584475271547307092303 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC05120PlusFourthP006Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP006ExpBound2559 :
    Real.exp batchC05120PlusFourthP006Exponent2559 ≤ batchC05120PlusFourthP006ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP006Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP006Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP006Input2559 5).1 =
      batchC05120PlusFourthP006Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP006Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP006Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP006Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP006Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP006Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP006Input2559 =
      (batchC05120PlusFourthP006Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP006Input2559,
        batchC05120PlusFourthP006Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP006Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP006Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP006Center2559))).trans
  norm_num [batchC05120PlusFourthP006Error2559, batchC05120PlusFourthP006ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP006Center2559]

theorem batchC05120PlusFourthP006Bound2559 : batchC05120PlusFourthCell2559 ⟨6, by omega⟩ ≤
    batchC05120PlusFourthP006Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      batchC05120PlusFourthP006Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP006Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP006Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) (0 : ℝ) ((65536001 : ℝ) /
        204800000000) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP006ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP006Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) (0 : ℝ) ((65536001 : ℝ) /
        204800000000) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP006ExpUpper2559, batchC05120PlusFourthP006Frequency2559,
        batchC05120PlusFourthP006Upper2559]

def batchC05120PlusFourthP007Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP007Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP007Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP007ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP007Frequency2559 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC05120PlusFourthP007Upper2559 : ℝ := ((65053358101589633320478942525855053
    : ℝ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968))

noncomputable def batchC05120PlusFourthP007Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP007ExpBound2559 :
    Real.exp batchC05120PlusFourthP007Exponent2559 ≤ batchC05120PlusFourthP007ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP007Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP007Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP007Input2559 5).1 =
      batchC05120PlusFourthP007Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP007Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP007Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP007Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP007Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP007Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP007Input2559 =
      (batchC05120PlusFourthP007Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP007Input2559,
        batchC05120PlusFourthP007Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP007Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP007Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP007Center2559))).trans
  norm_num [batchC05120PlusFourthP007Error2559, batchC05120PlusFourthP007ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP007Center2559]

theorem batchC05120PlusFourthP007Bound2559 : batchC05120PlusFourthCell2559 ⟨7, by omega⟩ ≤
    batchC05120PlusFourthP007Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      batchC05120PlusFourthP007Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP007Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP007Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP007ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP007Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP007ExpUpper2559, batchC05120PlusFourthP007Frequency2559,
        batchC05120PlusFourthP007Upper2559]

def batchC05120PlusFourthP008Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP008Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP008Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP008ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP008Frequency2559 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def batchC05120PlusFourthP008Upper2559 : ℝ :=
    ((1632940905703249210481260534584507374399 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC05120PlusFourthP008Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP008ExpBound2559 :
    Real.exp batchC05120PlusFourthP008Exponent2559 ≤ batchC05120PlusFourthP008ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP008Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP008Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP008Input2559 5).1 =
      batchC05120PlusFourthP008Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP008Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP008Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP008Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP008Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP008Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP008Input2559 =
      (batchC05120PlusFourthP008Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP008Input2559,
        batchC05120PlusFourthP008Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP008Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP008Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP008Center2559))).trans
  norm_num [batchC05120PlusFourthP008Error2559, batchC05120PlusFourthP008ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP008Center2559]

theorem batchC05120PlusFourthP008Bound2559 : batchC05120PlusFourthCell2559 ⟨8, by omega⟩ ≤
    batchC05120PlusFourthP008Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      batchC05120PlusFourthP008Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP008Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP008Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP008ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP008Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP008ExpUpper2559, batchC05120PlusFourthP008Frequency2559,
        batchC05120PlusFourthP008Upper2559]

def batchC05120PlusFourthP009Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP009Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP009Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP009ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP009Frequency2559 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def batchC05120PlusFourthP009Upper2559 : ℝ := (((1 * 10^40
        + 4542223335602797445439734824814323504963) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120PlusFourthP009Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP009ExpBound2559 :
    Real.exp batchC05120PlusFourthP009Exponent2559 ≤ batchC05120PlusFourthP009ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP009Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP009Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP009Input2559 5).1 =
      batchC05120PlusFourthP009Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP009Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP009Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP009Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP009Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP009Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP009Input2559 =
      (batchC05120PlusFourthP009Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP009Input2559,
        batchC05120PlusFourthP009Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP009Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP009Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP009Center2559))).trans
  norm_num [batchC05120PlusFourthP009Error2559, batchC05120PlusFourthP009ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP009Center2559]

theorem batchC05120PlusFourthP009Bound2559 : batchC05120PlusFourthCell2559 ⟨9, by omega⟩ ≤
    batchC05120PlusFourthP009Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      batchC05120PlusFourthP009Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP009Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP009Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP009ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP009Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP009ExpUpper2559, batchC05120PlusFourthP009Frequency2559,
        batchC05120PlusFourthP009Upper2559]

def batchC05120PlusFourthP010Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP010Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP010Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP010ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP010Frequency2559 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def batchC05120PlusFourthP010Upper2559 : ℝ := (((2 * 10^40
        + 8445577044430899163613284817764845464241) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120PlusFourthP010Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP010ExpBound2559 :
    Real.exp batchC05120PlusFourthP010Exponent2559 ≤ batchC05120PlusFourthP010ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP010Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP010Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP010Input2559 5).1 =
      batchC05120PlusFourthP010Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP010Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP010Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP010Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP010Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP010Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP010Input2559 =
      (batchC05120PlusFourthP010Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP010Input2559,
        batchC05120PlusFourthP010Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP010Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP010Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP010Center2559))).trans
  norm_num [batchC05120PlusFourthP010Error2559, batchC05120PlusFourthP010ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP010Center2559]

theorem batchC05120PlusFourthP010Bound2559 : batchC05120PlusFourthCell2559 ⟨10, by omega⟩ ≤
    batchC05120PlusFourthP010Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      batchC05120PlusFourthP010Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP010Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP010Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP010ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP010Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP010ExpUpper2559, batchC05120PlusFourthP010Frequency2559,
        batchC05120PlusFourthP010Upper2559]

def batchC05120PlusFourthP011Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP011Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP011Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP011ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP011Frequency2559 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def batchC05120PlusFourthP011Upper2559 : ℝ := (((8 * 10^40
        + 4318014266247539741551097150765614777993) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120PlusFourthP011Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP011ExpBound2559 :
    Real.exp batchC05120PlusFourthP011Exponent2559 ≤ batchC05120PlusFourthP011ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP011Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP011Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP011Input2559 5).1 =
      batchC05120PlusFourthP011Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP011Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP011Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP011Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP011Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP011Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP011Input2559 =
      (batchC05120PlusFourthP011Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP011Input2559,
        batchC05120PlusFourthP011Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP011Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP011Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP011Center2559))).trans
  norm_num [batchC05120PlusFourthP011Error2559, batchC05120PlusFourthP011ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP011Center2559]

theorem batchC05120PlusFourthP011Bound2559 : batchC05120PlusFourthCell2559 ⟨11, by omega⟩ ≤
    batchC05120PlusFourthP011Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      batchC05120PlusFourthP011Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP011Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP011Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP011ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP011Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP011ExpUpper2559, batchC05120PlusFourthP011Frequency2559,
        batchC05120PlusFourthP011Upper2559]

def batchC05120PlusFourthP012Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP012Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP012Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP012ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP012Frequency2559 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def batchC05120PlusFourthP012Upper2559 : ℝ := (((1 * 10^40
        + 5277560075846031619885527329175232759707) : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC05120PlusFourthP012Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP012ExpBound2559 :
    Real.exp batchC05120PlusFourthP012Exponent2559 ≤ batchC05120PlusFourthP012ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP012Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP012Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP012Input2559 5).1 =
      batchC05120PlusFourthP012Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP012Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP012Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP012Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP012Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP012Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP012Input2559 =
      (batchC05120PlusFourthP012Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP012Input2559,
        batchC05120PlusFourthP012Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP012Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP012Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP012Center2559))).trans
  norm_num [batchC05120PlusFourthP012Error2559, batchC05120PlusFourthP012ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP012Center2559]

theorem batchC05120PlusFourthP012Bound2559 : batchC05120PlusFourthCell2559 ⟨12, by omega⟩ ≤
    batchC05120PlusFourthP012Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      batchC05120PlusFourthP012Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP012Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP012Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP012ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP012Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP012ExpUpper2559, batchC05120PlusFourthP012Frequency2559,
        batchC05120PlusFourthP012Upper2559]

def batchC05120PlusFourthP013Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP013Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP013Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP013ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP013Frequency2559 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def batchC05120PlusFourthP013Upper2559 : ℝ := (((16 * 10^40
        + 6837949523115563859000360871046890931297) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120PlusFourthP013Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP013ExpBound2559 :
    Real.exp batchC05120PlusFourthP013Exponent2559 ≤ batchC05120PlusFourthP013ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP013Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP013Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP013Input2559 5).1 =
      batchC05120PlusFourthP013Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP013Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP013Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP013Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP013Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP013Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP013Input2559 =
      (batchC05120PlusFourthP013Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP013Input2559,
        batchC05120PlusFourthP013Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP013Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP013Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP013Center2559))).trans
  norm_num [batchC05120PlusFourthP013Error2559, batchC05120PlusFourthP013ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP013Center2559]

theorem batchC05120PlusFourthP013Bound2559 : batchC05120PlusFourthCell2559 ⟨13, by omega⟩ ≤
    batchC05120PlusFourthP013Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      batchC05120PlusFourthP013Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP013Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP013Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP013ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP013Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP013ExpUpper2559, batchC05120PlusFourthP013Frequency2559,
        batchC05120PlusFourthP013Upper2559]

def batchC05120PlusFourthP014Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP014Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP014Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP014ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP014Frequency2559 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def batchC05120PlusFourthP014Upper2559 : ℝ := (((14 * 10^40
        + 361698572858198437249921517049598220201) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120PlusFourthP014Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP014ExpBound2559 :
    Real.exp batchC05120PlusFourthP014Exponent2559 ≤ batchC05120PlusFourthP014ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP014Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP014Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP014Input2559 5).1 =
      batchC05120PlusFourthP014Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP014Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP014Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP014Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP014Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP014Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP014Input2559 =
      (batchC05120PlusFourthP014Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP014Input2559,
        batchC05120PlusFourthP014Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP014Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP014Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP014Center2559))).trans
  norm_num [batchC05120PlusFourthP014Error2559, batchC05120PlusFourthP014ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP014Center2559]

theorem batchC05120PlusFourthP014Bound2559 : batchC05120PlusFourthCell2559 ⟨14, by omega⟩ ≤
    batchC05120PlusFourthP014Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      batchC05120PlusFourthP014Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP014Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP014Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP014ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP014Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP014ExpUpper2559, batchC05120PlusFourthP014Frequency2559,
        batchC05120PlusFourthP014Upper2559]

def batchC05120PlusFourthP015Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP015Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP015Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP015ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP015Frequency2559 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def batchC05120PlusFourthP015Upper2559 : ℝ := (((39 * 10^40
        + 2677361324008412817987528877049788573141) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120PlusFourthP015Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP015ExpBound2559 :
    Real.exp batchC05120PlusFourthP015Exponent2559 ≤ batchC05120PlusFourthP015ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP015Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP015Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP015Input2559 5).1 =
      batchC05120PlusFourthP015Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP015Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP015Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP015Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP015Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP015Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP015Input2559 =
      (batchC05120PlusFourthP015Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP015Input2559,
        batchC05120PlusFourthP015Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP015Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP015Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP015Center2559))).trans
  norm_num [batchC05120PlusFourthP015Error2559, batchC05120PlusFourthP015ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP015Center2559]

theorem batchC05120PlusFourthP015Bound2559 : batchC05120PlusFourthCell2559 ⟨15, by omega⟩ ≤
    batchC05120PlusFourthP015Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      batchC05120PlusFourthP015Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP015Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP015Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP015ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP015Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP015ExpUpper2559, batchC05120PlusFourthP015Frequency2559,
        batchC05120PlusFourthP015Upper2559]

def batchC05120PlusFourthP016Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP016Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP016Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP016ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP016Frequency2559 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def batchC05120PlusFourthP016Upper2559 : ℝ := (((24 * 10^40
        + 6201010231334217657786310680889075551089) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120PlusFourthP016Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP016ExpBound2559 :
    Real.exp batchC05120PlusFourthP016Exponent2559 ≤ batchC05120PlusFourthP016ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP016Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP016Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP016Input2559 5).1 =
      batchC05120PlusFourthP016Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP016Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP016Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP016Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP016Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP016Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP016Input2559 =
      (batchC05120PlusFourthP016Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP016Input2559,
        batchC05120PlusFourthP016Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP016Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP016Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP016Center2559))).trans
  norm_num [batchC05120PlusFourthP016Error2559, batchC05120PlusFourthP016ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP016Center2559]

theorem batchC05120PlusFourthP016Bound2559 : batchC05120PlusFourthCell2559 ⟨16, by omega⟩ ≤
    batchC05120PlusFourthP016Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      batchC05120PlusFourthP016Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP016Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP016Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP016ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP016Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP016ExpUpper2559, batchC05120PlusFourthP016Frequency2559,
        batchC05120PlusFourthP016Upper2559]

def batchC05120PlusFourthP017Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP017Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP017Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP017ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP017Frequency2559 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def batchC05120PlusFourthP017Upper2559 : ℝ := (((73 * 10^40
        + 9260124292652928899991279722425775921803) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120PlusFourthP017Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP017ExpBound2559 :
    Real.exp batchC05120PlusFourthP017Exponent2559 ≤ batchC05120PlusFourthP017ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP017Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP017Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP017Input2559 5).1 =
      batchC05120PlusFourthP017Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP017Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP017Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP017Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP017Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP017Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP017Input2559 =
      (batchC05120PlusFourthP017Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP017Input2559,
        batchC05120PlusFourthP017Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP017Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP017Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP017Center2559))).trans
  norm_num [batchC05120PlusFourthP017Error2559, batchC05120PlusFourthP017ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP017Center2559]

theorem batchC05120PlusFourthP017Bound2559 : batchC05120PlusFourthCell2559 ⟨17, by omega⟩ ≤
    batchC05120PlusFourthP017Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      batchC05120PlusFourthP017Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP017Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP017Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP017ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP017Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP017ExpUpper2559, batchC05120PlusFourthP017Frequency2559,
        batchC05120PlusFourthP017Upper2559]

def batchC05120PlusFourthP018Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP018Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP018Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP018ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP018Frequency2559 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def batchC05120PlusFourthP018Upper2559 : ℝ :=
    ((6667095131675882463601446325266484992903 : ℝ) /
        (1141798 * 10^40
        + 1541647679048466287755595961091061972992))

noncomputable def batchC05120PlusFourthP018Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP018ExpBound2559 :
    Real.exp batchC05120PlusFourthP018Exponent2559 ≤ batchC05120PlusFourthP018ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP018Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP018Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP018Input2559 5).1 =
      batchC05120PlusFourthP018Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP018Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP018Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP018Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP018Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP018Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP018Input2559 =
      (batchC05120PlusFourthP018Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP018Input2559,
        batchC05120PlusFourthP018Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP018Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP018Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP018Center2559))).trans
  norm_num [batchC05120PlusFourthP018Error2559, batchC05120PlusFourthP018ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP018Center2559]

theorem batchC05120PlusFourthP018Bound2559 : batchC05120PlusFourthCell2559 ⟨18, by omega⟩ ≤
    batchC05120PlusFourthP018Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      batchC05120PlusFourthP018Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP018Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP018Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP018ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP018Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP018ExpUpper2559, batchC05120PlusFourthP018Frequency2559,
        batchC05120PlusFourthP018Upper2559]

def batchC05120PlusFourthP019Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP019Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP019Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP019ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP019Frequency2559 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def batchC05120PlusFourthP019Upper2559 : ℝ := (((109 * 10^40
        + 2661023715143872465616857530169628556751) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120PlusFourthP019Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP019ExpBound2559 :
    Real.exp batchC05120PlusFourthP019Exponent2559 ≤ batchC05120PlusFourthP019ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP019Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP019Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP019Input2559 5).1 =
      batchC05120PlusFourthP019Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP019Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP019Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP019Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP019Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP019Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP019Input2559 =
      (batchC05120PlusFourthP019Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP019Input2559,
        batchC05120PlusFourthP019Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP019Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP019Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP019Center2559))).trans
  norm_num [batchC05120PlusFourthP019Error2559, batchC05120PlusFourthP019ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP019Center2559]

theorem batchC05120PlusFourthP019Bound2559 : batchC05120PlusFourthCell2559 ⟨19, by omega⟩ ≤
    batchC05120PlusFourthP019Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      batchC05120PlusFourthP019Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP019Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP019Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP019ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP019Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP019ExpUpper2559, batchC05120PlusFourthP019Frequency2559,
        batchC05120PlusFourthP019Upper2559]

def batchC05120PlusFourthP020Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP020Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP020Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP020ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP020Frequency2559 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def batchC05120PlusFourthP020Upper2559 : ℝ := (((140 * 10^40
        + 6644802555729554046236806182008087307495) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120PlusFourthP020Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP020ExpBound2559 :
    Real.exp batchC05120PlusFourthP020Exponent2559 ≤ batchC05120PlusFourthP020ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP020Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP020Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP020Input2559 5).1 =
      batchC05120PlusFourthP020Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP020Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP020Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP020Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP020Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP020Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP020Input2559 =
      (batchC05120PlusFourthP020Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP020Input2559,
        batchC05120PlusFourthP020Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP020Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP020Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP020Center2559))).trans
  norm_num [batchC05120PlusFourthP020Error2559, batchC05120PlusFourthP020ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP020Center2559]

theorem batchC05120PlusFourthP020Bound2559 : batchC05120PlusFourthCell2559 ⟨20, by omega⟩ ≤
    batchC05120PlusFourthP020Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      batchC05120PlusFourthP020Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP020Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP020Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP020ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP020Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP020ExpUpper2559, batchC05120PlusFourthP020Frequency2559,
        batchC05120PlusFourthP020Upper2559]

def batchC05120PlusFourthP021Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP021Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP021Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP021ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP021Frequency2559 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def batchC05120PlusFourthP021Upper2559 : ℝ := (((171 * 10^40
        + 6876705691398468410181972270403907439335) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120PlusFourthP021Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP021ExpBound2559 :
    Real.exp batchC05120PlusFourthP021Exponent2559 ≤ batchC05120PlusFourthP021ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP021Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP021Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP021Input2559 5).1 =
      batchC05120PlusFourthP021Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP021Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP021Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP021Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP021Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP021Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP021Input2559 =
      (batchC05120PlusFourthP021Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP021Input2559,
        batchC05120PlusFourthP021Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP021Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP021Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP021Center2559))).trans
  norm_num [batchC05120PlusFourthP021Error2559, batchC05120PlusFourthP021ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP021Center2559]

theorem batchC05120PlusFourthP021Bound2559 : batchC05120PlusFourthCell2559 ⟨21, by omega⟩ ≤
    batchC05120PlusFourthP021Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      batchC05120PlusFourthP021Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP021Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP021Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP021ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP021Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP021ExpUpper2559, batchC05120PlusFourthP021Frequency2559,
        batchC05120PlusFourthP021Upper2559]

def batchC05120PlusFourthP022Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP022Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP022Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP022ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP022Frequency2559 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def batchC05120PlusFourthP022Upper2559 : ℝ := (((11 * 10^40
        + 8390024648421759098177739345588519914343) : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC05120PlusFourthP022Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP022ExpBound2559 :
    Real.exp batchC05120PlusFourthP022Exponent2559 ≤ batchC05120PlusFourthP022ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP022Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP022Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP022Input2559 5).1 =
      batchC05120PlusFourthP022Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP022Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP022Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP022Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP022Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP022Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP022Input2559 =
      (batchC05120PlusFourthP022Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP022Input2559,
        batchC05120PlusFourthP022Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP022Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP022Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP022Center2559))).trans
  norm_num [batchC05120PlusFourthP022Error2559, batchC05120PlusFourthP022ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP022Center2559]

theorem batchC05120PlusFourthP022Bound2559 : batchC05120PlusFourthCell2559 ⟨22, by omega⟩ ≤
    batchC05120PlusFourthP022Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      batchC05120PlusFourthP022Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP022Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP022Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP022ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP022Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP022ExpUpper2559, batchC05120PlusFourthP022Frequency2559,
        batchC05120PlusFourthP022Upper2559]

def batchC05120PlusFourthP023Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP023Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP023Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP023ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP023Frequency2559 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def batchC05120PlusFourthP023Upper2559 : ℝ := (((15 * 10^40
        + 5193678309755299690946883652748096356343) : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC05120PlusFourthP023Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP023ExpBound2559 :
    Real.exp batchC05120PlusFourthP023Exponent2559 ≤ batchC05120PlusFourthP023ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP023Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP023Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP023Input2559 5).1 =
      batchC05120PlusFourthP023Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP023Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP023Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP023Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP023Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP023Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP023Input2559 =
      (batchC05120PlusFourthP023Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP023Input2559,
        batchC05120PlusFourthP023Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP023Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP023Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP023Center2559))).trans
  norm_num [batchC05120PlusFourthP023Error2559, batchC05120PlusFourthP023ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP023Center2559]

theorem batchC05120PlusFourthP023Bound2559 : batchC05120PlusFourthCell2559 ⟨23, by omega⟩ ≤
    batchC05120PlusFourthP023Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      batchC05120PlusFourthP023Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP023Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP023Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP023ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP023Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP023ExpUpper2559, batchC05120PlusFourthP023Frequency2559,
        batchC05120PlusFourthP023Upper2559]

def batchC05120PlusFourthP024Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP024Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP024Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP024ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP024Frequency2559 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def batchC05120PlusFourthP024Upper2559 : ℝ := (((279 * 10^40
        + 5587095792064239473786804694736326254441) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120PlusFourthP024Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP024ExpBound2559 :
    Real.exp batchC05120PlusFourthP024Exponent2559 ≤ batchC05120PlusFourthP024ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP024Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP024Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP024Input2559 5).1 =
      batchC05120PlusFourthP024Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP024Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP024Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP024Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP024Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP024Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP024Input2559 =
      (batchC05120PlusFourthP024Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP024Input2559,
        batchC05120PlusFourthP024Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP024Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP024Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP024Center2559))).trans
  norm_num [batchC05120PlusFourthP024Error2559, batchC05120PlusFourthP024ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP024Center2559]

theorem batchC05120PlusFourthP024Bound2559 : batchC05120PlusFourthCell2559 ⟨24, by omega⟩ ≤
    batchC05120PlusFourthP024Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      batchC05120PlusFourthP024Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP024Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP024Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP024ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP024Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP024ExpUpper2559, batchC05120PlusFourthP024Frequency2559,
        batchC05120PlusFourthP024Upper2559]

def batchC05120PlusFourthP025Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP025Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP025Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP025ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP025Frequency2559 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def batchC05120PlusFourthP025Upper2559 : ℝ := (((10 * 10^40
        + 877241788646568162588014988192168350981) : ℝ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968))

noncomputable def batchC05120PlusFourthP025Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP025ExpBound2559 :
    Real.exp batchC05120PlusFourthP025Exponent2559 ≤ batchC05120PlusFourthP025ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP025Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP025Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP025Input2559 5).1 =
      batchC05120PlusFourthP025Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP025Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP025Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP025Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP025Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP025Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP025Input2559 =
      (batchC05120PlusFourthP025Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP025Input2559,
        batchC05120PlusFourthP025Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP025Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP025Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP025Center2559))).trans
  norm_num [batchC05120PlusFourthP025Error2559, batchC05120PlusFourthP025ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP025Center2559]

theorem batchC05120PlusFourthP025Bound2559 : batchC05120PlusFourthCell2559 ⟨25, by omega⟩ ≤
    batchC05120PlusFourthP025Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      batchC05120PlusFourthP025Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP025Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP025Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP025ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP025Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP025ExpUpper2559, batchC05120PlusFourthP025Frequency2559,
        batchC05120PlusFourthP025Upper2559]

def batchC05120PlusFourthP026Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP026Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP026Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP026ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP026Frequency2559 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def batchC05120PlusFourthP026Upper2559 : ℝ := (((372 * 10^40
        + 94954765079138679024202679818126715375) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120PlusFourthP026Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP026ExpBound2559 :
    Real.exp batchC05120PlusFourthP026Exponent2559 ≤ batchC05120PlusFourthP026ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP026Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP026Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP026Input2559 5).1 =
      batchC05120PlusFourthP026Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP026Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP026Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP026Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP026Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP026Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP026Input2559 =
      (batchC05120PlusFourthP026Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP026Input2559,
        batchC05120PlusFourthP026Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP026Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP026Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP026Center2559))).trans
  norm_num [batchC05120PlusFourthP026Error2559, batchC05120PlusFourthP026ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP026Center2559]

theorem batchC05120PlusFourthP026Bound2559 : batchC05120PlusFourthCell2559 ⟨26, by omega⟩ ≤
    batchC05120PlusFourthP026Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      batchC05120PlusFourthP026Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP026Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP026Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP026ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP026Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP026ExpUpper2559, batchC05120PlusFourthP026Frequency2559,
        batchC05120PlusFourthP026Upper2559]

def batchC05120PlusFourthP027Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP027Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP027Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP027ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP027Frequency2559 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def batchC05120PlusFourthP027Upper2559 : ℝ := (((452 * 10^40
        + 6786345091539698329946814744907837875095) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120PlusFourthP027Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP027ExpBound2559 :
    Real.exp batchC05120PlusFourthP027Exponent2559 ≤ batchC05120PlusFourthP027ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP027Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP027Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP027Input2559 5).1 =
      batchC05120PlusFourthP027Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP027Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP027Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP027Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP027Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP027Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP027Input2559 =
      (batchC05120PlusFourthP027Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP027Input2559,
        batchC05120PlusFourthP027Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP027Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP027Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP027Center2559))).trans
  norm_num [batchC05120PlusFourthP027Error2559, batchC05120PlusFourthP027ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP027Center2559]

theorem batchC05120PlusFourthP027Bound2559 : batchC05120PlusFourthCell2559 ⟨27, by omega⟩ ≤
    batchC05120PlusFourthP027Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      batchC05120PlusFourthP027Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP027Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP027Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP027ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP027Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP027ExpUpper2559, batchC05120PlusFourthP027Frequency2559,
        batchC05120PlusFourthP027Upper2559]

def batchC05120PlusFourthP028Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP028Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP028Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP028ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP028Frequency2559 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def batchC05120PlusFourthP028Upper2559 : ℝ := (((487 * 10^40
        + 9968220192092433092611214835795700831131) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120PlusFourthP028Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP028ExpBound2559 :
    Real.exp batchC05120PlusFourthP028Exponent2559 ≤ batchC05120PlusFourthP028ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP028Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP028Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP028Input2559 5).1 =
      batchC05120PlusFourthP028Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP028Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP028Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP028Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP028Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP028Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP028Input2559 =
      (batchC05120PlusFourthP028Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP028Input2559,
        batchC05120PlusFourthP028Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP028Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP028Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP028Center2559))).trans
  norm_num [batchC05120PlusFourthP028Error2559, batchC05120PlusFourthP028ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP028Center2559]

theorem batchC05120PlusFourthP028Bound2559 : batchC05120PlusFourthCell2559 ⟨28, by omega⟩ ≤
    batchC05120PlusFourthP028Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      batchC05120PlusFourthP028Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP028Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP028Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP028ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP028Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP028ExpUpper2559, batchC05120PlusFourthP028Frequency2559,
        batchC05120PlusFourthP028Upper2559]

def batchC05120PlusFourthP029Input2559 : RatPair2542 := ((((-3071934463999) : ℚ) /
        3276800000000),
    ((0 : ℚ) /
        1))

def batchC05120PlusFourthP029Center2559 : RatPair2542 := (((68424684240621388324808134511496993 :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusFourthP029Error2559 : ℝ := ((12295182894598806073537677760679 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP029ExpUpper2559 : ℝ := (((15046747 * 10^40
        + 1898928886572644482158050116257596315815) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120PlusFourthP029Frequency2559 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def batchC05120PlusFourthP029Upper2559 : ℝ := (((272 * 10^40
        + 8446216373049208469554252443189200902565) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120PlusFourthP029Exponent2559 : ℝ := (((-3071934463999) : ℝ) /
        102400000000)

theorem batchC05120PlusFourthP029ExpBound2559 :
    Real.exp batchC05120PlusFourthP029Exponent2559 ≤ batchC05120PlusFourthP029ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120PlusFourthP029Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120PlusFourthP029Input2559]
  have hc : (compactExp2547 batchC05120PlusFourthP029Input2559 5).1 =
      batchC05120PlusFourthP029Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120PlusFourthP029Input2559 5).2 : ℝ) =
      batchC05120PlusFourthP029Error2559 := by
    have hq : (compactExp2547 batchC05120PlusFourthP029Input2559 5).2 =
        ((12295182894598806073537677760679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120PlusFourthP029Error2559]
  have h := compactExp_error2547 batchC05120PlusFourthP029Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120PlusFourthP029Input2559 =
      (batchC05120PlusFourthP029Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120PlusFourthP029Input2559,
        batchC05120PlusFourthP029Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120PlusFourthP029Exponent2559 : ℂ)) (embedPair2542
        batchC05120PlusFourthP029Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120PlusFourthP029Center2559))).trans
  norm_num [batchC05120PlusFourthP029Error2559, batchC05120PlusFourthP029ExpUpper2559,
      pairMagnitude2542,
      batchC05120PlusFourthP029Center2559]

theorem batchC05120PlusFourthP029Bound2559 : batchC05120PlusFourthCell2559 ⟨29, by omega⟩ ≤
    batchC05120PlusFourthP029Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      batchC05120PlusFourthP029Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120PlusFourthP029Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120PlusFourthP029Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120PlusFourthP029ExpBound2559 using 1; norm_num
        [batchC05120PlusFourthP029Exponent2559])
  have hid : batchC05120PlusFourthCell2559 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120PlusFourthCell2559, cellNearAbs2538, batchN05120PlusPosition2559,
      batchN05121PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120PlusFourthP029ExpUpper2559, batchC05120PlusFourthP029Frequency2559,
        batchC05120PlusFourthP029Upper2559]

noncomputable def batchC05120PlusFourthUpper2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05120PlusFourthP000Upper2559
  | 1 => batchC05120PlusFourthP001Upper2559
  | 2 => batchC05120PlusFourthP002Upper2559
  | 3 => batchC05120PlusFourthP003Upper2559
  | 4 => batchC05120PlusFourthP004Upper2559
  | 5 => batchC05120PlusFourthP005Upper2559
  | 6 => batchC05120PlusFourthP006Upper2559
  | 7 => batchC05120PlusFourthP007Upper2559
  | 8 => batchC05120PlusFourthP008Upper2559
  | 9 => batchC05120PlusFourthP009Upper2559
  | 10 => batchC05120PlusFourthP010Upper2559
  | 11 => batchC05120PlusFourthP011Upper2559
  | 12 => batchC05120PlusFourthP012Upper2559
  | 13 => batchC05120PlusFourthP013Upper2559
  | 14 => batchC05120PlusFourthP014Upper2559
  | 15 => batchC05120PlusFourthP015Upper2559
  | 16 => batchC05120PlusFourthP016Upper2559
  | 17 => batchC05120PlusFourthP017Upper2559
  | 18 => batchC05120PlusFourthP018Upper2559
  | 19 => batchC05120PlusFourthP019Upper2559
  | 20 => batchC05120PlusFourthP020Upper2559
  | 21 => batchC05120PlusFourthP021Upper2559
  | 22 => batchC05120PlusFourthP022Upper2559
  | 23 => batchC05120PlusFourthP023Upper2559
  | 24 => batchC05120PlusFourthP024Upper2559
  | 25 => batchC05120PlusFourthP025Upper2559
  | 26 => batchC05120PlusFourthP026Upper2559
  | 27 => batchC05120PlusFourthP027Upper2559
  | 28 => batchC05120PlusFourthP028Upper2559
  | 29 => batchC05120PlusFourthP029Upper2559
  | _ => 0

theorem batchC05120PlusFourthBound2559 (i : Fin 30) :
    batchC05120PlusFourthCell2559 i ≤ batchC05120PlusFourthUpper2559 i := by
  fin_cases i
  · exact batchC05120PlusFourthP000Bound2559
  · exact batchC05120PlusFourthP001Bound2559
  · exact batchC05120PlusFourthP002Bound2559
  · exact batchC05120PlusFourthP003Bound2559
  · exact batchC05120PlusFourthP004Bound2559
  · exact batchC05120PlusFourthP005Bound2559
  · exact batchC05120PlusFourthP006Bound2559
  · exact batchC05120PlusFourthP007Bound2559
  · exact batchC05120PlusFourthP008Bound2559
  · exact batchC05120PlusFourthP009Bound2559
  · exact batchC05120PlusFourthP010Bound2559
  · exact batchC05120PlusFourthP011Bound2559
  · exact batchC05120PlusFourthP012Bound2559
  · exact batchC05120PlusFourthP013Bound2559
  · exact batchC05120PlusFourthP014Bound2559
  · exact batchC05120PlusFourthP015Bound2559
  · exact batchC05120PlusFourthP016Bound2559
  · exact batchC05120PlusFourthP017Bound2559
  · exact batchC05120PlusFourthP018Bound2559
  · exact batchC05120PlusFourthP019Bound2559
  · exact batchC05120PlusFourthP020Bound2559
  · exact batchC05120PlusFourthP021Bound2559
  · exact batchC05120PlusFourthP022Bound2559
  · exact batchC05120PlusFourthP023Bound2559
  · exact batchC05120PlusFourthP024Bound2559
  · exact batchC05120PlusFourthP025Bound2559
  · exact batchC05120PlusFourthP026Bound2559
  · exact batchC05120PlusFourthP027Bound2559
  · exact batchC05120PlusFourthP028Bound2559
  · exact batchC05120PlusFourthP029Bound2559

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP000Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP001Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP002Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP003Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP004Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP005Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP006Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP007Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP008Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP009Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP010Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP011Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP012Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP013Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP014Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP015Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP016Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP017Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP018Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP019Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP020Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP021Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP022Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP023Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP024Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP025Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP026Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP027Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP028Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthP029Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusFourthBound2559
