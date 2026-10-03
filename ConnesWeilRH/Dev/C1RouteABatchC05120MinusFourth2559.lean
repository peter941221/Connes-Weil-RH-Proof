import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteABatchN05120Minus2559
import ConnesWeilRH.Dev.C1RouteABatchN05121Minus2559

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC05120MinusFourthCell2559 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 batchN05120MinusPosition2559 batchN05121MinusPosition2559 < storedWidth i ^ 2
      then
    weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 batchN05120MinusPosition2559 batchN05121MinusPosition2559 / (storedWidth i
          ^ 2))
      (min (max |batchN05120MinusPosition2559| |batchN05121MinusPosition2559|) (storedWidth i ^ 2)
          /
        (storedWidth i ^ 2)) batchN05120MinusPosition2559 batchN05121MinusPosition2559
  else 0


def batchC05120MinusFourthP000Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP000Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP000Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP000ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP000Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05120MinusFourthP000Upper2559 : ℝ := (((16 * 10^40
        + 8385532545953607545850732697571780453127) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120MinusFourthP000Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP000ExpBound2559 :
    Real.exp batchC05120MinusFourthP000Exponent2559 ≤ batchC05120MinusFourthP000ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP000Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP000Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP000Input2559 5).1 =
      batchC05120MinusFourthP000Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP000Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP000Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP000Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP000Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP000Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP000Input2559 =
      (batchC05120MinusFourthP000Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP000Input2559,
        batchC05120MinusFourthP000Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP000Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP000Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP000Center2559))).trans
  norm_num [batchC05120MinusFourthP000Error2559, batchC05120MinusFourthP000ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP000Center2559]

theorem batchC05120MinusFourthP000Bound2559 : batchC05120MinusFourthCell2559 ⟨0, by omega⟩ ≤
    batchC05120MinusFourthP000Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨0, by omega⟩)‖ ≤
      batchC05120MinusFourthP000Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP000Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP000Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    ((12980742146337070512478121581609 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5070602400912918168936766242816015625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP000ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP000Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨0, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
        ((12980742146337070512478121581609 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5070602400912918168936766242816015625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP000ExpUpper2559, batchC05120MinusFourthP000Frequency2559,
        batchC05120MinusFourthP000Upper2559]

def batchC05120MinusFourthP001Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP001Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP001Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP001ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP001Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05120MinusFourthP001Upper2559 : ℝ := (((33 * 10^40
        + 1621169247851613800965393103780832678891) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120MinusFourthP001Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP001ExpBound2559 :
    Real.exp batchC05120MinusFourthP001Exponent2559 ≤ batchC05120MinusFourthP001ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP001Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP001Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP001Input2559 5).1 =
      batchC05120MinusFourthP001Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP001Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP001Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP001Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP001Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP001Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP001Input2559 =
      (batchC05120MinusFourthP001Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP001Input2559,
        batchC05120MinusFourthP001Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP001Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP001Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP001Center2559))).trans
  norm_num [batchC05120MinusFourthP001Error2559, batchC05120MinusFourthP001ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP001Center2559]

theorem batchC05120MinusFourthP001Bound2559 : batchC05120MinusFourthCell2559 ⟨1, by omega⟩ ≤
    batchC05120MinusFourthP001Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      batchC05120MinusFourthP001Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP001Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP001Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) (0 : ℝ) ((39614081861595078604086562521088 : ℝ) /
        104779244925114570282650713456640625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP001ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP001Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) (0 : ℝ) ((39614081861595078604086562521088 : ℝ) /
        104779244925114570282650713456640625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP001ExpUpper2559, batchC05120MinusFourthP001Frequency2559,
        batchC05120MinusFourthP001Upper2559]

def batchC05120MinusFourthP002Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP002Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP002Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP002ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP002Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05120MinusFourthP002Upper2559 : ℝ := (((32 * 10^40
        + 8961581366567523392108107584023530070545) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120MinusFourthP002Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP002ExpBound2559 :
    Real.exp batchC05120MinusFourthP002Exponent2559 ≤ batchC05120MinusFourthP002ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP002Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP002Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP002Input2559 5).1 =
      batchC05120MinusFourthP002Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP002Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP002Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP002Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP002Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP002Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP002Input2559 =
      (batchC05120MinusFourthP002Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP002Input2559,
        batchC05120MinusFourthP002Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP002Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP002Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP002Center2559))).trans
  norm_num [batchC05120MinusFourthP002Error2559, batchC05120MinusFourthP002ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP002Center2559]

theorem batchC05120MinusFourthP002Bound2559 : batchC05120MinusFourthCell2559 ⟨2, by omega⟩ ≤
    batchC05120MinusFourthP002Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      batchC05120MinusFourthP002Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP002Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP002Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        535582378596426958724104076656640625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP002ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP002Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        535582378596426958724104076656640625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP002ExpUpper2559, batchC05120MinusFourthP002Frequency2559,
        batchC05120MinusFourthP002Upper2559]

def batchC05120MinusFourthP003Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP003Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP003Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP003ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP003Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05120MinusFourthP003Upper2559 : ℝ := (((32 * 10^40
        + 7476280563014223513882974463551520267563) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120MinusFourthP003Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP003ExpBound2559 :
    Real.exp batchC05120MinusFourthP003Exponent2559 ≤ batchC05120MinusFourthP003ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP003Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP003Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP003Input2559 5).1 =
      batchC05120MinusFourthP003Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP003Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP003Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP003Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP003Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP003Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP003Input2559 =
      (batchC05120MinusFourthP003Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP003Input2559,
        batchC05120MinusFourthP003Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP003Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP003Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP003Center2559))).trans
  norm_num [batchC05120MinusFourthP003Error2559, batchC05120MinusFourthP003ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP003Center2559]

theorem batchC05120MinusFourthP003Bound2559 : batchC05120MinusFourthCell2559 ⟨3, by omega⟩ ≤
    batchC05120MinusFourthP003Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      batchC05120MinusFourthP003Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP003Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP003Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP003ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP003Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP003ExpUpper2559, batchC05120MinusFourthP003Frequency2559,
        batchC05120MinusFourthP003Upper2559]

def batchC05120MinusFourthP004Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP004Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP004Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP004ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP004Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05120MinusFourthP004Upper2559 : ℝ := (((32 * 10^40
        + 6594234811174218890457509768495468177871) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120MinusFourthP004Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP004ExpBound2559 :
    Real.exp batchC05120MinusFourthP004Exponent2559 ≤ batchC05120MinusFourthP004ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP004Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP004Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP004Input2559 5).1 =
      batchC05120MinusFourthP004Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP004Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP004Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP004Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP004Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP004Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP004Input2559 =
      (batchC05120MinusFourthP004Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP004Input2559,
        batchC05120MinusFourthP004Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP004Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP004Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP004Center2559))).trans
  norm_num [batchC05120MinusFourthP004Error2559, batchC05120MinusFourthP004ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP004Center2559]

theorem batchC05120MinusFourthP004Bound2559 : batchC05120MinusFourthCell2559 ⟨4, by omega⟩ ≤
    batchC05120MinusFourthP004Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      batchC05120MinusFourthP004Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP004Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP004Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        811296384146067132209863967375390625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP004ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP004Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        811296384146067132209863967375390625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP004ExpUpper2559, batchC05120MinusFourthP004Frequency2559,
        batchC05120MinusFourthP004Upper2559]

def batchC05120MinusFourthP005Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP005Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP005Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP005ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP005Frequency2559 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC05120MinusFourthP005Upper2559 : ℝ :=
    ((2916879604232232297564820528127523461 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC05120MinusFourthP005Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP005ExpBound2559 :
    Real.exp batchC05120MinusFourthP005Exponent2559 ≤ batchC05120MinusFourthP005ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP005Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP005Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP005Input2559 5).1 =
      batchC05120MinusFourthP005Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP005Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP005Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP005Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP005Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP005Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP005Input2559 =
      (batchC05120MinusFourthP005Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP005Input2559,
        batchC05120MinusFourthP005Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP005Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP005Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP005Center2559))).trans
  norm_num [batchC05120MinusFourthP005Error2559, batchC05120MinusFourthP005ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP005Center2559]

theorem batchC05120MinusFourthP005Bound2559 : batchC05120MinusFourthCell2559 ⟨5, by omega⟩ ≤
    batchC05120MinusFourthP005Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨5, by omega⟩)‖ ≤
      batchC05120MinusFourthP005Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP005Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP005Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    ((14311268216336621374914235141089 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5590339147006492724575873101987890625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP005ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP005Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨5, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
        ((14311268216336621374914235141089 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5590339147006492724575873101987890625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP005ExpUpper2559, batchC05120MinusFourthP005Frequency2559,
        batchC05120MinusFourthP005Upper2559]

def batchC05120MinusFourthP006Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP006Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP006Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP006ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP006Frequency2559 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC05120MinusFourthP006Upper2559 : ℝ :=
    ((6177006966271344294564419883343040157 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120MinusFourthP006Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP006ExpBound2559 :
    Real.exp batchC05120MinusFourthP006Exponent2559 ≤ batchC05120MinusFourthP006ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP006Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP006Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP006Input2559 5).1 =
      batchC05120MinusFourthP006Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP006Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP006Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP006Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP006Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP006Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP006Input2559 =
      (batchC05120MinusFourthP006Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP006Input2559,
        batchC05120MinusFourthP006Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP006Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP006Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP006Center2559))).trans
  norm_num [batchC05120MinusFourthP006Error2559, batchC05120MinusFourthP006ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP006Center2559]

theorem batchC05120MinusFourthP006Bound2559 : batchC05120MinusFourthCell2559 ⟨6, by omega⟩ ≤
    batchC05120MinusFourthP006Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      batchC05120MinusFourthP006Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP006Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP006Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) (0 : ℝ) ((65536001 : ℝ) /
        204800000000) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP006ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP006Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) (0 : ℝ) ((65536001 : ℝ) /
        204800000000) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP006ExpUpper2559, batchC05120MinusFourthP006Frequency2559,
        batchC05120MinusFourthP006Upper2559]

def batchC05120MinusFourthP007Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP007Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP007Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP007ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP007Frequency2559 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC05120MinusFourthP007Upper2559 : ℝ :=
    ((1040187796349691280434068961427336963 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120MinusFourthP007Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP007ExpBound2559 :
    Real.exp batchC05120MinusFourthP007Exponent2559 ≤ batchC05120MinusFourthP007ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP007Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP007Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP007Input2559 5).1 =
      batchC05120MinusFourthP007Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP007Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP007Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP007Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP007Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP007Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP007Input2559 =
      (batchC05120MinusFourthP007Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP007Input2559,
        batchC05120MinusFourthP007Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP007Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP007Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP007Center2559))).trans
  norm_num [batchC05120MinusFourthP007Error2559, batchC05120MinusFourthP007ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP007Center2559]

theorem batchC05120MinusFourthP007Bound2559 : batchC05120MinusFourthCell2559 ⟨7, by omega⟩ ≤
    batchC05120MinusFourthP007Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      batchC05120MinusFourthP007Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP007Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP007Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP007ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP007Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP007ExpUpper2559, batchC05120MinusFourthP007Frequency2559,
        batchC05120MinusFourthP007Upper2559]

def batchC05120MinusFourthP008Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP008Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP008Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP008ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP008Frequency2559 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def batchC05120MinusFourthP008Upper2559 : ℝ :=
    ((6527584631450509079669555237816951044509 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120MinusFourthP008Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP008ExpBound2559 :
    Real.exp batchC05120MinusFourthP008Exponent2559 ≤ batchC05120MinusFourthP008ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP008Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP008Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP008Input2559 5).1 =
      batchC05120MinusFourthP008Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP008Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP008Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP008Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP008Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP008Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP008Input2559 =
      (batchC05120MinusFourthP008Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP008Input2559,
        batchC05120MinusFourthP008Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP008Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP008Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP008Center2559))).trans
  norm_num [batchC05120MinusFourthP008Error2559, batchC05120MinusFourthP008ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP008Center2559]

theorem batchC05120MinusFourthP008Bound2559 : batchC05120MinusFourthCell2559 ⟨8, by omega⟩ ≤
    batchC05120MinusFourthP008Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      batchC05120MinusFourthP008Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP008Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP008Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP008ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP008Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP008ExpUpper2559, batchC05120MinusFourthP008Frequency2559,
        batchC05120MinusFourthP008Upper2559]

def batchC05120MinusFourthP009Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP009Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP009Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP009ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP009Frequency2559 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def batchC05120MinusFourthP009Upper2559 : ℝ := (((1 * 10^40
        + 4532919290138169958700958438267627073095) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120MinusFourthP009Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP009ExpBound2559 :
    Real.exp batchC05120MinusFourthP009Exponent2559 ≤ batchC05120MinusFourthP009ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP009Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP009Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP009Input2559 5).1 =
      batchC05120MinusFourthP009Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP009Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP009Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP009Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP009Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP009Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP009Input2559 =
      (batchC05120MinusFourthP009Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP009Input2559,
        batchC05120MinusFourthP009Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP009Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP009Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP009Center2559))).trans
  norm_num [batchC05120MinusFourthP009Error2559, batchC05120MinusFourthP009ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP009Center2559]

theorem batchC05120MinusFourthP009Bound2559 : batchC05120MinusFourthCell2559 ⟨9, by omega⟩ ≤
    batchC05120MinusFourthP009Upper2559 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      batchC05120MinusFourthP009Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP009Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP009Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP009ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP009Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP009ExpUpper2559, batchC05120MinusFourthP009Frequency2559,
        batchC05120MinusFourthP009Upper2559]

def batchC05120MinusFourthP010Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP010Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP010Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP010ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP010Frequency2559 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def batchC05120MinusFourthP010Upper2559 : ℝ := (((5 * 10^40
        + 6854755398512847151884572989396243825841) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120MinusFourthP010Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP010ExpBound2559 :
    Real.exp batchC05120MinusFourthP010Exponent2559 ≤ batchC05120MinusFourthP010ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP010Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP010Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP010Input2559 5).1 =
      batchC05120MinusFourthP010Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP010Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP010Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP010Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP010Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP010Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP010Input2559 =
      (batchC05120MinusFourthP010Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP010Input2559,
        batchC05120MinusFourthP010Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP010Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP010Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP010Center2559))).trans
  norm_num [batchC05120MinusFourthP010Error2559, batchC05120MinusFourthP010ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP010Center2559]

theorem batchC05120MinusFourthP010Bound2559 : batchC05120MinusFourthCell2559 ⟨10, by omega⟩ ≤
    batchC05120MinusFourthP010Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      batchC05120MinusFourthP010Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP010Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP010Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP010ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP010Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP010ExpUpper2559, batchC05120MinusFourthP010Frequency2559,
        batchC05120MinusFourthP010Upper2559]

def batchC05120MinusFourthP011Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP011Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP011Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP011ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP011Frequency2559 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def batchC05120MinusFourthP011Upper2559 : ℝ := (((8 * 10^40
        + 4264068000940250849243123338024083715475) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120MinusFourthP011Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP011ExpBound2559 :
    Real.exp batchC05120MinusFourthP011Exponent2559 ≤ batchC05120MinusFourthP011ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP011Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP011Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP011Input2559 5).1 =
      batchC05120MinusFourthP011Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP011Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP011Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP011Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP011Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP011Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP011Input2559 =
      (batchC05120MinusFourthP011Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP011Input2559,
        batchC05120MinusFourthP011Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP011Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP011Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP011Center2559))).trans
  norm_num [batchC05120MinusFourthP011Error2559, batchC05120MinusFourthP011ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP011Center2559]

theorem batchC05120MinusFourthP011Bound2559 : batchC05120MinusFourthCell2559 ⟨11, by omega⟩ ≤
    batchC05120MinusFourthP011Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      batchC05120MinusFourthP011Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP011Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP011Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP011ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP011Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP011ExpUpper2559, batchC05120MinusFourthP011Frequency2559,
        batchC05120MinusFourthP011Upper2559]

def batchC05120MinusFourthP012Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP012Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP012Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP012ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP012Frequency2559 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def batchC05120MinusFourthP012Upper2559 : ℝ := (((3 * 10^40
        + 535571130850628447861799889660599514677) : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC05120MinusFourthP012Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP012ExpBound2559 :
    Real.exp batchC05120MinusFourthP012Exponent2559 ≤ batchC05120MinusFourthP012ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP012Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP012Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP012Input2559 5).1 =
      batchC05120MinusFourthP012Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP012Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP012Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP012Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP012Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP012Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP012Input2559 =
      (batchC05120MinusFourthP012Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP012Input2559,
        batchC05120MinusFourthP012Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP012Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP012Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP012Center2559))).trans
  norm_num [batchC05120MinusFourthP012Error2559, batchC05120MinusFourthP012ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP012Center2559]

theorem batchC05120MinusFourthP012Bound2559 : batchC05120MinusFourthCell2559 ⟨12, by omega⟩ ≤
    batchC05120MinusFourthP012Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      batchC05120MinusFourthP012Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP012Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP012Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP012ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP012Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP012ExpUpper2559, batchC05120MinusFourthP012Frequency2559,
        batchC05120MinusFourthP012Upper2559]

def batchC05120MinusFourthP013Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP013Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP013Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP013ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP013Frequency2559 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def batchC05120MinusFourthP013Upper2559 : ℝ := (((16 * 10^40
        + 6731207394916502677155202593498759531867) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120MinusFourthP013Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP013ExpBound2559 :
    Real.exp batchC05120MinusFourthP013Exponent2559 ≤ batchC05120MinusFourthP013ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP013Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP013Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP013Input2559 5).1 =
      batchC05120MinusFourthP013Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP013Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP013Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP013Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP013Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP013Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP013Input2559 =
      (batchC05120MinusFourthP013Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP013Input2559,
        batchC05120MinusFourthP013Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP013Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP013Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP013Center2559))).trans
  norm_num [batchC05120MinusFourthP013Error2559, batchC05120MinusFourthP013ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP013Center2559]

theorem batchC05120MinusFourthP013Bound2559 : batchC05120MinusFourthCell2559 ⟨13, by omega⟩ ≤
    batchC05120MinusFourthP013Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      batchC05120MinusFourthP013Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP013Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP013Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP013ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP013Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP013ExpUpper2559, batchC05120MinusFourthP013Frequency2559,
        batchC05120MinusFourthP013Upper2559]

def batchC05120MinusFourthP014Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP014Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP014Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP014ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP014Frequency2559 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def batchC05120MinusFourthP014Upper2559 : ℝ := (((1 * 10^40
        + 7533986978043259883414355931548925070063) : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC05120MinusFourthP014Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP014ExpBound2559 :
    Real.exp batchC05120MinusFourthP014Exponent2559 ≤ batchC05120MinusFourthP014ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP014Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP014Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP014Input2559 5).1 =
      batchC05120MinusFourthP014Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP014Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP014Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP014Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP014Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP014Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP014Input2559 =
      (batchC05120MinusFourthP014Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP014Input2559,
        batchC05120MinusFourthP014Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP014Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP014Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP014Center2559))).trans
  norm_num [batchC05120MinusFourthP014Error2559, batchC05120MinusFourthP014ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP014Center2559]

theorem batchC05120MinusFourthP014Bound2559 : batchC05120MinusFourthCell2559 ⟨14, by omega⟩ ≤
    batchC05120MinusFourthP014Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      batchC05120MinusFourthP014Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP014Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP014Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP014ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP014Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP014ExpUpper2559, batchC05120MinusFourthP014Frequency2559,
        batchC05120MinusFourthP014Upper2559]

def batchC05120MinusFourthP015Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP015Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP015Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP015ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP015Frequency2559 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def batchC05120MinusFourthP015Upper2559 : ℝ := (((19 * 10^40
        + 6213064106049384571348106147600088646179) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120MinusFourthP015Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP015ExpBound2559 :
    Real.exp batchC05120MinusFourthP015Exponent2559 ≤ batchC05120MinusFourthP015ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP015Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP015Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP015Input2559 5).1 =
      batchC05120MinusFourthP015Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP015Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP015Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP015Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP015Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP015Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP015Input2559 =
      (batchC05120MinusFourthP015Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP015Input2559,
        batchC05120MinusFourthP015Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP015Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP015Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP015Center2559))).trans
  norm_num [batchC05120MinusFourthP015Error2559, batchC05120MinusFourthP015ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP015Center2559]

theorem batchC05120MinusFourthP015Bound2559 : batchC05120MinusFourthCell2559 ⟨15, by omega⟩ ≤
    batchC05120MinusFourthP015Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      batchC05120MinusFourthP015Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP015Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP015Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP015ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP015Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP015ExpUpper2559, batchC05120MinusFourthP015Frequency2559,
        batchC05120MinusFourthP015Upper2559]

def batchC05120MinusFourthP016Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP016Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP016Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP016ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP016Frequency2559 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def batchC05120MinusFourthP016Upper2559 : ℝ := (((24 * 10^40
        + 6043491993595325237169992733866581212045) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120MinusFourthP016Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP016ExpBound2559 :
    Real.exp batchC05120MinusFourthP016Exponent2559 ≤ batchC05120MinusFourthP016ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP016Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP016Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP016Input2559 5).1 =
      batchC05120MinusFourthP016Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP016Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP016Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP016Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP016Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP016Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP016Input2559 =
      (batchC05120MinusFourthP016Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP016Input2559,
        batchC05120MinusFourthP016Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP016Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP016Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP016Center2559))).trans
  norm_num [batchC05120MinusFourthP016Error2559, batchC05120MinusFourthP016ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP016Center2559]

theorem batchC05120MinusFourthP016Bound2559 : batchC05120MinusFourthCell2559 ⟨16, by omega⟩ ≤
    batchC05120MinusFourthP016Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      batchC05120MinusFourthP016Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP016Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP016Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP016ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP016Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP016ExpUpper2559, batchC05120MinusFourthP016Frequency2559,
        batchC05120MinusFourthP016Upper2559]

def batchC05120MinusFourthP017Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP017Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP017Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP017ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP017Frequency2559 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def batchC05120MinusFourthP017Upper2559 : ℝ := (((73 * 10^40
        + 8787149174070767376412930778400914863545) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120MinusFourthP017Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP017ExpBound2559 :
    Real.exp batchC05120MinusFourthP017Exponent2559 ≤ batchC05120MinusFourthP017ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP017Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP017Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP017Input2559 5).1 =
      batchC05120MinusFourthP017Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP017Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP017Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP017Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP017Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP017Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP017Input2559 =
      (batchC05120MinusFourthP017Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP017Input2559,
        batchC05120MinusFourthP017Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP017Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP017Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP017Center2559))).trans
  norm_num [batchC05120MinusFourthP017Error2559, batchC05120MinusFourthP017ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP017Center2559]

theorem batchC05120MinusFourthP017Bound2559 : batchC05120MinusFourthCell2559 ⟨17, by omega⟩ ≤
    batchC05120MinusFourthP017Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      batchC05120MinusFourthP017Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP017Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP017Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP017ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP017Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP017ExpUpper2559, batchC05120MinusFourthP017Frequency2559,
        batchC05120MinusFourthP017Upper2559]

def batchC05120MinusFourthP018Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP018Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP018Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP018ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP018Frequency2559 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def batchC05120MinusFourthP018Upper2559 : ℝ := (((21 * 10^40
        + 3210545787404254096747270019293503496131) : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC05120MinusFourthP018Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP018ExpBound2559 :
    Real.exp batchC05120MinusFourthP018Exponent2559 ≤ batchC05120MinusFourthP018ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP018Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP018Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP018Input2559 5).1 =
      batchC05120MinusFourthP018Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP018Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP018Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP018Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP018Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP018Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP018Input2559 =
      (batchC05120MinusFourthP018Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP018Input2559,
        batchC05120MinusFourthP018Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP018Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP018Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP018Center2559))).trans
  norm_num [batchC05120MinusFourthP018Error2559, batchC05120MinusFourthP018ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP018Center2559]

theorem batchC05120MinusFourthP018Bound2559 : batchC05120MinusFourthCell2559 ⟨18, by omega⟩ ≤
    batchC05120MinusFourthP018Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      batchC05120MinusFourthP018Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP018Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP018Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP018ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP018Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP018ExpUpper2559, batchC05120MinusFourthP018Frequency2559,
        batchC05120MinusFourthP018Upper2559]

def batchC05120MinusFourthP019Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP019Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP019Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP019ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP019Frequency2559 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def batchC05120MinusFourthP019Upper2559 : ℝ := (((54 * 10^40
        + 5980972189274347546421330201154234157627) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120MinusFourthP019Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP019ExpBound2559 :
    Real.exp batchC05120MinusFourthP019Exponent2559 ≤ batchC05120MinusFourthP019ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP019Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP019Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP019Input2559 5).1 =
      batchC05120MinusFourthP019Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP019Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP019Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP019Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP019Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP019Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP019Input2559 =
      (batchC05120MinusFourthP019Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP019Input2559,
        batchC05120MinusFourthP019Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP019Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP019Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP019Center2559))).trans
  norm_num [batchC05120MinusFourthP019Error2559, batchC05120MinusFourthP019ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP019Center2559]

theorem batchC05120MinusFourthP019Bound2559 : batchC05120MinusFourthCell2559 ⟨19, by omega⟩ ≤
    batchC05120MinusFourthP019Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      batchC05120MinusFourthP019Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP019Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP019Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP019ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP019Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP019ExpUpper2559, batchC05120MinusFourthP019Frequency2559,
        batchC05120MinusFourthP019Upper2559]

def batchC05120MinusFourthP020Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP020Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP020Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP020ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP020Frequency2559 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def batchC05120MinusFourthP020Upper2559 : ℝ := (((140 * 10^40
        + 5744837887774056323750653200767926016331) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120MinusFourthP020Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP020ExpBound2559 :
    Real.exp batchC05120MinusFourthP020Exponent2559 ≤ batchC05120MinusFourthP020ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP020Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP020Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP020Input2559 5).1 =
      batchC05120MinusFourthP020Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP020Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP020Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP020Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP020Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP020Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP020Input2559 =
      (batchC05120MinusFourthP020Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP020Input2559,
        batchC05120MinusFourthP020Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP020Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP020Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP020Center2559))).trans
  norm_num [batchC05120MinusFourthP020Error2559, batchC05120MinusFourthP020ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP020Center2559]

theorem batchC05120MinusFourthP020Bound2559 : batchC05120MinusFourthCell2559 ⟨20, by omega⟩ ≤
    batchC05120MinusFourthP020Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      batchC05120MinusFourthP020Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP020Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP020Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP020ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP020Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP020ExpUpper2559, batchC05120MinusFourthP020Frequency2559,
        batchC05120MinusFourthP020Upper2559]

def batchC05120MinusFourthP021Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP021Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP021Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP021ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP021Frequency2559 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def batchC05120MinusFourthP021Upper2559 : ℝ := (((85 * 10^40
        + 7889128062175082199079910727357873178413) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120MinusFourthP021Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP021ExpBound2559 :
    Real.exp batchC05120MinusFourthP021Exponent2559 ≤ batchC05120MinusFourthP021ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP021Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP021Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP021Input2559 5).1 =
      batchC05120MinusFourthP021Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP021Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP021Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP021Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP021Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP021Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP021Input2559 =
      (batchC05120MinusFourthP021Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP021Input2559,
        batchC05120MinusFourthP021Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP021Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP021Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP021Center2559))).trans
  norm_num [batchC05120MinusFourthP021Error2559, batchC05120MinusFourthP021ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP021Center2559]

theorem batchC05120MinusFourthP021Bound2559 : batchC05120MinusFourthCell2559 ⟨21, by omega⟩ ≤
    batchC05120MinusFourthP021Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      batchC05120MinusFourthP021Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP021Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP021Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP021ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP021Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP021ExpUpper2559, batchC05120MinusFourthP021Frequency2559,
        batchC05120MinusFourthP021Upper2559]

def batchC05120MinusFourthP022Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP022Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP022Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP022ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP022Frequency2559 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def batchC05120MinusFourthP022Upper2559 : ℝ := (((189 * 10^40
        + 3028468361547082913484636570055890250493) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120MinusFourthP022Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP022ExpBound2559 :
    Real.exp batchC05120MinusFourthP022Exponent2559 ≤ batchC05120MinusFourthP022ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP022Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP022Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP022Input2559 5).1 =
      batchC05120MinusFourthP022Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP022Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP022Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP022Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP022Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP022Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP022Input2559 =
      (batchC05120MinusFourthP022Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP022Input2559,
        batchC05120MinusFourthP022Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP022Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP022Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP022Center2559))).trans
  norm_num [batchC05120MinusFourthP022Error2559, batchC05120MinusFourthP022ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP022Center2559]

theorem batchC05120MinusFourthP022Bound2559 : batchC05120MinusFourthCell2559 ⟨22, by omega⟩ ≤
    batchC05120MinusFourthP022Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      batchC05120MinusFourthP022Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP022Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP022Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP022ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP022Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP022ExpUpper2559, batchC05120MinusFourthP022Frequency2559,
        batchC05120MinusFourthP022Upper2559]

def batchC05120MinusFourthP023Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP023Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP023Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP023ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP023Frequency2559 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def batchC05120MinusFourthP023Upper2559 : ℝ := (((124 * 10^40
        + 755089048066799983132593836264199659491) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120MinusFourthP023Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP023ExpBound2559 :
    Real.exp batchC05120MinusFourthP023Exponent2559 ≤ batchC05120MinusFourthP023ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP023Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP023Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP023Input2559 5).1 =
      batchC05120MinusFourthP023Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP023Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP023Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP023Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP023Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP023Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP023Input2559 =
      (batchC05120MinusFourthP023Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP023Input2559,
        batchC05120MinusFourthP023Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP023Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP023Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP023Center2559))).trans
  norm_num [batchC05120MinusFourthP023Error2559, batchC05120MinusFourthP023ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP023Center2559]

theorem batchC05120MinusFourthP023Bound2559 : batchC05120MinusFourthCell2559 ⟨23, by omega⟩ ≤
    batchC05120MinusFourthP023Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      batchC05120MinusFourthP023Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP023Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP023Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP023ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP023Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP023ExpUpper2559, batchC05120MinusFourthP023Frequency2559,
        batchC05120MinusFourthP023Upper2559]

def batchC05120MinusFourthP024Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP024Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP024Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP024ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP024Frequency2559 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def batchC05120MinusFourthP024Upper2559 : ℝ := (((139 * 10^40
        + 6899246218794912147576920088019173674939) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120MinusFourthP024Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP024ExpBound2559 :
    Real.exp batchC05120MinusFourthP024Exponent2559 ≤ batchC05120MinusFourthP024ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP024Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP024Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP024Input2559 5).1 =
      batchC05120MinusFourthP024Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP024Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP024Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP024Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP024Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP024Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP024Input2559 =
      (batchC05120MinusFourthP024Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP024Input2559,
        batchC05120MinusFourthP024Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP024Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP024Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP024Center2559))).trans
  norm_num [batchC05120MinusFourthP024Error2559, batchC05120MinusFourthP024ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP024Center2559]

theorem batchC05120MinusFourthP024Bound2559 : batchC05120MinusFourthCell2559 ⟨24, by omega⟩ ≤
    batchC05120MinusFourthP024Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      batchC05120MinusFourthP024Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP024Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP024Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP024ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP024Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP024ExpUpper2559, batchC05120MinusFourthP024Frequency2559,
        batchC05120MinusFourthP024Upper2559]

def batchC05120MinusFourthP025Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP025Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP025Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP025ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP025Frequency2559 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def batchC05120MinusFourthP025Upper2559 : ℝ := (((40 * 10^40
        + 3250804032679059151191230319052096355583) : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC05120MinusFourthP025Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP025ExpBound2559 :
    Real.exp batchC05120MinusFourthP025Exponent2559 ≤ batchC05120MinusFourthP025ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP025Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP025Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP025Input2559 5).1 =
      batchC05120MinusFourthP025Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP025Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP025Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP025Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP025Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP025Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP025Input2559 =
      (batchC05120MinusFourthP025Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP025Input2559,
        batchC05120MinusFourthP025Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP025Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP025Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP025Center2559))).trans
  norm_num [batchC05120MinusFourthP025Error2559, batchC05120MinusFourthP025ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP025Center2559]

theorem batchC05120MinusFourthP025Bound2559 : batchC05120MinusFourthCell2559 ⟨25, by omega⟩ ≤
    batchC05120MinusFourthP025Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      batchC05120MinusFourthP025Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP025Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP025Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP025ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP025Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP025ExpUpper2559, batchC05120MinusFourthP025Frequency2559,
        batchC05120MinusFourthP025Upper2559]

def batchC05120MinusFourthP026Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP026Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP026Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP026ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP026Frequency2559 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def batchC05120MinusFourthP026Upper2559 : ℝ := (((371 * 10^40
        + 7714855670662988155578528403584661985395) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120MinusFourthP026Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP026ExpBound2559 :
    Real.exp batchC05120MinusFourthP026Exponent2559 ≤ batchC05120MinusFourthP026ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP026Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP026Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP026Input2559 5).1 =
      batchC05120MinusFourthP026Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP026Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP026Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP026Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP026Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP026Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP026Input2559 =
      (batchC05120MinusFourthP026Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP026Input2559,
        batchC05120MinusFourthP026Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP026Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP026Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP026Center2559))).trans
  norm_num [batchC05120MinusFourthP026Error2559, batchC05120MinusFourthP026ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP026Center2559]

theorem batchC05120MinusFourthP026Bound2559 : batchC05120MinusFourthCell2559 ⟨26, by omega⟩ ≤
    batchC05120MinusFourthP026Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      batchC05120MinusFourthP026Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP026Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP026Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP026ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP026Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP026ExpUpper2559, batchC05120MinusFourthP026Frequency2559,
        batchC05120MinusFourthP026Upper2559]

def batchC05120MinusFourthP027Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP027Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP027Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP027ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP027Frequency2559 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def batchC05120MinusFourthP027Upper2559 : ℝ := (((452 * 10^40
        + 3890128674599300327300588382308555792043) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05120MinusFourthP027Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP027ExpBound2559 :
    Real.exp batchC05120MinusFourthP027Exponent2559 ≤ batchC05120MinusFourthP027ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP027Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP027Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP027Input2559 5).1 =
      batchC05120MinusFourthP027Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP027Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP027Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP027Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP027Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP027Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP027Input2559 =
      (batchC05120MinusFourthP027Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP027Input2559,
        batchC05120MinusFourthP027Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP027Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP027Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP027Center2559))).trans
  norm_num [batchC05120MinusFourthP027Error2559, batchC05120MinusFourthP027ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP027Center2559]

theorem batchC05120MinusFourthP027Bound2559 : batchC05120MinusFourthCell2559 ⟨27, by omega⟩ ≤
    batchC05120MinusFourthP027Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      batchC05120MinusFourthP027Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP027Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP027Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP027ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP027Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP027ExpUpper2559, batchC05120MinusFourthP027Frequency2559,
        batchC05120MinusFourthP027Upper2559]

def batchC05120MinusFourthP028Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP028Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP028Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP028ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP028Frequency2559 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def batchC05120MinusFourthP028Upper2559 : ℝ := (((1 * 10^40
        + 9050179842530705405820839488291952256947) : ℝ) /
        (570899 * 10^40
        + 770823839524233143877797980545530986496))

noncomputable def batchC05120MinusFourthP028Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP028ExpBound2559 :
    Real.exp batchC05120MinusFourthP028Exponent2559 ≤ batchC05120MinusFourthP028ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP028Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP028Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP028Input2559 5).1 =
      batchC05120MinusFourthP028Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP028Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP028Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP028Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP028Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP028Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP028Input2559 =
      (batchC05120MinusFourthP028Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP028Input2559,
        batchC05120MinusFourthP028Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP028Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP028Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP028Center2559))).trans
  norm_num [batchC05120MinusFourthP028Error2559, batchC05120MinusFourthP028ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP028Center2559]

theorem batchC05120MinusFourthP028Bound2559 : batchC05120MinusFourthCell2559 ⟨28, by omega⟩ ≤
    batchC05120MinusFourthP028Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      batchC05120MinusFourthP028Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP028Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP028Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP028ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP028Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP028ExpUpper2559, batchC05120MinusFourthP028Frequency2559,
        batchC05120MinusFourthP028Upper2559]

def batchC05120MinusFourthP029Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05120MinusFourthP029Center2559 : RatPair2542 := (((136761812904851798033513937177447845
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusFourthP029Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP029ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05120MinusFourthP029Frequency2559 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def batchC05120MinusFourthP029Upper2559 : ℝ := (((272 * 10^40
        + 6700569434539071544678381115247579945815) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05120MinusFourthP029Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05120MinusFourthP029ExpBound2559 :
    Real.exp batchC05120MinusFourthP029Exponent2559 ≤ batchC05120MinusFourthP029ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05120MinusFourthP029Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusFourthP029Input2559]
  have hc : (compactExp2547 batchC05120MinusFourthP029Input2559 5).1 =
      batchC05120MinusFourthP029Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05120MinusFourthP029Input2559 5).2 : ℝ) =
      batchC05120MinusFourthP029Error2559 := by
    have hq : (compactExp2547 batchC05120MinusFourthP029Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05120MinusFourthP029Error2559]
  have h := compactExp_error2547 batchC05120MinusFourthP029Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05120MinusFourthP029Input2559 =
      (batchC05120MinusFourthP029Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05120MinusFourthP029Input2559,
        batchC05120MinusFourthP029Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05120MinusFourthP029Exponent2559 : ℂ)) (embedPair2542
        batchC05120MinusFourthP029Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05120MinusFourthP029Center2559))).trans
  norm_num [batchC05120MinusFourthP029Error2559, batchC05120MinusFourthP029ExpUpper2559,
      pairMagnitude2542,
      batchC05120MinusFourthP029Center2559]

theorem batchC05120MinusFourthP029Bound2559 : batchC05120MinusFourthCell2559 ⟨29, by omega⟩ ≤
    batchC05120MinusFourthP029Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      batchC05120MinusFourthP029Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05120MinusFourthP029Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05120MinusFourthP029Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC05120MinusFourthP029ExpBound2559 using 1; norm_num
        [batchC05120MinusFourthP029Exponent2559])
  have hid : batchC05120MinusFourthCell2559 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (0 : ℝ) ((65536001 : ℝ) /
        51200000000) := by
    norm_num [batchC05120MinusFourthCell2559, cellNearAbs2538, batchN05120MinusPosition2559,
      batchN05121MinusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05120MinusFourthP029ExpUpper2559, batchC05120MinusFourthP029Frequency2559,
        batchC05120MinusFourthP029Upper2559]

noncomputable def batchC05120MinusFourthUpper2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05120MinusFourthP000Upper2559
  | 1 => batchC05120MinusFourthP001Upper2559
  | 2 => batchC05120MinusFourthP002Upper2559
  | 3 => batchC05120MinusFourthP003Upper2559
  | 4 => batchC05120MinusFourthP004Upper2559
  | 5 => batchC05120MinusFourthP005Upper2559
  | 6 => batchC05120MinusFourthP006Upper2559
  | 7 => batchC05120MinusFourthP007Upper2559
  | 8 => batchC05120MinusFourthP008Upper2559
  | 9 => batchC05120MinusFourthP009Upper2559
  | 10 => batchC05120MinusFourthP010Upper2559
  | 11 => batchC05120MinusFourthP011Upper2559
  | 12 => batchC05120MinusFourthP012Upper2559
  | 13 => batchC05120MinusFourthP013Upper2559
  | 14 => batchC05120MinusFourthP014Upper2559
  | 15 => batchC05120MinusFourthP015Upper2559
  | 16 => batchC05120MinusFourthP016Upper2559
  | 17 => batchC05120MinusFourthP017Upper2559
  | 18 => batchC05120MinusFourthP018Upper2559
  | 19 => batchC05120MinusFourthP019Upper2559
  | 20 => batchC05120MinusFourthP020Upper2559
  | 21 => batchC05120MinusFourthP021Upper2559
  | 22 => batchC05120MinusFourthP022Upper2559
  | 23 => batchC05120MinusFourthP023Upper2559
  | 24 => batchC05120MinusFourthP024Upper2559
  | 25 => batchC05120MinusFourthP025Upper2559
  | 26 => batchC05120MinusFourthP026Upper2559
  | 27 => batchC05120MinusFourthP027Upper2559
  | 28 => batchC05120MinusFourthP028Upper2559
  | 29 => batchC05120MinusFourthP029Upper2559
  | _ => 0

theorem batchC05120MinusFourthBound2559 (i : Fin 30) :
    batchC05120MinusFourthCell2559 i ≤ batchC05120MinusFourthUpper2559 i := by
  fin_cases i
  · exact batchC05120MinusFourthP000Bound2559
  · exact batchC05120MinusFourthP001Bound2559
  · exact batchC05120MinusFourthP002Bound2559
  · exact batchC05120MinusFourthP003Bound2559
  · exact batchC05120MinusFourthP004Bound2559
  · exact batchC05120MinusFourthP005Bound2559
  · exact batchC05120MinusFourthP006Bound2559
  · exact batchC05120MinusFourthP007Bound2559
  · exact batchC05120MinusFourthP008Bound2559
  · exact batchC05120MinusFourthP009Bound2559
  · exact batchC05120MinusFourthP010Bound2559
  · exact batchC05120MinusFourthP011Bound2559
  · exact batchC05120MinusFourthP012Bound2559
  · exact batchC05120MinusFourthP013Bound2559
  · exact batchC05120MinusFourthP014Bound2559
  · exact batchC05120MinusFourthP015Bound2559
  · exact batchC05120MinusFourthP016Bound2559
  · exact batchC05120MinusFourthP017Bound2559
  · exact batchC05120MinusFourthP018Bound2559
  · exact batchC05120MinusFourthP019Bound2559
  · exact batchC05120MinusFourthP020Bound2559
  · exact batchC05120MinusFourthP021Bound2559
  · exact batchC05120MinusFourthP022Bound2559
  · exact batchC05120MinusFourthP023Bound2559
  · exact batchC05120MinusFourthP024Bound2559
  · exact batchC05120MinusFourthP025Bound2559
  · exact batchC05120MinusFourthP026Bound2559
  · exact batchC05120MinusFourthP027Bound2559
  · exact batchC05120MinusFourthP028Bound2559
  · exact batchC05120MinusFourthP029Bound2559

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP000Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP001Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP002Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP003Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP004Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP005Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP006Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP007Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP008Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP009Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP010Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP011Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP012Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP013Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP014Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP015Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP016Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP017Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP018Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP019Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP020Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP021Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP022Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP023Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP024Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP025Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP026Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP027Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP028Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthP029Bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusFourthBound2559
