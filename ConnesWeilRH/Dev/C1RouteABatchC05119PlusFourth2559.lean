import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteABatchN05119Plus2559
import ConnesWeilRH.Dev.C1RouteABatchN05120Plus2559

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC05119PlusFourthCell2559 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 batchN05119PlusPosition2559 batchN05120PlusPosition2559 < storedWidth i ^ 2
      then
    weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 batchN05119PlusPosition2559 batchN05120PlusPosition2559 / (storedWidth i ^
          2))
      (min (max |batchN05119PlusPosition2559| |batchN05120PlusPosition2559|) (storedWidth i ^ 2) /
        (storedWidth i ^ 2)) batchN05119PlusPosition2559 batchN05120PlusPosition2559
  else 0


def batchC05119PlusFourthP000Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP000Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP000Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP000ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP000Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05119PlusFourthP000Upper2559 : ℝ := (((16 * 10^40
        + 8385532545953607545850732697571780453127) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119PlusFourthP000Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP000ExpBound2559 :
    Real.exp batchC05119PlusFourthP000Exponent2559 ≤ batchC05119PlusFourthP000ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP000Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP000Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP000Input2559 5).1 =
      batchC05119PlusFourthP000Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP000Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP000Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP000Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP000Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP000Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP000Input2559 =
      (batchC05119PlusFourthP000Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP000Input2559,
        batchC05119PlusFourthP000Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP000Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP000Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP000Center2559))).trans
  norm_num [batchC05119PlusFourthP000Error2559, batchC05119PlusFourthP000ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP000Center2559]

theorem batchC05119PlusFourthP000Bound2559 : batchC05119PlusFourthCell2559 ⟨0, by omega⟩ ≤
    batchC05119PlusFourthP000Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨0, by omega⟩)‖ ≤
      batchC05119PlusFourthP000Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP000Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP000Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    ((12980742146337070512478121581609 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5070602400912918168936766242816015625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP000ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP000Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨0, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨0, by omega⟩)
        ((12980742146337070512478121581609 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5070602400912918168936766242816015625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP000ExpUpper2559, batchC05119PlusFourthP000Frequency2559,
        batchC05119PlusFourthP000Upper2559]

def batchC05119PlusFourthP001Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP001Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP001Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP001ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP001Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05119PlusFourthP001Upper2559 : ℝ := (((33 * 10^40
        + 1621169247851613800965393103780832678891) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119PlusFourthP001Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP001ExpBound2559 :
    Real.exp batchC05119PlusFourthP001Exponent2559 ≤ batchC05119PlusFourthP001ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP001Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP001Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP001Input2559 5).1 =
      batchC05119PlusFourthP001Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP001Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP001Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP001Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP001Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP001Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP001Input2559 =
      (batchC05119PlusFourthP001Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP001Input2559,
        batchC05119PlusFourthP001Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP001Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP001Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP001Center2559))).trans
  norm_num [batchC05119PlusFourthP001Error2559, batchC05119PlusFourthP001ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP001Center2559]

theorem batchC05119PlusFourthP001Bound2559 : batchC05119PlusFourthCell2559 ⟨1, by omega⟩ ≤
    batchC05119PlusFourthP001Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      batchC05119PlusFourthP001Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP001Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP001Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) (0 : ℝ) ((39614081861595078604086562521088 : ℝ) /
        104779244925114570282650713456640625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP001ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP001Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) (0 : ℝ) ((39614081861595078604086562521088 : ℝ) /
        104779244925114570282650713456640625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP001ExpUpper2559, batchC05119PlusFourthP001Frequency2559,
        batchC05119PlusFourthP001Upper2559]

def batchC05119PlusFourthP002Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP002Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP002Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP002ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP002Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05119PlusFourthP002Upper2559 : ℝ := (((32 * 10^40
        + 8961581366567523392108107584023530070545) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119PlusFourthP002Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP002ExpBound2559 :
    Real.exp batchC05119PlusFourthP002Exponent2559 ≤ batchC05119PlusFourthP002ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP002Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP002Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP002Input2559 5).1 =
      batchC05119PlusFourthP002Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP002Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP002Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP002Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP002Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP002Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP002Input2559 =
      (batchC05119PlusFourthP002Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP002Input2559,
        batchC05119PlusFourthP002Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP002Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP002Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP002Center2559))).trans
  norm_num [batchC05119PlusFourthP002Error2559, batchC05119PlusFourthP002ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP002Center2559]

theorem batchC05119PlusFourthP002Bound2559 : batchC05119PlusFourthCell2559 ⟨2, by omega⟩ ≤
    batchC05119PlusFourthP002Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      batchC05119PlusFourthP002Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP002Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP002Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        535582378596426958724104076656640625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP002ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP002Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        535582378596426958724104076656640625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP002ExpUpper2559, batchC05119PlusFourthP002Frequency2559,
        batchC05119PlusFourthP002Upper2559]

def batchC05119PlusFourthP003Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP003Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP003Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP003ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP003Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05119PlusFourthP003Upper2559 : ℝ := (((32 * 10^40
        + 7476280563014223513882974463551520267563) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119PlusFourthP003Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP003ExpBound2559 :
    Real.exp batchC05119PlusFourthP003Exponent2559 ≤ batchC05119PlusFourthP003ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP003Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP003Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP003Input2559 5).1 =
      batchC05119PlusFourthP003Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP003Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP003Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP003Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP003Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP003Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP003Input2559 =
      (batchC05119PlusFourthP003Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP003Input2559,
        batchC05119PlusFourthP003Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP003Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP003Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP003Center2559))).trans
  norm_num [batchC05119PlusFourthP003Error2559, batchC05119PlusFourthP003ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP003Center2559]

theorem batchC05119PlusFourthP003Bound2559 : batchC05119PlusFourthCell2559 ⟨3, by omega⟩ ≤
    batchC05119PlusFourthP003Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      batchC05119PlusFourthP003Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP003Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP003Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP003ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP003Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP003ExpUpper2559, batchC05119PlusFourthP003Frequency2559,
        batchC05119PlusFourthP003Upper2559]

def batchC05119PlusFourthP004Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP004Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP004Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP004ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP004Frequency2559 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC05119PlusFourthP004Upper2559 : ℝ := (((32 * 10^40
        + 6594234811174218890457509768495468177871) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119PlusFourthP004Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP004ExpBound2559 :
    Real.exp batchC05119PlusFourthP004Exponent2559 ≤ batchC05119PlusFourthP004ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP004Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP004Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP004Input2559 5).1 =
      batchC05119PlusFourthP004Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP004Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP004Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP004Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP004Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP004Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP004Input2559 =
      (batchC05119PlusFourthP004Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP004Input2559,
        batchC05119PlusFourthP004Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP004Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP004Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP004Center2559))).trans
  norm_num [batchC05119PlusFourthP004Error2559, batchC05119PlusFourthP004ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP004Center2559]

theorem batchC05119PlusFourthP004Bound2559 : batchC05119PlusFourthCell2559 ⟨4, by omega⟩ ≤
    batchC05119PlusFourthP004Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      batchC05119PlusFourthP004Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP004Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP004Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        811296384146067132209863967375390625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP004ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP004Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) (0 : ℝ) ((158456327446380314416346250084352 : ℝ) /
        811296384146067132209863967375390625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP004ExpUpper2559, batchC05119PlusFourthP004Frequency2559,
        batchC05119PlusFourthP004Upper2559]

def batchC05119PlusFourthP005Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP005Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP005Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP005ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP005Frequency2559 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC05119PlusFourthP005Upper2559 : ℝ :=
    ((2916879604232232297564820528127523461 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC05119PlusFourthP005Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP005ExpBound2559 :
    Real.exp batchC05119PlusFourthP005Exponent2559 ≤ batchC05119PlusFourthP005ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP005Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP005Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP005Input2559 5).1 =
      batchC05119PlusFourthP005Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP005Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP005Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP005Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP005Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP005Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP005Input2559 =
      (batchC05119PlusFourthP005Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP005Input2559,
        batchC05119PlusFourthP005Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP005Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP005Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP005Center2559))).trans
  norm_num [batchC05119PlusFourthP005Error2559, batchC05119PlusFourthP005ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP005Center2559]

theorem batchC05119PlusFourthP005Bound2559 : batchC05119PlusFourthCell2559 ⟨5, by omega⟩ ≤
    batchC05119PlusFourthP005Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨5, by omega⟩)‖ ≤
      batchC05119PlusFourthP005Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP005Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP005Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    ((14311268216336621374914235141089 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5590339147006492724575873101987890625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP005ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP005Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨5, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨5, by omega⟩)
        ((14311268216336621374914235141089 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        5590339147006492724575873101987890625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP005ExpUpper2559, batchC05119PlusFourthP005Frequency2559,
        batchC05119PlusFourthP005Upper2559]

def batchC05119PlusFourthP006Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP006Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP006Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP006ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP006Frequency2559 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC05119PlusFourthP006Upper2559 : ℝ :=
    ((6177006966271344294564419883343040157 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119PlusFourthP006Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP006ExpBound2559 :
    Real.exp batchC05119PlusFourthP006Exponent2559 ≤ batchC05119PlusFourthP006ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP006Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP006Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP006Input2559 5).1 =
      batchC05119PlusFourthP006Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP006Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP006Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP006Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP006Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP006Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP006Input2559 =
      (batchC05119PlusFourthP006Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP006Input2559,
        batchC05119PlusFourthP006Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP006Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP006Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP006Center2559))).trans
  norm_num [batchC05119PlusFourthP006Error2559, batchC05119PlusFourthP006ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP006Center2559]

theorem batchC05119PlusFourthP006Bound2559 : batchC05119PlusFourthCell2559 ⟨6, by omega⟩ ≤
    batchC05119PlusFourthP006Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      batchC05119PlusFourthP006Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP006Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP006Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) (0 : ℝ) ((65536001 : ℝ) /
        204800000000) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP006ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP006Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) (0 : ℝ) ((65536001 : ℝ) /
        204800000000) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP006ExpUpper2559, batchC05119PlusFourthP006Frequency2559,
        batchC05119PlusFourthP006Upper2559]

def batchC05119PlusFourthP007Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP007Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP007Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP007ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP007Frequency2559 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC05119PlusFourthP007Upper2559 : ℝ :=
    ((1040187796349691280434068961427336963 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119PlusFourthP007Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP007ExpBound2559 :
    Real.exp batchC05119PlusFourthP007Exponent2559 ≤ batchC05119PlusFourthP007ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP007Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP007Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP007Input2559 5).1 =
      batchC05119PlusFourthP007Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP007Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP007Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP007Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP007Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP007Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP007Input2559 =
      (batchC05119PlusFourthP007Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP007Input2559,
        batchC05119PlusFourthP007Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP007Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP007Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP007Center2559))).trans
  norm_num [batchC05119PlusFourthP007Error2559, batchC05119PlusFourthP007ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP007Center2559]

theorem batchC05119PlusFourthP007Bound2559 : batchC05119PlusFourthCell2559 ⟨7, by omega⟩ ≤
    batchC05119PlusFourthP007Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      batchC05119PlusFourthP007Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP007Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP007Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP007ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP007Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        10660941547919407797287895527587890625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP007ExpUpper2559, batchC05119PlusFourthP007Frequency2559,
        batchC05119PlusFourthP007Upper2559]

def batchC05119PlusFourthP008Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP008Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP008Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP008ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP008Frequency2559 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def batchC05119PlusFourthP008Upper2559 : ℝ :=
    ((6527584631450509079669555237816951044509 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119PlusFourthP008Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP008ExpBound2559 :
    Real.exp batchC05119PlusFourthP008Exponent2559 ≤ batchC05119PlusFourthP008ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP008Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP008Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP008Input2559 5).1 =
      batchC05119PlusFourthP008Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP008Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP008Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP008Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP008Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP008Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP008Input2559 =
      (batchC05119PlusFourthP008Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP008Input2559,
        batchC05119PlusFourthP008Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP008Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP008Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP008Center2559))).trans
  norm_num [batchC05119PlusFourthP008Error2559, batchC05119PlusFourthP008ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP008Center2559]

theorem batchC05119PlusFourthP008Bound2559 : batchC05119PlusFourthCell2559 ⟨8, by omega⟩ ≤
    batchC05119PlusFourthP008Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      batchC05119PlusFourthP008Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP008Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP008Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP008ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP008Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP008ExpUpper2559, batchC05119PlusFourthP008Frequency2559,
        batchC05119PlusFourthP008Upper2559]

def batchC05119PlusFourthP009Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP009Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP009Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP009ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP009Frequency2559 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def batchC05119PlusFourthP009Upper2559 : ℝ := (((1 * 10^40
        + 4532919290138169958700958438267627073095) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119PlusFourthP009Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP009ExpBound2559 :
    Real.exp batchC05119PlusFourthP009Exponent2559 ≤ batchC05119PlusFourthP009ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP009Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP009Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP009Input2559 5).1 =
      batchC05119PlusFourthP009Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP009Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP009Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP009Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP009Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP009Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP009Input2559 =
      (batchC05119PlusFourthP009Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP009Input2559,
        batchC05119PlusFourthP009Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP009Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP009Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP009Center2559))).trans
  norm_num [batchC05119PlusFourthP009Error2559, batchC05119PlusFourthP009ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP009Center2559]

theorem batchC05119PlusFourthP009Bound2559 : batchC05119PlusFourthCell2559 ⟨9, by omega⟩ ≤
    batchC05119PlusFourthP009Upper2559 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      batchC05119PlusFourthP009Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP009Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP009Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP009ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP009Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP009ExpUpper2559, batchC05119PlusFourthP009Frequency2559,
        batchC05119PlusFourthP009Upper2559]

def batchC05119PlusFourthP010Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP010Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP010Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP010ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP010Frequency2559 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def batchC05119PlusFourthP010Upper2559 : ℝ := (((5 * 10^40
        + 6854755398512847151884572989396243825841) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119PlusFourthP010Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP010ExpBound2559 :
    Real.exp batchC05119PlusFourthP010Exponent2559 ≤ batchC05119PlusFourthP010ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP010Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP010Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP010Input2559 5).1 =
      batchC05119PlusFourthP010Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP010Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP010Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP010Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP010Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP010Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP010Input2559 =
      (batchC05119PlusFourthP010Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP010Input2559,
        batchC05119PlusFourthP010Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP010Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP010Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP010Center2559))).trans
  norm_num [batchC05119PlusFourthP010Error2559, batchC05119PlusFourthP010ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP010Center2559]

theorem batchC05119PlusFourthP010Bound2559 : batchC05119PlusFourthCell2559 ⟨10, by omega⟩ ≤
    batchC05119PlusFourthP010Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      batchC05119PlusFourthP010Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP010Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP010Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP010ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP010Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP010ExpUpper2559, batchC05119PlusFourthP010Frequency2559,
        batchC05119PlusFourthP010Upper2559]

def batchC05119PlusFourthP011Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP011Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP011Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP011ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP011Frequency2559 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def batchC05119PlusFourthP011Upper2559 : ℝ := (((8 * 10^40
        + 4264068000940250849243123338024083715475) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119PlusFourthP011Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP011ExpBound2559 :
    Real.exp batchC05119PlusFourthP011Exponent2559 ≤ batchC05119PlusFourthP011ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP011Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP011Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP011Input2559 5).1 =
      batchC05119PlusFourthP011Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP011Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP011Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP011Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP011Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP011Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP011Input2559 =
      (batchC05119PlusFourthP011Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP011Input2559,
        batchC05119PlusFourthP011Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP011Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP011Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP011Center2559))).trans
  norm_num [batchC05119PlusFourthP011Error2559, batchC05119PlusFourthP011ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP011Center2559]

theorem batchC05119PlusFourthP011Bound2559 : batchC05119PlusFourthCell2559 ⟨11, by omega⟩ ≤
    batchC05119PlusFourthP011Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      batchC05119PlusFourthP011Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP011Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP011Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP011ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP011Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP011ExpUpper2559, batchC05119PlusFourthP011Frequency2559,
        batchC05119PlusFourthP011Upper2559]

def batchC05119PlusFourthP012Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP012Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP012Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP012ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP012Frequency2559 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def batchC05119PlusFourthP012Upper2559 : ℝ := (((3 * 10^40
        + 535571130850628447861799889660599514677) : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC05119PlusFourthP012Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP012ExpBound2559 :
    Real.exp batchC05119PlusFourthP012Exponent2559 ≤ batchC05119PlusFourthP012ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP012Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP012Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP012Input2559 5).1 =
      batchC05119PlusFourthP012Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP012Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP012Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP012Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP012Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP012Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP012Input2559 =
      (batchC05119PlusFourthP012Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP012Input2559,
        batchC05119PlusFourthP012Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP012Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP012Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP012Center2559))).trans
  norm_num [batchC05119PlusFourthP012Error2559, batchC05119PlusFourthP012ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP012Center2559]

theorem batchC05119PlusFourthP012Bound2559 : batchC05119PlusFourthCell2559 ⟨12, by omega⟩ ≤
    batchC05119PlusFourthP012Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      batchC05119PlusFourthP012Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP012Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP012Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP012ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP012Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP012ExpUpper2559, batchC05119PlusFourthP012Frequency2559,
        batchC05119PlusFourthP012Upper2559]

def batchC05119PlusFourthP013Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP013Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP013Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP013ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP013Frequency2559 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def batchC05119PlusFourthP013Upper2559 : ℝ := (((16 * 10^40
        + 6731207394916502677155202593498759531867) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119PlusFourthP013Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP013ExpBound2559 :
    Real.exp batchC05119PlusFourthP013Exponent2559 ≤ batchC05119PlusFourthP013ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP013Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP013Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP013Input2559 5).1 =
      batchC05119PlusFourthP013Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP013Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP013Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP013Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP013Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP013Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP013Input2559 =
      (batchC05119PlusFourthP013Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP013Input2559,
        batchC05119PlusFourthP013Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP013Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP013Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP013Center2559))).trans
  norm_num [batchC05119PlusFourthP013Error2559, batchC05119PlusFourthP013ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP013Center2559]

theorem batchC05119PlusFourthP013Bound2559 : batchC05119PlusFourthCell2559 ⟨13, by omega⟩ ≤
    batchC05119PlusFourthP013Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      batchC05119PlusFourthP013Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP013Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP013Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP013ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP013Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP013ExpUpper2559, batchC05119PlusFourthP013Frequency2559,
        batchC05119PlusFourthP013Upper2559]

def batchC05119PlusFourthP014Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP014Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP014Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP014ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP014Frequency2559 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def batchC05119PlusFourthP014Upper2559 : ℝ := (((1 * 10^40
        + 7533986978043259883414355931548925070063) : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC05119PlusFourthP014Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP014ExpBound2559 :
    Real.exp batchC05119PlusFourthP014Exponent2559 ≤ batchC05119PlusFourthP014ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP014Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP014Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP014Input2559 5).1 =
      batchC05119PlusFourthP014Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP014Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP014Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP014Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP014Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP014Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP014Input2559 =
      (batchC05119PlusFourthP014Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP014Input2559,
        batchC05119PlusFourthP014Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP014Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP014Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP014Center2559))).trans
  norm_num [batchC05119PlusFourthP014Error2559, batchC05119PlusFourthP014ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP014Center2559]

theorem batchC05119PlusFourthP014Bound2559 : batchC05119PlusFourthCell2559 ⟨14, by omega⟩ ≤
    batchC05119PlusFourthP014Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      batchC05119PlusFourthP014Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP014Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP014Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP014ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP014Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP014ExpUpper2559, batchC05119PlusFourthP014Frequency2559,
        batchC05119PlusFourthP014Upper2559]

def batchC05119PlusFourthP015Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP015Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP015Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP015ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP015Frequency2559 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def batchC05119PlusFourthP015Upper2559 : ℝ := (((19 * 10^40
        + 6213064106049384571348106147600088646179) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119PlusFourthP015Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP015ExpBound2559 :
    Real.exp batchC05119PlusFourthP015Exponent2559 ≤ batchC05119PlusFourthP015ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP015Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP015Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP015Input2559 5).1 =
      batchC05119PlusFourthP015Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP015Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP015Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP015Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP015Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP015Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP015Input2559 =
      (batchC05119PlusFourthP015Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP015Input2559,
        batchC05119PlusFourthP015Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP015Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP015Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP015Center2559))).trans
  norm_num [batchC05119PlusFourthP015Error2559, batchC05119PlusFourthP015ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP015Center2559]

theorem batchC05119PlusFourthP015Bound2559 : batchC05119PlusFourthCell2559 ⟨15, by omega⟩ ≤
    batchC05119PlusFourthP015Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      batchC05119PlusFourthP015Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP015Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP015Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP015ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP015Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP015ExpUpper2559, batchC05119PlusFourthP015Frequency2559,
        batchC05119PlusFourthP015Upper2559]

def batchC05119PlusFourthP016Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP016Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP016Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP016ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP016Frequency2559 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def batchC05119PlusFourthP016Upper2559 : ℝ := (((24 * 10^40
        + 6043491993595325237169992733866581212045) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119PlusFourthP016Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP016ExpBound2559 :
    Real.exp batchC05119PlusFourthP016Exponent2559 ≤ batchC05119PlusFourthP016ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP016Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP016Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP016Input2559 5).1 =
      batchC05119PlusFourthP016Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP016Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP016Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP016Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP016Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP016Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP016Input2559 =
      (batchC05119PlusFourthP016Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP016Input2559,
        batchC05119PlusFourthP016Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP016Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP016Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP016Center2559))).trans
  norm_num [batchC05119PlusFourthP016Error2559, batchC05119PlusFourthP016ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP016Center2559]

theorem batchC05119PlusFourthP016Bound2559 : batchC05119PlusFourthCell2559 ⟨16, by omega⟩ ≤
    batchC05119PlusFourthP016Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      batchC05119PlusFourthP016Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP016Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP016Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP016ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP016Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP016ExpUpper2559, batchC05119PlusFourthP016Frequency2559,
        batchC05119PlusFourthP016Upper2559]

def batchC05119PlusFourthP017Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP017Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP017Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP017ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP017Frequency2559 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def batchC05119PlusFourthP017Upper2559 : ℝ := (((73 * 10^40
        + 8787149174070767376412930778400914863545) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119PlusFourthP017Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP017ExpBound2559 :
    Real.exp batchC05119PlusFourthP017Exponent2559 ≤ batchC05119PlusFourthP017ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP017Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP017Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP017Input2559 5).1 =
      batchC05119PlusFourthP017Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP017Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP017Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP017Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP017Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP017Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP017Input2559 =
      (batchC05119PlusFourthP017Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP017Input2559,
        batchC05119PlusFourthP017Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP017Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP017Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP017Center2559))).trans
  norm_num [batchC05119PlusFourthP017Error2559, batchC05119PlusFourthP017ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP017Center2559]

theorem batchC05119PlusFourthP017Bound2559 : batchC05119PlusFourthCell2559 ⟨17, by omega⟩ ≤
    batchC05119PlusFourthP017Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      batchC05119PlusFourthP017Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP017Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP017Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP017ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP017Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP017ExpUpper2559, batchC05119PlusFourthP017Frequency2559,
        batchC05119PlusFourthP017Upper2559]

def batchC05119PlusFourthP018Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP018Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP018Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP018ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP018Frequency2559 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def batchC05119PlusFourthP018Upper2559 : ℝ := (((21 * 10^40
        + 3210545787404254096747270019293503496131) : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC05119PlusFourthP018Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP018ExpBound2559 :
    Real.exp batchC05119PlusFourthP018Exponent2559 ≤ batchC05119PlusFourthP018ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP018Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP018Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP018Input2559 5).1 =
      batchC05119PlusFourthP018Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP018Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP018Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP018Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP018Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP018Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP018Input2559 =
      (batchC05119PlusFourthP018Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP018Input2559,
        batchC05119PlusFourthP018Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP018Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP018Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP018Center2559))).trans
  norm_num [batchC05119PlusFourthP018Error2559, batchC05119PlusFourthP018ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP018Center2559]

theorem batchC05119PlusFourthP018Bound2559 : batchC05119PlusFourthCell2559 ⟨18, by omega⟩ ≤
    batchC05119PlusFourthP018Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      batchC05119PlusFourthP018Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP018Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP018Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP018ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP018Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP018ExpUpper2559, batchC05119PlusFourthP018Frequency2559,
        batchC05119PlusFourthP018Upper2559]

def batchC05119PlusFourthP019Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP019Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP019Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP019ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP019Frequency2559 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def batchC05119PlusFourthP019Upper2559 : ℝ := (((54 * 10^40
        + 5980972189274347546421330201154234157627) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119PlusFourthP019Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP019ExpBound2559 :
    Real.exp batchC05119PlusFourthP019Exponent2559 ≤ batchC05119PlusFourthP019ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP019Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP019Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP019Input2559 5).1 =
      batchC05119PlusFourthP019Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP019Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP019Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP019Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP019Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP019Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP019Input2559 =
      (batchC05119PlusFourthP019Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP019Input2559,
        batchC05119PlusFourthP019Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP019Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP019Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP019Center2559))).trans
  norm_num [batchC05119PlusFourthP019Error2559, batchC05119PlusFourthP019ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP019Center2559]

theorem batchC05119PlusFourthP019Bound2559 : batchC05119PlusFourthCell2559 ⟨19, by omega⟩ ≤
    batchC05119PlusFourthP019Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      batchC05119PlusFourthP019Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP019Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP019Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP019ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP019Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP019ExpUpper2559, batchC05119PlusFourthP019Frequency2559,
        batchC05119PlusFourthP019Upper2559]

def batchC05119PlusFourthP020Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP020Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP020Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP020ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP020Frequency2559 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def batchC05119PlusFourthP020Upper2559 : ℝ := (((140 * 10^40
        + 5744837887774056323750653200767926016331) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119PlusFourthP020Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP020ExpBound2559 :
    Real.exp batchC05119PlusFourthP020Exponent2559 ≤ batchC05119PlusFourthP020ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP020Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP020Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP020Input2559 5).1 =
      batchC05119PlusFourthP020Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP020Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP020Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP020Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP020Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP020Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP020Input2559 =
      (batchC05119PlusFourthP020Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP020Input2559,
        batchC05119PlusFourthP020Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP020Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP020Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP020Center2559))).trans
  norm_num [batchC05119PlusFourthP020Error2559, batchC05119PlusFourthP020ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP020Center2559]

theorem batchC05119PlusFourthP020Bound2559 : batchC05119PlusFourthCell2559 ⟨20, by omega⟩ ≤
    batchC05119PlusFourthP020Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      batchC05119PlusFourthP020Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP020Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP020Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP020ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP020Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP020ExpUpper2559, batchC05119PlusFourthP020Frequency2559,
        batchC05119PlusFourthP020Upper2559]

def batchC05119PlusFourthP021Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP021Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP021Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP021ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP021Frequency2559 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def batchC05119PlusFourthP021Upper2559 : ℝ := (((85 * 10^40
        + 7889128062175082199079910727357873178413) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119PlusFourthP021Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP021ExpBound2559 :
    Real.exp batchC05119PlusFourthP021Exponent2559 ≤ batchC05119PlusFourthP021ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP021Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP021Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP021Input2559 5).1 =
      batchC05119PlusFourthP021Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP021Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP021Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP021Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP021Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP021Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP021Input2559 =
      (batchC05119PlusFourthP021Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP021Input2559,
        batchC05119PlusFourthP021Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP021Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP021Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP021Center2559))).trans
  norm_num [batchC05119PlusFourthP021Error2559, batchC05119PlusFourthP021ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP021Center2559]

theorem batchC05119PlusFourthP021Bound2559 : batchC05119PlusFourthCell2559 ⟨21, by omega⟩ ≤
    batchC05119PlusFourthP021Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      batchC05119PlusFourthP021Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP021Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP021Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP021ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP021Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP021ExpUpper2559, batchC05119PlusFourthP021Frequency2559,
        batchC05119PlusFourthP021Upper2559]

def batchC05119PlusFourthP022Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP022Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP022Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP022ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP022Frequency2559 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def batchC05119PlusFourthP022Upper2559 : ℝ := (((189 * 10^40
        + 3028468361547082913484636570055890250493) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119PlusFourthP022Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP022ExpBound2559 :
    Real.exp batchC05119PlusFourthP022Exponent2559 ≤ batchC05119PlusFourthP022ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP022Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP022Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP022Input2559 5).1 =
      batchC05119PlusFourthP022Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP022Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP022Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP022Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP022Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP022Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP022Input2559 =
      (batchC05119PlusFourthP022Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP022Input2559,
        batchC05119PlusFourthP022Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP022Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP022Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP022Center2559))).trans
  norm_num [batchC05119PlusFourthP022Error2559, batchC05119PlusFourthP022ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP022Center2559]

theorem batchC05119PlusFourthP022Bound2559 : batchC05119PlusFourthCell2559 ⟨22, by omega⟩ ≤
    batchC05119PlusFourthP022Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      batchC05119PlusFourthP022Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP022Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP022Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP022ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP022Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP022ExpUpper2559, batchC05119PlusFourthP022Frequency2559,
        batchC05119PlusFourthP022Upper2559]

def batchC05119PlusFourthP023Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP023Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP023Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP023ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP023Frequency2559 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def batchC05119PlusFourthP023Upper2559 : ℝ := (((124 * 10^40
        + 755089048066799983132593836264199659491) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119PlusFourthP023Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP023ExpBound2559 :
    Real.exp batchC05119PlusFourthP023Exponent2559 ≤ batchC05119PlusFourthP023ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP023Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP023Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP023Input2559 5).1 =
      batchC05119PlusFourthP023Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP023Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP023Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP023Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP023Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP023Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP023Input2559 =
      (batchC05119PlusFourthP023Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP023Input2559,
        batchC05119PlusFourthP023Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP023Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP023Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP023Center2559))).trans
  norm_num [batchC05119PlusFourthP023Error2559, batchC05119PlusFourthP023ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP023Center2559]

theorem batchC05119PlusFourthP023Bound2559 : batchC05119PlusFourthCell2559 ⟨23, by omega⟩ ≤
    batchC05119PlusFourthP023Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      batchC05119PlusFourthP023Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP023Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP023Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP023ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP023Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP023ExpUpper2559, batchC05119PlusFourthP023Frequency2559,
        batchC05119PlusFourthP023Upper2559]

def batchC05119PlusFourthP024Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP024Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP024Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP024ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP024Frequency2559 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def batchC05119PlusFourthP024Upper2559 : ℝ := (((139 * 10^40
        + 6899246218794912147576920088019173674939) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119PlusFourthP024Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP024ExpBound2559 :
    Real.exp batchC05119PlusFourthP024Exponent2559 ≤ batchC05119PlusFourthP024ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP024Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP024Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP024Input2559 5).1 =
      batchC05119PlusFourthP024Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP024Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP024Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP024Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP024Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP024Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP024Input2559 =
      (batchC05119PlusFourthP024Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP024Input2559,
        batchC05119PlusFourthP024Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP024Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP024Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP024Center2559))).trans
  norm_num [batchC05119PlusFourthP024Error2559, batchC05119PlusFourthP024ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP024Center2559]

theorem batchC05119PlusFourthP024Bound2559 : batchC05119PlusFourthCell2559 ⟨24, by omega⟩ ≤
    batchC05119PlusFourthP024Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      batchC05119PlusFourthP024Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP024Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP024Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP024ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP024Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP024ExpUpper2559, batchC05119PlusFourthP024Frequency2559,
        batchC05119PlusFourthP024Upper2559]

def batchC05119PlusFourthP025Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP025Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP025Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP025ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP025Frequency2559 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def batchC05119PlusFourthP025Upper2559 : ℝ := (((40 * 10^40
        + 3250804032679059151191230319052096355583) : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC05119PlusFourthP025Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP025ExpBound2559 :
    Real.exp batchC05119PlusFourthP025Exponent2559 ≤ batchC05119PlusFourthP025ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP025Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP025Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP025Input2559 5).1 =
      batchC05119PlusFourthP025Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP025Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP025Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP025Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP025Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP025Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP025Input2559 =
      (batchC05119PlusFourthP025Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP025Input2559,
        batchC05119PlusFourthP025Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP025Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP025Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP025Center2559))).trans
  norm_num [batchC05119PlusFourthP025Error2559, batchC05119PlusFourthP025ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP025Center2559]

theorem batchC05119PlusFourthP025Bound2559 : batchC05119PlusFourthCell2559 ⟨25, by omega⟩ ≤
    batchC05119PlusFourthP025Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      batchC05119PlusFourthP025Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP025Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP025Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP025ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP025Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP025ExpUpper2559, batchC05119PlusFourthP025Frequency2559,
        batchC05119PlusFourthP025Upper2559]

def batchC05119PlusFourthP026Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP026Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP026Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP026ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP026Frequency2559 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def batchC05119PlusFourthP026Upper2559 : ℝ := (((371 * 10^40
        + 7714855670662988155578528403584661985395) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119PlusFourthP026Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP026ExpBound2559 :
    Real.exp batchC05119PlusFourthP026Exponent2559 ≤ batchC05119PlusFourthP026ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP026Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP026Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP026Input2559 5).1 =
      batchC05119PlusFourthP026Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP026Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP026Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP026Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP026Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP026Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP026Input2559 =
      (batchC05119PlusFourthP026Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP026Input2559,
        batchC05119PlusFourthP026Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP026Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP026Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP026Center2559))).trans
  norm_num [batchC05119PlusFourthP026Error2559, batchC05119PlusFourthP026ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP026Center2559]

theorem batchC05119PlusFourthP026Bound2559 : batchC05119PlusFourthCell2559 ⟨26, by omega⟩ ≤
    batchC05119PlusFourthP026Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      batchC05119PlusFourthP026Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP026Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP026Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP026ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP026Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP026ExpUpper2559, batchC05119PlusFourthP026Frequency2559,
        batchC05119PlusFourthP026Upper2559]

def batchC05119PlusFourthP027Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP027Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP027Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP027ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP027Frequency2559 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def batchC05119PlusFourthP027Upper2559 : ℝ := (((452 * 10^40
        + 3890128674599300327300588382308555792043) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC05119PlusFourthP027Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP027ExpBound2559 :
    Real.exp batchC05119PlusFourthP027Exponent2559 ≤ batchC05119PlusFourthP027ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP027Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP027Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP027Input2559 5).1 =
      batchC05119PlusFourthP027Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP027Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP027Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP027Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP027Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP027Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP027Input2559 =
      (batchC05119PlusFourthP027Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP027Input2559,
        batchC05119PlusFourthP027Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP027Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP027Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP027Center2559))).trans
  norm_num [batchC05119PlusFourthP027Error2559, batchC05119PlusFourthP027ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP027Center2559]

theorem batchC05119PlusFourthP027Bound2559 : batchC05119PlusFourthCell2559 ⟨27, by omega⟩ ≤
    batchC05119PlusFourthP027Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      batchC05119PlusFourthP027Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP027Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP027Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP027ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP027Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP027ExpUpper2559, batchC05119PlusFourthP027Frequency2559,
        batchC05119PlusFourthP027Upper2559]

def batchC05119PlusFourthP028Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP028Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP028Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP028ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP028Frequency2559 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def batchC05119PlusFourthP028Upper2559 : ℝ := (((1 * 10^40
        + 9050179842530705405820839488291952256947) : ℝ) /
        (570899 * 10^40
        + 770823839524233143877797980545530986496))

noncomputable def batchC05119PlusFourthP028Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP028ExpBound2559 :
    Real.exp batchC05119PlusFourthP028Exponent2559 ≤ batchC05119PlusFourthP028ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP028Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP028Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP028Input2559 5).1 =
      batchC05119PlusFourthP028Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP028Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP028Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP028Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP028Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP028Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP028Input2559 =
      (batchC05119PlusFourthP028Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP028Input2559,
        batchC05119PlusFourthP028Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP028Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP028Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP028Center2559))).trans
  norm_num [batchC05119PlusFourthP028Error2559, batchC05119PlusFourthP028ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP028Center2559]

theorem batchC05119PlusFourthP028Bound2559 : batchC05119PlusFourthCell2559 ⟨28, by omega⟩ ≤
    batchC05119PlusFourthP028Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      batchC05119PlusFourthP028Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP028Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP028Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP028ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP028Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP028ExpUpper2559, batchC05119PlusFourthP028Frequency2559,
        batchC05119PlusFourthP028Upper2559]

def batchC05119PlusFourthP029Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchC05119PlusFourthP029Center2559 : RatPair2542 := (((136761812904851798033513937177447845 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusFourthP029Error2559 : ℝ := ((12287562243733755928524809515635 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP029ExpUpper2559 : ℝ := (((15037120 * 10^40
        + 3524610375751431548600914211538102858355) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC05119PlusFourthP029Frequency2559 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def batchC05119PlusFourthP029Upper2559 : ℝ := (((272 * 10^40
        + 6700569434539071544678381115247579945815) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC05119PlusFourthP029Exponent2559 : ℝ := ((-30) : ℝ)

theorem batchC05119PlusFourthP029ExpBound2559 :
    Real.exp batchC05119PlusFourthP029Exponent2559 ≤ batchC05119PlusFourthP029ExpUpper2559 := by
  have hz : ‖embedPair2542 batchC05119PlusFourthP029Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119PlusFourthP029Input2559]
  have hc : (compactExp2547 batchC05119PlusFourthP029Input2559 5).1 =
      batchC05119PlusFourthP029Center2559 := by decide +kernel
  have he : ((compactExp2547 batchC05119PlusFourthP029Input2559 5).2 : ℝ) =
      batchC05119PlusFourthP029Error2559 := by
    have hq : (compactExp2547 batchC05119PlusFourthP029Input2559 5).2 =
        ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC05119PlusFourthP029Error2559]
  have h := compactExp_error2547 batchC05119PlusFourthP029Input2559 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 batchC05119PlusFourthP029Input2559 =
      (batchC05119PlusFourthP029Exponent2559 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC05119PlusFourthP029Input2559,
        batchC05119PlusFourthP029Exponent2559,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC05119PlusFourthP029Exponent2559 : ℂ)) (embedPair2542
        batchC05119PlusFourthP029Center2559) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC05119PlusFourthP029Center2559))).trans
  norm_num [batchC05119PlusFourthP029Error2559, batchC05119PlusFourthP029ExpUpper2559,
      pairMagnitude2542,
      batchC05119PlusFourthP029Center2559]

theorem batchC05119PlusFourthP029Bound2559 : batchC05119PlusFourthCell2559 ⟨29, by omega⟩ ≤
    batchC05119PlusFourthP029Upper2559 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      batchC05119PlusFourthP029Frequency2559 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC05119PlusFourthP029Frequency2559])
    norm_num [weightedLambda2537, nodeModulation2541, batchC05119PlusFourthP029Frequency2559,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ)
    (by norm_num) (by norm_num) hf
    (by convert batchC05119PlusFourthP029ExpBound2559 using 1; norm_num
        [batchC05119PlusFourthP029Exponent2559])
  have hid : batchC05119PlusFourthCell2559 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) (0 : ℝ) ((2535301239142085030661540001349632 : ℝ) /
        6135428905104631913280910298972265625) (((-65536001) : ℝ) /
        51200000000) (0 : ℝ) := by
    norm_num [batchC05119PlusFourthCell2559, cellNearAbs2538, batchN05119PlusPosition2559,
      batchN05120PlusPosition2559, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC05119PlusFourthP029ExpUpper2559, batchC05119PlusFourthP029Frequency2559,
        batchC05119PlusFourthP029Upper2559]

noncomputable def batchC05119PlusFourthUpper2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05119PlusFourthP000Upper2559
  | 1 => batchC05119PlusFourthP001Upper2559
  | 2 => batchC05119PlusFourthP002Upper2559
  | 3 => batchC05119PlusFourthP003Upper2559
  | 4 => batchC05119PlusFourthP004Upper2559
  | 5 => batchC05119PlusFourthP005Upper2559
  | 6 => batchC05119PlusFourthP006Upper2559
  | 7 => batchC05119PlusFourthP007Upper2559
  | 8 => batchC05119PlusFourthP008Upper2559
  | 9 => batchC05119PlusFourthP009Upper2559
  | 10 => batchC05119PlusFourthP010Upper2559
  | 11 => batchC05119PlusFourthP011Upper2559
  | 12 => batchC05119PlusFourthP012Upper2559
  | 13 => batchC05119PlusFourthP013Upper2559
  | 14 => batchC05119PlusFourthP014Upper2559
  | 15 => batchC05119PlusFourthP015Upper2559
  | 16 => batchC05119PlusFourthP016Upper2559
  | 17 => batchC05119PlusFourthP017Upper2559
  | 18 => batchC05119PlusFourthP018Upper2559
  | 19 => batchC05119PlusFourthP019Upper2559
  | 20 => batchC05119PlusFourthP020Upper2559
  | 21 => batchC05119PlusFourthP021Upper2559
  | 22 => batchC05119PlusFourthP022Upper2559
  | 23 => batchC05119PlusFourthP023Upper2559
  | 24 => batchC05119PlusFourthP024Upper2559
  | 25 => batchC05119PlusFourthP025Upper2559
  | 26 => batchC05119PlusFourthP026Upper2559
  | 27 => batchC05119PlusFourthP027Upper2559
  | 28 => batchC05119PlusFourthP028Upper2559
  | 29 => batchC05119PlusFourthP029Upper2559
  | _ => 0

theorem batchC05119PlusFourthBound2559 (i : Fin 30) :
    batchC05119PlusFourthCell2559 i ≤ batchC05119PlusFourthUpper2559 i := by
  fin_cases i
  · exact batchC05119PlusFourthP000Bound2559
  · exact batchC05119PlusFourthP001Bound2559
  · exact batchC05119PlusFourthP002Bound2559
  · exact batchC05119PlusFourthP003Bound2559
  · exact batchC05119PlusFourthP004Bound2559
  · exact batchC05119PlusFourthP005Bound2559
  · exact batchC05119PlusFourthP006Bound2559
  · exact batchC05119PlusFourthP007Bound2559
  · exact batchC05119PlusFourthP008Bound2559
  · exact batchC05119PlusFourthP009Bound2559
  · exact batchC05119PlusFourthP010Bound2559
  · exact batchC05119PlusFourthP011Bound2559
  · exact batchC05119PlusFourthP012Bound2559
  · exact batchC05119PlusFourthP013Bound2559
  · exact batchC05119PlusFourthP014Bound2559
  · exact batchC05119PlusFourthP015Bound2559
  · exact batchC05119PlusFourthP016Bound2559
  · exact batchC05119PlusFourthP017Bound2559
  · exact batchC05119PlusFourthP018Bound2559
  · exact batchC05119PlusFourthP019Bound2559
  · exact batchC05119PlusFourthP020Bound2559
  · exact batchC05119PlusFourthP021Bound2559
  · exact batchC05119PlusFourthP022Bound2559
  · exact batchC05119PlusFourthP023Bound2559
  · exact batchC05119PlusFourthP024Bound2559
  · exact batchC05119PlusFourthP025Bound2559
  · exact batchC05119PlusFourthP026Bound2559
  · exact batchC05119PlusFourthP027Bound2559
  · exact batchC05119PlusFourthP028Bound2559
  · exact batchC05119PlusFourthP029Bound2559

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP000Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP001Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP002Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP003Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP004Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP005Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP006Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP007Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP008Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP009Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP010Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP011Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP012Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP013Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP014Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP015Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP016Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP017Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP018Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP019Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP020Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP021Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP022Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP023Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP024Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP025Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP026Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP027Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP028Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthP029Bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusFourthBound2559
