import ConnesWeilRH.Dev.C1RouteABatchN02702Minus2558
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC02702MinusLeftP000NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP000NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02702MinusPosition2558‖ ≤
      batchC02702MinusLeftP000NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP000Factor2558 * embedPair2542
      batchN02702MinusP000Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP000Factor2558, batchN02702MinusP000Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP000Factor2558 * embedPair2542 batchN02702MinusP000Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP000DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP000Factor2558, batchN02702MinusP000Error2558,
      batchC02702MinusLeftP000NormUpper2558]

noncomputable def batchC02702MinusLeftP001NormUpper2558 : ℝ := ((704715163 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP001NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02702MinusPosition2558‖ ≤
      batchC02702MinusLeftP001NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP001Factor2558 * embedPair2542
      batchN02702MinusP001Center2558‖
      ≤
      ((104916041 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP001Factor2558, batchN02702MinusP001Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP001Factor2558 * embedPair2542 batchN02702MinusP001Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP001DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP001Factor2558, batchN02702MinusP001Error2558,
      batchC02702MinusLeftP001NormUpper2558]

noncomputable def batchC02702MinusLeftP002NormUpper2558 : ℝ := ((2595539582942058653006232471 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP002NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02702MinusPosition2558‖ ≤
      batchC02702MinusLeftP002NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP002Factor2558 * embedPair2542
      batchN02702MinusP002Center2558‖
      ≤
      ((2595539582942046288305543645 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP002Factor2558, batchN02702MinusP002Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP002Factor2558 * embedPair2542 batchN02702MinusP002Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP002DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP002Factor2558, batchN02702MinusP002Error2558,
      batchC02702MinusLeftP002NormUpper2558]

noncomputable def batchC02702MinusLeftP003NormUpper2558 : ℝ :=
    ((17268815808325362392860283283174165 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP003NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02702MinusPosition2558‖ ≤
      batchC02702MinusLeftP003NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP003Factor2558 * embedPair2542
      batchN02702MinusP003Center2558‖
      ≤
      ((17268815808325287067125096695009981 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP003Factor2558, batchN02702MinusP003Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP003Factor2558 * embedPair2542 batchN02702MinusP003Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP003DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP003Factor2558, batchN02702MinusP003Error2558,
      batchC02702MinusLeftP003NormUpper2558]

noncomputable def batchC02702MinusLeftP004NormUpper2558 : ℝ :=
    ((7446143126680576499603186399761486353 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP004NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02702MinusPosition2558‖ ≤
      batchC02702MinusLeftP004NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP004Factor2558 * embedPair2542
      batchN02702MinusP004Center2558‖
      ≤
      ((7446143126680545355107817497486576277 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP004Factor2558, batchN02702MinusP004Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP004Factor2558 * embedPair2542 batchN02702MinusP004Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP004DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP004Factor2558, batchN02702MinusP004Error2558,
      batchC02702MinusLeftP004NormUpper2558]

noncomputable def batchC02702MinusLeftP005NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP005NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02702MinusPosition2558‖ ≤
      batchC02702MinusLeftP005NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP005Factor2558 * embedPair2542
      batchN02702MinusP005Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP005Factor2558, batchN02702MinusP005Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP005Factor2558 * embedPair2542 batchN02702MinusP005Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP005DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP005Factor2558, batchN02702MinusP005Error2558,
      batchC02702MinusLeftP005NormUpper2558]

noncomputable def batchC02702MinusLeftP006NormUpper2558 : ℝ := ((3894819270069028170449 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702MinusLeftP006NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02702MinusPosition2558‖ ≤
      batchC02702MinusLeftP006NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP006Factor2558 * embedPair2542
      batchN02702MinusP006Center2558‖
      ≤
      ((3894819270069026954841 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP006Factor2558, batchN02702MinusP006Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP006Factor2558 * embedPair2542 batchN02702MinusP006Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP006DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP006Factor2558, batchN02702MinusP006Error2558,
      batchC02702MinusLeftP006NormUpper2558]

noncomputable def batchC02702MinusLeftP007NormUpper2558 : ℝ := ((489569142148219184847028759268395
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP007NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02702MinusPosition2558‖ ≤
      batchC02702MinusLeftP007NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP007Factor2558 * embedPair2542
      batchN02702MinusP007Center2558‖
      ≤
      ((489569142148219123239172704927239 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP007Factor2558, batchN02702MinusP007Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP007Factor2558 * embedPair2542 batchN02702MinusP007Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP007DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP007Factor2558, batchN02702MinusP007Error2558,
      batchC02702MinusLeftP007NormUpper2558]

noncomputable def batchC02702MinusLeftP008NormUpper2558 : ℝ := ((89075193393858148745 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem batchC02702MinusLeftP008NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02702MinusPosition2558‖ ≤
      batchC02702MinusLeftP008NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP008Factor2558 * embedPair2542
      batchN02702MinusP008Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP008Factor2558, batchN02702MinusP008Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP008Factor2558 * embedPair2542 batchN02702MinusP008Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP008DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP008Factor2558, batchN02702MinusP008Error2558,
      batchC02702MinusLeftP008NormUpper2558]

noncomputable def batchC02702MinusLeftP009NormUpper2558 : ℝ := ((178150906061417449139 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702MinusLeftP009NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02702MinusPosition2558‖ ≤
      batchC02702MinusLeftP009NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP009Factor2558 * embedPair2542
      batchN02702MinusP009Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP009Factor2558, batchN02702MinusP009Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP009Factor2558 * embedPair2542 batchN02702MinusP009Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP009DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP009Factor2558, batchN02702MinusP009Error2558,
      batchC02702MinusLeftP009NormUpper2558]

noncomputable def batchC02702MinusLeftP010NormUpper2558 : ℝ := ((712604827202252553319 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP010NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP010NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP010Factor2558 * embedPair2542
      batchN02702MinusP010Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP010Factor2558, batchN02702MinusP010Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP010Factor2558 * embedPair2542 batchN02702MinusP010Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP010DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP010Factor2558, batchN02702MinusP010Error2558,
      batchC02702MinusLeftP010NormUpper2558]

noncomputable def batchC02702MinusLeftP011NormUpper2558 : ℝ := ((178151407312167922869 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702MinusLeftP011NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP011NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP011Factor2558 * embedPair2542
      batchN02702MinusP011Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP011Factor2558, batchN02702MinusP011Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP011Factor2558 * embedPair2542 batchN02702MinusP011Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP011DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP011Factor2558, batchN02702MinusP011Error2558,
      batchC02702MinusLeftP011NormUpper2558]

noncomputable def batchC02702MinusLeftP012NormUpper2558 : ℝ := ((178151614992959116109 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702MinusLeftP012NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP012NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP012Factor2558 * embedPair2542
      batchN02702MinusP012Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP012Factor2558, batchN02702MinusP012Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP012Factor2558 * embedPair2542 batchN02702MinusP012Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP012DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP012Factor2558, batchN02702MinusP012Error2558,
      batchC02702MinusLeftP012NormUpper2558]

noncomputable def batchC02702MinusLeftP013NormUpper2558 : ℝ := ((356303608498649232907 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702MinusLeftP013NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP013NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP013Factor2558 * embedPair2542
      batchN02702MinusP013Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP013Factor2558, batchN02702MinusP013Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP013Factor2558 * embedPair2542 batchN02702MinusP013Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP013DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP013Factor2558, batchN02702MinusP013Error2558,
      batchC02702MinusLeftP013NormUpper2558]

noncomputable def batchC02702MinusLeftP014NormUpper2558 : ℝ := ((178152154921632271395 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702MinusLeftP014NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP014NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP014Factor2558 * embedPair2542
      batchN02702MinusP014Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP014Factor2558, batchN02702MinusP014Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP014Factor2558 * embedPair2542 batchN02702MinusP014Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP014DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP014Factor2558, batchN02702MinusP014Error2558,
      batchC02702MinusLeftP014NormUpper2558]

noncomputable def batchC02702MinusLeftP015NormUpper2558 : ℝ := ((712609624717005060525 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP015NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP015NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP015Factor2558 * embedPair2542
      batchN02702MinusP015Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP015Factor2558, batchN02702MinusP015Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP015Factor2558 * embedPair2542 batchN02702MinusP015Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP015DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP015Factor2558, batchN02702MinusP015Error2558,
      batchC02702MinusLeftP015NormUpper2558]

noncomputable def batchC02702MinusLeftP016NormUpper2558 : ℝ := ((712610351029924683683 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP016NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP016NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP016Factor2558 * embedPair2542
      batchN02702MinusP016Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP016Factor2558, batchN02702MinusP016Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP016Factor2558 * embedPair2542 batchN02702MinusP016Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP016DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP016Factor2558, batchN02702MinusP016Error2558,
      batchC02702MinusLeftP016NormUpper2558]

noncomputable def batchC02702MinusLeftP017NormUpper2558 : ℝ := ((712611761845952749745 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP017NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP017NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP017Factor2558 * embedPair2542
      batchN02702MinusP017Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP017Factor2558, batchN02702MinusP017Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP017Factor2558 * embedPair2542 batchN02702MinusP017Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP017DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP017Factor2558, batchN02702MinusP017Error2558,
      batchC02702MinusLeftP017NormUpper2558]

noncomputable def batchC02702MinusLeftP018NormUpper2558 : ℝ := ((44538268452811709037 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

theorem batchC02702MinusLeftP018NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP018NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP018Factor2558 * embedPair2542
      batchN02702MinusP018Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP018Factor2558, batchN02702MinusP018Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP018Factor2558 * embedPair2542 batchN02702MinusP018Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP018DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP018Factor2558, batchN02702MinusP018Error2558,
      batchC02702MinusLeftP018NormUpper2558]

noncomputable def batchC02702MinusLeftP019NormUpper2558 : ℝ := ((712613259241534784573 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP019NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP019NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP019Factor2558 * embedPair2542
      batchN02702MinusP019Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP019Factor2558, batchN02702MinusP019Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP019Factor2558 * embedPair2542 batchN02702MinusP019Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP019DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP019Factor2558, batchN02702MinusP019Error2558,
      batchC02702MinusLeftP019NormUpper2558]

noncomputable def batchC02702MinusLeftP020NormUpper2558 : ℝ := ((356307153754859636307 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702MinusLeftP020NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP020NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP020Factor2558 * embedPair2542
      batchN02702MinusP020Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP020Factor2558, batchN02702MinusP020Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP020Factor2558 * embedPair2542 batchN02702MinusP020Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP020DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP020Factor2558, batchN02702MinusP020Error2558,
      batchC02702MinusLeftP020NormUpper2558]

noncomputable def batchC02702MinusLeftP021NormUpper2558 : ℝ := ((356307591164854795023 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702MinusLeftP021NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP021NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP021Factor2558 * embedPair2542
      batchN02702MinusP021Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP021Factor2558, batchN02702MinusP021Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP021Factor2558 * embedPair2542 batchN02702MinusP021Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP021DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP021Factor2558, batchN02702MinusP021Error2558,
      batchC02702MinusLeftP021NormUpper2558]

noncomputable def batchC02702MinusLeftP022NormUpper2558 : ℝ := ((178153907523641105649 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702MinusLeftP022NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP022NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP022Factor2558 * embedPair2542
      batchN02702MinusP022Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP022Factor2558, batchN02702MinusP022Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP022Factor2558 * embedPair2542 batchN02702MinusP022Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP022DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP022Factor2558, batchN02702MinusP022Error2558,
      batchC02702MinusLeftP022NormUpper2558]

noncomputable def batchC02702MinusLeftP023NormUpper2558 : ℝ := ((712616921082795578011 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP023NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP023NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP023Factor2558 * embedPair2542
      batchN02702MinusP023Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP023Factor2558, batchN02702MinusP023Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP023Factor2558 * embedPair2542 batchN02702MinusP023Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP023DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP023Factor2558, batchN02702MinusP023Error2558,
      batchC02702MinusLeftP023NormUpper2558]

noncomputable def batchC02702MinusLeftP024NormUpper2558 : ℝ := ((712617514368184075747 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP024NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP024NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP024Factor2558 * embedPair2542
      batchN02702MinusP024Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP024Factor2558, batchN02702MinusP024Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP024Factor2558 * embedPair2542 batchN02702MinusP024Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP024DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP024Factor2558, batchN02702MinusP024Error2558,
      batchC02702MinusLeftP024NormUpper2558]

noncomputable def batchC02702MinusLeftP025NormUpper2558 : ℝ := ((712618258238730360595 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP025NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP025NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP025Factor2558 * embedPair2542
      batchN02702MinusP025Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP025Factor2558, batchN02702MinusP025Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP025Factor2558 * embedPair2542 batchN02702MinusP025Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP025DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP025Factor2558, batchN02702MinusP025Error2558,
      batchC02702MinusLeftP025NormUpper2558]

noncomputable def batchC02702MinusLeftP026NormUpper2558 : ℝ := ((178154754610917085233 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702MinusLeftP026NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP026NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP026Factor2558 * embedPair2542
      batchN02702MinusP026Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP026Factor2558, batchN02702MinusP026Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP026Factor2558 * embedPair2542 batchN02702MinusP026Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP026DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP026Factor2558, batchN02702MinusP026Error2558,
      batchC02702MinusLeftP026NormUpper2558]

noncomputable def batchC02702MinusLeftP027NormUpper2558 : ℝ := ((712620115443221426289 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP027NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP027NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP027Factor2558 * embedPair2542
      batchN02702MinusP027Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP027Factor2558, batchN02702MinusP027Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP027Factor2558 * embedPair2542 batchN02702MinusP027Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP027DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP027Factor2558, batchN02702MinusP027Error2558,
      batchC02702MinusLeftP027NormUpper2558]

noncomputable def batchC02702MinusLeftP028NormUpper2558 : ℝ := ((89077568720015747205 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem batchC02702MinusLeftP028NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP028NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP028Factor2558 * embedPair2542
      batchN02702MinusP028Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP028Factor2558, batchN02702MinusP028Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP028Factor2558 * embedPair2542 batchN02702MinusP028Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP028DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP028Factor2558, batchN02702MinusP028Error2558,
      batchC02702MinusLeftP028NormUpper2558]

noncomputable def batchC02702MinusLeftP029NormUpper2558 : ℝ := ((712621210979389208025 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusLeftP029NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02702MinusPosition2558‖
        ≤
      batchC02702MinusLeftP029NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02702MinusP029Factor2558 * embedPair2542
      batchN02702MinusP029Center2558‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02702MinusP029Factor2558, batchN02702MinusP029Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02702MinusPosition2558)
    (embedPair2542 batchN02702MinusP029Factor2558 * embedPair2542 batchN02702MinusP029Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02702MinusP029DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02702MinusP029Factor2558, batchN02702MinusP029Error2558,
      batchC02702MinusLeftP029NormUpper2558]

noncomputable def batchC02702MinusLeftNormUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02702MinusLeftP000NormUpper2558
  | 1 => batchC02702MinusLeftP001NormUpper2558
  | 2 => batchC02702MinusLeftP002NormUpper2558
  | 3 => batchC02702MinusLeftP003NormUpper2558
  | 4 => batchC02702MinusLeftP004NormUpper2558
  | 5 => batchC02702MinusLeftP005NormUpper2558
  | 6 => batchC02702MinusLeftP006NormUpper2558
  | 7 => batchC02702MinusLeftP007NormUpper2558
  | 8 => batchC02702MinusLeftP008NormUpper2558
  | 9 => batchC02702MinusLeftP009NormUpper2558
  | 10 => batchC02702MinusLeftP010NormUpper2558
  | 11 => batchC02702MinusLeftP011NormUpper2558
  | 12 => batchC02702MinusLeftP012NormUpper2558
  | 13 => batchC02702MinusLeftP013NormUpper2558
  | 14 => batchC02702MinusLeftP014NormUpper2558
  | 15 => batchC02702MinusLeftP015NormUpper2558
  | 16 => batchC02702MinusLeftP016NormUpper2558
  | 17 => batchC02702MinusLeftP017NormUpper2558
  | 18 => batchC02702MinusLeftP018NormUpper2558
  | 19 => batchC02702MinusLeftP019NormUpper2558
  | 20 => batchC02702MinusLeftP020NormUpper2558
  | 21 => batchC02702MinusLeftP021NormUpper2558
  | 22 => batchC02702MinusLeftP022NormUpper2558
  | 23 => batchC02702MinusLeftP023NormUpper2558
  | 24 => batchC02702MinusLeftP024NormUpper2558
  | 25 => batchC02702MinusLeftP025NormUpper2558
  | 26 => batchC02702MinusLeftP026NormUpper2558
  | 27 => batchC02702MinusLeftP027NormUpper2558
  | 28 => batchC02702MinusLeftP028NormUpper2558
  | 29 => batchC02702MinusLeftP029NormUpper2558
  | _ => 0

theorem batchC02702MinusLeftNormBound2558 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 i batchN02702MinusPosition2558‖ ≤
        batchC02702MinusLeftNormUpper2558 i := by
  fin_cases i
  · exact batchC02702MinusLeftP000NormBound2558
  · exact batchC02702MinusLeftP001NormBound2558
  · exact batchC02702MinusLeftP002NormBound2558
  · exact batchC02702MinusLeftP003NormBound2558
  · exact batchC02702MinusLeftP004NormBound2558
  · exact batchC02702MinusLeftP005NormBound2558
  · exact batchC02702MinusLeftP006NormBound2558
  · exact batchC02702MinusLeftP007NormBound2558
  · exact batchC02702MinusLeftP008NormBound2558
  · exact batchC02702MinusLeftP009NormBound2558
  · exact batchC02702MinusLeftP010NormBound2558
  · exact batchC02702MinusLeftP011NormBound2558
  · exact batchC02702MinusLeftP012NormBound2558
  · exact batchC02702MinusLeftP013NormBound2558
  · exact batchC02702MinusLeftP014NormBound2558
  · exact batchC02702MinusLeftP015NormBound2558
  · exact batchC02702MinusLeftP016NormBound2558
  · exact batchC02702MinusLeftP017NormBound2558
  · exact batchC02702MinusLeftP018NormBound2558
  · exact batchC02702MinusLeftP019NormBound2558
  · exact batchC02702MinusLeftP020NormBound2558
  · exact batchC02702MinusLeftP021NormBound2558
  · exact batchC02702MinusLeftP022NormBound2558
  · exact batchC02702MinusLeftP023NormBound2558
  · exact batchC02702MinusLeftP024NormBound2558
  · exact batchC02702MinusLeftP025NormBound2558
  · exact batchC02702MinusLeftP026NormBound2558
  · exact batchC02702MinusLeftP027NormBound2558
  · exact batchC02702MinusLeftP028NormBound2558
  · exact batchC02702MinusLeftP029NormBound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP000NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP001NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP002NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP003NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP004NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP005NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP006NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP007NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP008NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP009NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP010NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP011NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP012NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP013NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP014NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP015NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP016NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP017NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP018NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP019NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP020NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP021NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP022NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP023NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP024NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP025NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP026NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP027NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP028NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusLeftP029NormBound2558
