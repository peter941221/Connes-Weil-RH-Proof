import ConnesWeilRH.Dev.C1RouteABatchN02703Minus2558
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC02702MinusRightP000NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP000NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02703MinusPosition2558‖ ≤
      batchC02702MinusRightP000NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP000Factor2558 * embedPair2542
      batchN02703MinusP000Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP000Factor2558, batchN02703MinusP000Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP000Factor2558 * embedPair2542 batchN02703MinusP000Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP000DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP000Factor2558, batchN02703MinusP000Error2558,
      batchC02702MinusRightP000NormUpper2558]

noncomputable def batchC02702MinusRightP001NormUpper2558 : ℝ := ((686866823 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP001NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02703MinusPosition2558‖ ≤
      batchC02702MinusRightP001NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP001Factor2558 * embedPair2542
      batchN02703MinusP001Center2558‖ ≤
      ((102173809 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP001Factor2558, batchN02703MinusP001Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP001Factor2558 * embedPair2542 batchN02703MinusP001Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP001DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP001Factor2558, batchN02703MinusP001Error2558,
      batchC02702MinusRightP001NormUpper2558]

noncomputable def batchC02702MinusRightP002NormUpper2558 : ℝ := ((1363367199251416688601734939 :
    ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702MinusRightP002NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02703MinusPosition2558‖ ≤
      batchC02702MinusRightP002NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP002Factor2558 * embedPair2542
      batchN02703MinusP002Center2558‖ ≤
      ((2726734398502820311186438039 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP002Factor2558, batchN02703MinusP002Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP002Factor2558 * embedPair2542 batchN02703MinusP002Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP002DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP002Factor2558, batchN02703MinusP002Error2558,
      batchC02702MinusRightP002NormUpper2558]

noncomputable def batchC02702MinusRightP003NormUpper2558 : ℝ :=
    ((4392228783560267787373972656766757 : ℝ)
    /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702MinusRightP003NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02703MinusPosition2558‖ ≤
      batchC02702MinusRightP003NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP003Factor2558 * embedPair2542
      batchN02703MinusP003Center2558‖ ≤
      ((17568915134240994035422387310319979 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP003Factor2558, batchN02703MinusP003Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP003Factor2558 * embedPair2542 batchN02703MinusP003Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP003DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP003Factor2558, batchN02703MinusP003Error2558,
      batchC02702MinusRightP003NormUpper2558]

noncomputable def batchC02702MinusRightP004NormUpper2558 : ℝ :=
    ((7509223493182202117343684173729906105 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP004NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02703MinusPosition2558‖ ≤
      batchC02702MinusRightP004NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP004Factor2558 * embedPair2542
      batchN02703MinusP004Center2558‖ ≤
      ((7509223493182170523725434614781638305 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP004Factor2558, batchN02703MinusP004Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP004Factor2558 * embedPair2542 batchN02703MinusP004Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP004DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP004Factor2558, batchN02703MinusP004Error2558,
      batchC02702MinusRightP004NormUpper2558]

noncomputable def batchC02702MinusRightP005NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP005NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02703MinusPosition2558‖ ≤
      batchC02702MinusRightP005NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP005Factor2558 * embedPair2542
      batchN02703MinusP005Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP005Factor2558, batchN02703MinusP005Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP005Factor2558 * embedPair2542 batchN02703MinusP005Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP005DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP005Factor2558, batchN02703MinusP005Error2558,
      batchC02702MinusRightP005NormUpper2558]

noncomputable def batchC02702MinusRightP006NormUpper2558 : ℝ := ((8460559323743076923703 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP006NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02703MinusPosition2558‖ ≤
      batchC02702MinusRightP006NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP006Factor2558 * embedPair2542
      batchN02703MinusP006Center2558‖ ≤
      ((8460559323743074347567 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP006Factor2558, batchN02703MinusP006Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP006Factor2558 * embedPair2542 batchN02703MinusP006Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP006DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP006Factor2558, batchN02703MinusP006Error2558,
      batchC02702MinusRightP006NormUpper2558]

noncomputable def batchC02702MinusRightP007NormUpper2558 : ℝ :=
    ((496272929361394694840440149421585 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP007NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02703MinusPosition2558‖ ≤
      batchC02702MinusRightP007NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP007Factor2558 * embedPair2542
      batchN02703MinusP007Center2558‖ ≤
      ((124068232340348658101551476449947 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP007Factor2558, batchN02703MinusP007Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP007Factor2558 * embedPair2542 batchN02703MinusP007Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP007DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP007Factor2558, batchN02703MinusP007Error2558,
      batchC02702MinusRightP007NormUpper2558]

noncomputable def batchC02702MinusRightP008NormUpper2558 : ℝ := ((62548114149875153493 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP008NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02703MinusPosition2558‖ ≤
      batchC02702MinusRightP008NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP008Factor2558 * embedPair2542
      batchN02703MinusP008Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP008Factor2558, batchN02703MinusP008Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP008Factor2558 * embedPair2542 batchN02703MinusP008Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP008DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP008Factor2558, batchN02703MinusP008Error2558,
      batchC02702MinusRightP008NormUpper2558]

noncomputable def batchC02702MinusRightP009NormUpper2558 : ℝ := ((62548524404707843897 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP009NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02703MinusPosition2558‖ ≤
      batchC02702MinusRightP009NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP009Factor2558 * embedPair2542
      batchN02703MinusP009Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP009Factor2558, batchN02703MinusP009Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP009Factor2558 * embedPair2542 batchN02703MinusP009Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP009DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP009Factor2558, batchN02703MinusP009Error2558,
      batchC02702MinusRightP009NormUpper2558]

noncomputable def batchC02702MinusRightP010NormUpper2558 : ℝ := ((31274381002373049249 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702MinusRightP010NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP010NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP010Factor2558 * embedPair2542
      batchN02703MinusP010Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP010Factor2558, batchN02703MinusP010Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP010Factor2558 * embedPair2542 batchN02703MinusP010Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP010DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP010Factor2558, batchN02703MinusP010Error2558,
      batchC02702MinusRightP010NormUpper2558]

noncomputable def batchC02702MinusRightP011NormUpper2558 : ℝ := ((31274460209735633085 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702MinusRightP011NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP011NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP011Factor2558 * embedPair2542
      batchN02703MinusP011Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP011Factor2558, batchN02703MinusP011Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP011Factor2558 * embedPair2542 batchN02703MinusP011Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP011DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP011Factor2558, batchN02703MinusP011Error2558,
      batchC02702MinusRightP011NormUpper2558]

noncomputable def batchC02702MinusRightP012NormUpper2558 : ℝ := ((62549084498074514671 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP012NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP012NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP012Factor2558 * embedPair2542
      batchN02703MinusP012Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP012Factor2558, batchN02703MinusP012Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP012Factor2558 * embedPair2542 batchN02703MinusP012Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP012DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP012Factor2558, batchN02703MinusP012Error2558,
      batchC02702MinusRightP012NormUpper2558]

noncomputable def batchC02702MinusRightP013NormUpper2558 : ℝ := ((31274617010143226857 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702MinusRightP013NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP013NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP013Factor2558 * embedPair2542
      batchN02703MinusP013Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP013Factor2558, batchN02703MinusP013Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP013Factor2558 * embedPair2542 batchN02703MinusP013Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP013DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP013Factor2558, batchN02703MinusP013Error2558,
      batchC02702MinusRightP013NormUpper2558]

noncomputable def batchC02702MinusRightP014NormUpper2558 : ℝ := ((7818688883625195405 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem batchC02702MinusRightP014NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP014NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP014Factor2558 * embedPair2542
      batchN02703MinusP014Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP014Factor2558, batchN02703MinusP014Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP014Factor2558 * embedPair2542 batchN02703MinusP014Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP014DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP014Factor2558, batchN02703MinusP014Error2558,
      batchC02702MinusRightP014NormUpper2558]

noncomputable def batchC02702MinusRightP015NormUpper2558 : ℝ := ((62549709574845843127 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP015NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP015NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP015Factor2558 * embedPair2542
      batchN02703MinusP015Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP015Factor2558, batchN02703MinusP015Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP015Factor2558 * embedPair2542 batchN02703MinusP015Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP015DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP015Factor2558, batchN02703MinusP015Error2558,
      batchC02702MinusRightP015NormUpper2558]

noncomputable def batchC02702MinusRightP016NormUpper2558 : ℝ := ((3909365814400589361 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

theorem batchC02702MinusRightP016NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP016NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP016Factor2558 * embedPair2542
      batchN02703MinusP016Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP016Factor2558, batchN02703MinusP016Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP016Factor2558 * embedPair2542 batchN02703MinusP016Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP016DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP016Factor2558, batchN02703MinusP016Error2558,
      batchC02702MinusRightP016NormUpper2558]

noncomputable def batchC02702MinusRightP017NormUpper2558 : ℝ := ((15637532920811569919 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702MinusRightP017NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP017NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP017Factor2558 * embedPair2542
      batchN02703MinusP017Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP017Factor2558, batchN02703MinusP017Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP017Factor2558 * embedPair2542 batchN02703MinusP017Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP017DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP017Factor2558, batchN02703MinusP017Error2558,
      batchC02702MinusRightP017NormUpper2558]

noncomputable def batchC02702MinusRightP018NormUpper2558 : ℝ := ((31275118517869447971 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702MinusRightP018NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP018NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP018Factor2558 * embedPair2542
      batchN02703MinusP018Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP018Factor2558, batchN02703MinusP018Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP018Factor2558 * embedPair2542 batchN02703MinusP018Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP018DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP018Factor2558, batchN02703MinusP018Error2558,
      batchC02702MinusRightP018NormUpper2558]

noncomputable def batchC02702MinusRightP019NormUpper2558 : ℝ := ((62550427436065163143 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP019NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP019NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP019Factor2558 * embedPair2542
      batchN02703MinusP019Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP019Factor2558, batchN02703MinusP019Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP019Factor2558 * embedPair2542 batchN02703MinusP019Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP019DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP019Factor2558, batchN02703MinusP019Error2558,
      batchC02702MinusRightP019NormUpper2558]

noncomputable def batchC02702MinusRightP020NormUpper2558 : ℝ := ((15637658620189608797 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702MinusRightP020NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP020NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP020Factor2558 * embedPair2542
      batchN02703MinusP020Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP020Factor2558, batchN02703MinusP020Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP020Factor2558 * embedPair2542 batchN02703MinusP020Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP020DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP020Factor2558, batchN02703MinusP020Error2558,
      batchC02702MinusRightP020NormUpper2558]

noncomputable def batchC02702MinusRightP021NormUpper2558 : ℝ := ((31275403633649352445 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702MinusRightP021NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP021NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP021Factor2558 * embedPair2542
      batchN02703MinusP021Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP021Factor2558, batchN02703MinusP021Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP021Factor2558 * embedPair2542 batchN02703MinusP021Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP021DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP021Factor2558, batchN02703MinusP021Error2558,
      batchC02702MinusRightP021NormUpper2558]

noncomputable def batchC02702MinusRightP022NormUpper2558 : ℝ := ((62550895705698763679 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP022NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP022NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP022Factor2558 * embedPair2542
      batchN02703MinusP022Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP022Factor2558, batchN02703MinusP022Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP022Factor2558 * embedPair2542 batchN02703MinusP022Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP022DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP022Factor2558, batchN02703MinusP022Error2558,
      batchC02702MinusRightP022NormUpper2558]

noncomputable def batchC02702MinusRightP023NormUpper2558 : ℝ := ((62551150689573303751 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP023NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP023NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP023Factor2558 * embedPair2542
      batchN02703MinusP023Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP023Factor2558, batchN02703MinusP023Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP023Factor2558 * embedPair2542 batchN02703MinusP023Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP023DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP023Factor2558, batchN02703MinusP023Error2558,
      batchC02702MinusRightP023NormUpper2558]

noncomputable def batchC02702MinusRightP024NormUpper2558 : ℝ := ((62551267869603860077 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP024NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP024NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP024Factor2558 * embedPair2542
      batchN02703MinusP024Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP024Factor2558, batchN02703MinusP024Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP024Factor2558 * embedPair2542 batchN02703MinusP024Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP024DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP024Factor2558, batchN02703MinusP024Error2558,
      batchC02702MinusRightP024NormUpper2558]

noncomputable def batchC02702MinusRightP025NormUpper2558 : ℝ := ((15637853697913326075 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702MinusRightP025NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP025NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP025Factor2558 * embedPair2542
      batchN02703MinusP025Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP025Factor2558, batchN02703MinusP025Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP025Factor2558 * embedPair2542 batchN02703MinusP025Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP025DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP025Factor2558, batchN02703MinusP025Error2558,
      batchC02702MinusRightP025NormUpper2558]

noncomputable def batchC02702MinusRightP026NormUpper2558 : ℝ := ((15637891234945073015 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702MinusRightP026NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP026NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP026Factor2558 * embedPair2542
      batchN02703MinusP026Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP026Factor2558, batchN02703MinusP026Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP026Factor2558 * embedPair2542 batchN02703MinusP026Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP026DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP026Factor2558, batchN02703MinusP026Error2558,
      batchC02702MinusRightP026NormUpper2558]

noncomputable def batchC02702MinusRightP027NormUpper2558 : ℝ := ((62551781607998403245 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP027NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP027NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP027Factor2558 * embedPair2542
      batchN02703MinusP027Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP027Factor2558, batchN02703MinusP027Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP027Factor2558 * embedPair2542 batchN02703MinusP027Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP027DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP027Factor2558, batchN02703MinusP027Error2558,
      batchC02702MinusRightP027NormUpper2558]

noncomputable def batchC02702MinusRightP028NormUpper2558 : ℝ := ((62551867389788624171 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP028NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP028NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP028Factor2558 * embedPair2542
      batchN02703MinusP028Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP028Factor2558, batchN02703MinusP028Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP028Factor2558 * embedPair2542 batchN02703MinusP028Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP028DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP028Factor2558, batchN02703MinusP028Error2558,
      batchC02702MinusRightP028NormUpper2558]

noncomputable def batchC02702MinusRightP029NormUpper2558 : ℝ := ((62551997986906063319 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702MinusRightP029NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02703MinusPosition2558‖
        ≤
      batchC02702MinusRightP029NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703MinusP029Factor2558 * embedPair2542
      batchN02703MinusP029Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP029Factor2558, batchN02703MinusP029Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02703MinusPosition2558)
    (embedPair2542 batchN02703MinusP029Factor2558 * embedPair2542 batchN02703MinusP029Center2558)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP029DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP029Factor2558, batchN02703MinusP029Error2558,
      batchC02702MinusRightP029NormUpper2558]

noncomputable def batchC02702MinusRightNormUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02702MinusRightP000NormUpper2558
  | 1 => batchC02702MinusRightP001NormUpper2558
  | 2 => batchC02702MinusRightP002NormUpper2558
  | 3 => batchC02702MinusRightP003NormUpper2558
  | 4 => batchC02702MinusRightP004NormUpper2558
  | 5 => batchC02702MinusRightP005NormUpper2558
  | 6 => batchC02702MinusRightP006NormUpper2558
  | 7 => batchC02702MinusRightP007NormUpper2558
  | 8 => batchC02702MinusRightP008NormUpper2558
  | 9 => batchC02702MinusRightP009NormUpper2558
  | 10 => batchC02702MinusRightP010NormUpper2558
  | 11 => batchC02702MinusRightP011NormUpper2558
  | 12 => batchC02702MinusRightP012NormUpper2558
  | 13 => batchC02702MinusRightP013NormUpper2558
  | 14 => batchC02702MinusRightP014NormUpper2558
  | 15 => batchC02702MinusRightP015NormUpper2558
  | 16 => batchC02702MinusRightP016NormUpper2558
  | 17 => batchC02702MinusRightP017NormUpper2558
  | 18 => batchC02702MinusRightP018NormUpper2558
  | 19 => batchC02702MinusRightP019NormUpper2558
  | 20 => batchC02702MinusRightP020NormUpper2558
  | 21 => batchC02702MinusRightP021NormUpper2558
  | 22 => batchC02702MinusRightP022NormUpper2558
  | 23 => batchC02702MinusRightP023NormUpper2558
  | 24 => batchC02702MinusRightP024NormUpper2558
  | 25 => batchC02702MinusRightP025NormUpper2558
  | 26 => batchC02702MinusRightP026NormUpper2558
  | 27 => batchC02702MinusRightP027NormUpper2558
  | 28 => batchC02702MinusRightP028NormUpper2558
  | 29 => batchC02702MinusRightP029NormUpper2558
  | _ => 0

theorem batchC02702MinusRightNormBound2558 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 i batchN02703MinusPosition2558‖ ≤
        batchC02702MinusRightNormUpper2558 i := by
  fin_cases i
  · exact batchC02702MinusRightP000NormBound2558
  · exact batchC02702MinusRightP001NormBound2558
  · exact batchC02702MinusRightP002NormBound2558
  · exact batchC02702MinusRightP003NormBound2558
  · exact batchC02702MinusRightP004NormBound2558
  · exact batchC02702MinusRightP005NormBound2558
  · exact batchC02702MinusRightP006NormBound2558
  · exact batchC02702MinusRightP007NormBound2558
  · exact batchC02702MinusRightP008NormBound2558
  · exact batchC02702MinusRightP009NormBound2558
  · exact batchC02702MinusRightP010NormBound2558
  · exact batchC02702MinusRightP011NormBound2558
  · exact batchC02702MinusRightP012NormBound2558
  · exact batchC02702MinusRightP013NormBound2558
  · exact batchC02702MinusRightP014NormBound2558
  · exact batchC02702MinusRightP015NormBound2558
  · exact batchC02702MinusRightP016NormBound2558
  · exact batchC02702MinusRightP017NormBound2558
  · exact batchC02702MinusRightP018NormBound2558
  · exact batchC02702MinusRightP019NormBound2558
  · exact batchC02702MinusRightP020NormBound2558
  · exact batchC02702MinusRightP021NormBound2558
  · exact batchC02702MinusRightP022NormBound2558
  · exact batchC02702MinusRightP023NormBound2558
  · exact batchC02702MinusRightP024NormBound2558
  · exact batchC02702MinusRightP025NormBound2558
  · exact batchC02702MinusRightP026NormBound2558
  · exact batchC02702MinusRightP027NormBound2558
  · exact batchC02702MinusRightP028NormBound2558
  · exact batchC02702MinusRightP029NormBound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP000NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP001NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP002NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP003NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP004NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP005NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP006NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP007NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP008NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP009NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP010NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP011NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP012NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP013NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP014NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP015NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP016NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP017NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP018NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP019NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP020NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP021NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP022NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP023NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP024NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP025NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP026NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP027NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP028NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusRightP029NormBound2558
