import ConnesWeilRH.Dev.C1RouteABatchN02703Minus2654
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC02703MinusLeftP000NormUpper2654 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP000NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02703MinusPosition2654‖ ≤
      batchC02703MinusLeftP000NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP000Factor2654 * embedPair2542
      batchN02703MinusP000Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP000Factor2654, batchN02703MinusP000Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP000Factor2654 * embedPair2542 batchN02703MinusP000Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP000DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP000Factor2654, batchN02703MinusP000Error2654,
      batchC02703MinusLeftP000NormUpper2654]

noncomputable def batchC02703MinusLeftP001NormUpper2654 : ℝ := ((686866823 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP001NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02703MinusPosition2654‖ ≤
      batchC02703MinusLeftP001NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP001Factor2654 * embedPair2542
      batchN02703MinusP001Center2654‖
      ≤
      ((102173809 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP001Factor2654, batchN02703MinusP001Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP001Factor2654 * embedPair2542 batchN02703MinusP001Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP001DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP001Factor2654, batchN02703MinusP001Error2654,
      batchC02703MinusLeftP001NormUpper2654]

noncomputable def batchC02703MinusLeftP002NormUpper2654 : ℝ := ((1363367199251416688601734939 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703MinusLeftP002NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02703MinusPosition2654‖ ≤
      batchC02703MinusLeftP002NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP002Factor2654 * embedPair2542
      batchN02703MinusP002Center2654‖
      ≤
      ((2726734398502820311186438039 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP002Factor2654, batchN02703MinusP002Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP002Factor2654 * embedPair2542 batchN02703MinusP002Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP002DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP002Factor2654, batchN02703MinusP002Error2654,
      batchC02703MinusLeftP002NormUpper2654]

noncomputable def batchC02703MinusLeftP003NormUpper2654 : ℝ :=
    ((4392228783560267787373972656766757 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02703MinusLeftP003NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02703MinusPosition2654‖ ≤
      batchC02703MinusLeftP003NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP003Factor2654 * embedPair2542
      batchN02703MinusP003Center2654‖
      ≤
      ((17568915134240994035422387310319979 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP003Factor2654, batchN02703MinusP003Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP003Factor2654 * embedPair2542 batchN02703MinusP003Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP003DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP003Factor2654, batchN02703MinusP003Error2654,
      batchC02703MinusLeftP003NormUpper2654]

noncomputable def batchC02703MinusLeftP004NormUpper2654 : ℝ :=
    ((7509223493182202117343684173729906105 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP004NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02703MinusPosition2654‖ ≤
      batchC02703MinusLeftP004NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP004Factor2654 * embedPair2542
      batchN02703MinusP004Center2654‖
      ≤
      ((7509223493182170523725434614781638305 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP004Factor2654, batchN02703MinusP004Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP004Factor2654 * embedPair2542 batchN02703MinusP004Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP004DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP004Factor2654, batchN02703MinusP004Error2654,
      batchC02703MinusLeftP004NormUpper2654]

noncomputable def batchC02703MinusLeftP005NormUpper2654 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP005NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02703MinusPosition2654‖ ≤
      batchC02703MinusLeftP005NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP005Factor2654 * embedPair2542
      batchN02703MinusP005Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP005Factor2654, batchN02703MinusP005Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP005Factor2654 * embedPair2542 batchN02703MinusP005Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP005DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP005Factor2654, batchN02703MinusP005Error2654,
      batchC02703MinusLeftP005NormUpper2654]

noncomputable def batchC02703MinusLeftP006NormUpper2654 : ℝ := ((8460559323743076923703 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP006NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02703MinusPosition2654‖ ≤
      batchC02703MinusLeftP006NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP006Factor2654 * embedPair2542
      batchN02703MinusP006Center2654‖
      ≤
      ((8460559323743074347567 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP006Factor2654, batchN02703MinusP006Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP006Factor2654 * embedPair2542 batchN02703MinusP006Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP006DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP006Factor2654, batchN02703MinusP006Error2654,
      batchC02703MinusLeftP006NormUpper2654]

noncomputable def batchC02703MinusLeftP007NormUpper2654 : ℝ := ((496272929361394694840440149421585
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP007NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02703MinusPosition2654‖ ≤
      batchC02703MinusLeftP007NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP007Factor2654 * embedPair2542
      batchN02703MinusP007Center2654‖
      ≤
      ((124068232340348658101551476449947 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP007Factor2654, batchN02703MinusP007Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP007Factor2654 * embedPair2542 batchN02703MinusP007Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP007DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP007Factor2654, batchN02703MinusP007Error2654,
      batchC02703MinusLeftP007NormUpper2654]

noncomputable def batchC02703MinusLeftP008NormUpper2654 : ℝ := ((62548114149875153493 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP008NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02703MinusPosition2654‖ ≤
      batchC02703MinusLeftP008NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP008Factor2654 * embedPair2542
      batchN02703MinusP008Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP008Factor2654, batchN02703MinusP008Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP008Factor2654 * embedPair2542 batchN02703MinusP008Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP008DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP008Factor2654, batchN02703MinusP008Error2654,
      batchC02703MinusLeftP008NormUpper2654]

noncomputable def batchC02703MinusLeftP009NormUpper2654 : ℝ := ((62548524404707843897 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP009NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02703MinusPosition2654‖ ≤
      batchC02703MinusLeftP009NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP009Factor2654 * embedPair2542
      batchN02703MinusP009Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP009Factor2654, batchN02703MinusP009Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP009Factor2654 * embedPair2542 batchN02703MinusP009Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP009DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP009Factor2654, batchN02703MinusP009Error2654,
      batchC02703MinusLeftP009NormUpper2654]

noncomputable def batchC02703MinusLeftP010NormUpper2654 : ℝ := ((31274381002373049249 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703MinusLeftP010NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP010NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP010Factor2654 * embedPair2542
      batchN02703MinusP010Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP010Factor2654, batchN02703MinusP010Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP010Factor2654 * embedPair2542 batchN02703MinusP010Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP010DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP010Factor2654, batchN02703MinusP010Error2654,
      batchC02703MinusLeftP010NormUpper2654]

noncomputable def batchC02703MinusLeftP011NormUpper2654 : ℝ := ((31274460209735633085 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703MinusLeftP011NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP011NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP011Factor2654 * embedPair2542
      batchN02703MinusP011Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP011Factor2654, batchN02703MinusP011Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP011Factor2654 * embedPair2542 batchN02703MinusP011Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP011DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP011Factor2654, batchN02703MinusP011Error2654,
      batchC02703MinusLeftP011NormUpper2654]

noncomputable def batchC02703MinusLeftP012NormUpper2654 : ℝ := ((62549084498074514671 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP012NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP012NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP012Factor2654 * embedPair2542
      batchN02703MinusP012Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP012Factor2654, batchN02703MinusP012Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP012Factor2654 * embedPair2542 batchN02703MinusP012Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP012DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP012Factor2654, batchN02703MinusP012Error2654,
      batchC02703MinusLeftP012NormUpper2654]

noncomputable def batchC02703MinusLeftP013NormUpper2654 : ℝ := ((31274617010143226857 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703MinusLeftP013NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP013NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP013Factor2654 * embedPair2542
      batchN02703MinusP013Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP013Factor2654, batchN02703MinusP013Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP013Factor2654 * embedPair2542 batchN02703MinusP013Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP013DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP013Factor2654, batchN02703MinusP013Error2654,
      batchC02703MinusLeftP013NormUpper2654]

noncomputable def batchC02703MinusLeftP014NormUpper2654 : ℝ := ((7818688883625195405 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem batchC02703MinusLeftP014NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP014NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP014Factor2654 * embedPair2542
      batchN02703MinusP014Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP014Factor2654, batchN02703MinusP014Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP014Factor2654 * embedPair2542 batchN02703MinusP014Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP014DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP014Factor2654, batchN02703MinusP014Error2654,
      batchC02703MinusLeftP014NormUpper2654]

noncomputable def batchC02703MinusLeftP015NormUpper2654 : ℝ := ((62549709574845843127 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP015NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP015NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP015Factor2654 * embedPair2542
      batchN02703MinusP015Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP015Factor2654, batchN02703MinusP015Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP015Factor2654 * embedPair2542 batchN02703MinusP015Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP015DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP015Factor2654, batchN02703MinusP015Error2654,
      batchC02703MinusLeftP015NormUpper2654]

noncomputable def batchC02703MinusLeftP016NormUpper2654 : ℝ := ((3909365814400589361 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

theorem batchC02703MinusLeftP016NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP016NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP016Factor2654 * embedPair2542
      batchN02703MinusP016Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP016Factor2654, batchN02703MinusP016Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP016Factor2654 * embedPair2542 batchN02703MinusP016Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP016DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP016Factor2654, batchN02703MinusP016Error2654,
      batchC02703MinusLeftP016NormUpper2654]

noncomputable def batchC02703MinusLeftP017NormUpper2654 : ℝ := ((15637532920811569919 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02703MinusLeftP017NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP017NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP017Factor2654 * embedPair2542
      batchN02703MinusP017Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP017Factor2654, batchN02703MinusP017Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP017Factor2654 * embedPair2542 batchN02703MinusP017Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP017DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP017Factor2654, batchN02703MinusP017Error2654,
      batchC02703MinusLeftP017NormUpper2654]

noncomputable def batchC02703MinusLeftP018NormUpper2654 : ℝ := ((31275118517869447971 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703MinusLeftP018NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP018NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP018Factor2654 * embedPair2542
      batchN02703MinusP018Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP018Factor2654, batchN02703MinusP018Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP018Factor2654 * embedPair2542 batchN02703MinusP018Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP018DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP018Factor2654, batchN02703MinusP018Error2654,
      batchC02703MinusLeftP018NormUpper2654]

noncomputable def batchC02703MinusLeftP019NormUpper2654 : ℝ := ((62550427436065163143 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP019NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP019NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP019Factor2654 * embedPair2542
      batchN02703MinusP019Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP019Factor2654, batchN02703MinusP019Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP019Factor2654 * embedPair2542 batchN02703MinusP019Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP019DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP019Factor2654, batchN02703MinusP019Error2654,
      batchC02703MinusLeftP019NormUpper2654]

noncomputable def batchC02703MinusLeftP020NormUpper2654 : ℝ := ((15637658620189608797 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02703MinusLeftP020NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP020NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP020Factor2654 * embedPair2542
      batchN02703MinusP020Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP020Factor2654, batchN02703MinusP020Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP020Factor2654 * embedPair2542 batchN02703MinusP020Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP020DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP020Factor2654, batchN02703MinusP020Error2654,
      batchC02703MinusLeftP020NormUpper2654]

noncomputable def batchC02703MinusLeftP021NormUpper2654 : ℝ := ((31275403633649352445 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703MinusLeftP021NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP021NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP021Factor2654 * embedPair2542
      batchN02703MinusP021Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP021Factor2654, batchN02703MinusP021Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP021Factor2654 * embedPair2542 batchN02703MinusP021Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP021DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP021Factor2654, batchN02703MinusP021Error2654,
      batchC02703MinusLeftP021NormUpper2654]

noncomputable def batchC02703MinusLeftP022NormUpper2654 : ℝ := ((62550895705698763679 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP022NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP022NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP022Factor2654 * embedPair2542
      batchN02703MinusP022Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP022Factor2654, batchN02703MinusP022Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP022Factor2654 * embedPair2542 batchN02703MinusP022Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP022DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP022Factor2654, batchN02703MinusP022Error2654,
      batchC02703MinusLeftP022NormUpper2654]

noncomputable def batchC02703MinusLeftP023NormUpper2654 : ℝ := ((62551150689573303751 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP023NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP023NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP023Factor2654 * embedPair2542
      batchN02703MinusP023Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP023Factor2654, batchN02703MinusP023Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP023Factor2654 * embedPair2542 batchN02703MinusP023Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP023DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP023Factor2654, batchN02703MinusP023Error2654,
      batchC02703MinusLeftP023NormUpper2654]

noncomputable def batchC02703MinusLeftP024NormUpper2654 : ℝ := ((62551267869603860077 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP024NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP024NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP024Factor2654 * embedPair2542
      batchN02703MinusP024Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP024Factor2654, batchN02703MinusP024Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP024Factor2654 * embedPair2542 batchN02703MinusP024Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP024DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP024Factor2654, batchN02703MinusP024Error2654,
      batchC02703MinusLeftP024NormUpper2654]

noncomputable def batchC02703MinusLeftP025NormUpper2654 : ℝ := ((15637853697913326075 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02703MinusLeftP025NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP025NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP025Factor2654 * embedPair2542
      batchN02703MinusP025Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP025Factor2654, batchN02703MinusP025Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP025Factor2654 * embedPair2542 batchN02703MinusP025Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP025DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP025Factor2654, batchN02703MinusP025Error2654,
      batchC02703MinusLeftP025NormUpper2654]

noncomputable def batchC02703MinusLeftP026NormUpper2654 : ℝ := ((15637891234945073015 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02703MinusLeftP026NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP026NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP026Factor2654 * embedPair2542
      batchN02703MinusP026Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP026Factor2654, batchN02703MinusP026Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP026Factor2654 * embedPair2542 batchN02703MinusP026Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP026DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP026Factor2654, batchN02703MinusP026Error2654,
      batchC02703MinusLeftP026NormUpper2654]

noncomputable def batchC02703MinusLeftP027NormUpper2654 : ℝ := ((62551781607998403245 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP027NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP027NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP027Factor2654 * embedPair2542
      batchN02703MinusP027Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP027Factor2654, batchN02703MinusP027Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP027Factor2654 * embedPair2542 batchN02703MinusP027Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP027DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP027Factor2654, batchN02703MinusP027Error2654,
      batchC02703MinusLeftP027NormUpper2654]

noncomputable def batchC02703MinusLeftP028NormUpper2654 : ℝ := ((62551867389788624171 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP028NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP028NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP028Factor2654 * embedPair2542
      batchN02703MinusP028Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP028Factor2654, batchN02703MinusP028Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP028Factor2654 * embedPair2542 batchN02703MinusP028Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP028DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP028Factor2654, batchN02703MinusP028Error2654,
      batchC02703MinusLeftP028NormUpper2654]

noncomputable def batchC02703MinusLeftP029NormUpper2654 : ℝ := ((62551997986906063319 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703MinusLeftP029NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02703MinusPosition2654‖
        ≤
      batchC02703MinusLeftP029NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703MinusP029Factor2654 * embedPair2542
      batchN02703MinusP029Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703MinusP029Factor2654, batchN02703MinusP029Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02703MinusPosition2654)
    (embedPair2542 batchN02703MinusP029Factor2654 * embedPair2542 batchN02703MinusP029Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703MinusP029DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703MinusP029Factor2654, batchN02703MinusP029Error2654,
      batchC02703MinusLeftP029NormUpper2654]

noncomputable def batchC02703MinusLeftNormUpper2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02703MinusLeftP000NormUpper2654
  | 1 => batchC02703MinusLeftP001NormUpper2654
  | 2 => batchC02703MinusLeftP002NormUpper2654
  | 3 => batchC02703MinusLeftP003NormUpper2654
  | 4 => batchC02703MinusLeftP004NormUpper2654
  | 5 => batchC02703MinusLeftP005NormUpper2654
  | 6 => batchC02703MinusLeftP006NormUpper2654
  | 7 => batchC02703MinusLeftP007NormUpper2654
  | 8 => batchC02703MinusLeftP008NormUpper2654
  | 9 => batchC02703MinusLeftP009NormUpper2654
  | 10 => batchC02703MinusLeftP010NormUpper2654
  | 11 => batchC02703MinusLeftP011NormUpper2654
  | 12 => batchC02703MinusLeftP012NormUpper2654
  | 13 => batchC02703MinusLeftP013NormUpper2654
  | 14 => batchC02703MinusLeftP014NormUpper2654
  | 15 => batchC02703MinusLeftP015NormUpper2654
  | 16 => batchC02703MinusLeftP016NormUpper2654
  | 17 => batchC02703MinusLeftP017NormUpper2654
  | 18 => batchC02703MinusLeftP018NormUpper2654
  | 19 => batchC02703MinusLeftP019NormUpper2654
  | 20 => batchC02703MinusLeftP020NormUpper2654
  | 21 => batchC02703MinusLeftP021NormUpper2654
  | 22 => batchC02703MinusLeftP022NormUpper2654
  | 23 => batchC02703MinusLeftP023NormUpper2654
  | 24 => batchC02703MinusLeftP024NormUpper2654
  | 25 => batchC02703MinusLeftP025NormUpper2654
  | 26 => batchC02703MinusLeftP026NormUpper2654
  | 27 => batchC02703MinusLeftP027NormUpper2654
  | 28 => batchC02703MinusLeftP028NormUpper2654
  | 29 => batchC02703MinusLeftP029NormUpper2654
  | _ => 0

theorem batchC02703MinusLeftNormBound2654 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 i batchN02703MinusPosition2654‖ ≤
        batchC02703MinusLeftNormUpper2654 i := by
  fin_cases i
  · exact batchC02703MinusLeftP000NormBound2654
  · exact batchC02703MinusLeftP001NormBound2654
  · exact batchC02703MinusLeftP002NormBound2654
  · exact batchC02703MinusLeftP003NormBound2654
  · exact batchC02703MinusLeftP004NormBound2654
  · exact batchC02703MinusLeftP005NormBound2654
  · exact batchC02703MinusLeftP006NormBound2654
  · exact batchC02703MinusLeftP007NormBound2654
  · exact batchC02703MinusLeftP008NormBound2654
  · exact batchC02703MinusLeftP009NormBound2654
  · exact batchC02703MinusLeftP010NormBound2654
  · exact batchC02703MinusLeftP011NormBound2654
  · exact batchC02703MinusLeftP012NormBound2654
  · exact batchC02703MinusLeftP013NormBound2654
  · exact batchC02703MinusLeftP014NormBound2654
  · exact batchC02703MinusLeftP015NormBound2654
  · exact batchC02703MinusLeftP016NormBound2654
  · exact batchC02703MinusLeftP017NormBound2654
  · exact batchC02703MinusLeftP018NormBound2654
  · exact batchC02703MinusLeftP019NormBound2654
  · exact batchC02703MinusLeftP020NormBound2654
  · exact batchC02703MinusLeftP021NormBound2654
  · exact batchC02703MinusLeftP022NormBound2654
  · exact batchC02703MinusLeftP023NormBound2654
  · exact batchC02703MinusLeftP024NormBound2654
  · exact batchC02703MinusLeftP025NormBound2654
  · exact batchC02703MinusLeftP026NormBound2654
  · exact batchC02703MinusLeftP027NormBound2654
  · exact batchC02703MinusLeftP028NormBound2654
  · exact batchC02703MinusLeftP029NormBound2654

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP000NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP001NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP002NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP003NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP004NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP005NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP006NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP007NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP008NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP009NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP010NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP011NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP012NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP013NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP014NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP015NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP016NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP017NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP018NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP019NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP020NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP021NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP022NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP023NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP024NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP025NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP026NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP027NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP028NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusLeftP029NormBound2654
