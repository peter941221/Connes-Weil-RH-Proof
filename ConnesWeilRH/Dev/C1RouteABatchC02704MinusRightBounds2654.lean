import ConnesWeilRH.Dev.C1RouteABatchN02705Minus2654
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC02704MinusRightP000NormUpper2654 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP000NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02705MinusPosition2654‖ ≤
      batchC02704MinusRightP000NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP000Factor2654 * embedPair2542
      batchN02705MinusP000Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP000Factor2654, batchN02705MinusP000Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP000Factor2654 * embedPair2542 batchN02705MinusP000Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP000DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP000Factor2654, batchN02705MinusP000Error2654,
      batchC02704MinusRightP000NormUpper2654]

noncomputable def batchC02704MinusRightP001NormUpper2654 : ℝ := ((652744187 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP001NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02705MinusPosition2654‖ ≤
      batchC02704MinusRightP001NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP001Factor2654 * embedPair2542
      batchN02705MinusP001Center2654‖ ≤
      ((193872659 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP001Factor2654, batchN02705MinusP001Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP001Factor2654 * embedPair2542 batchN02705MinusP001Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP001DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP001Factor2654, batchN02705MinusP001Error2654,
      batchC02704MinusRightP001NormUpper2654]

noncomputable def batchC02704MinusRightP002NormUpper2654 : ℝ := ((752103438428176982519755357 : ℝ)
    /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02704MinusRightP002NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02705MinusPosition2654‖ ≤
      batchC02704MinusRightP002NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP002Factor2654 * embedPair2542
      batchN02705MinusP002Center2654‖ ≤
      ((752103438428173345999060647 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP002Factor2654, batchN02705MinusP002Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP002Factor2654 * embedPair2542 batchN02705MinusP002Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP002DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP002Factor2654, batchN02705MinusP002Error2654,
      batchC02704MinusRightP002NormUpper2654]

noncomputable def batchC02704MinusRightP003NormUpper2654 : ℝ :=
    ((18183682128209080528580333678024885 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP003NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02705MinusPosition2654‖ ≤
      batchC02704MinusRightP003NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP003Factor2654 * embedPair2542
      batchN02705MinusP003Center2654‖ ≤
      ((18183682128208999932089818361679305 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP003Factor2654, batchN02705MinusP003Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP003Factor2654 * embedPair2542 batchN02705MinusP003Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP003DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP003Factor2654, batchN02705MinusP003Error2654,
      batchC02704MinusRightP003NormUpper2654]

noncomputable def batchC02704MinusRightP004NormUpper2654 : ℝ :=
    ((7636809322627998825620669691665160715 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP004NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02705MinusPosition2654‖ ≤
      batchC02704MinusRightP004NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP004Factor2654 * embedPair2542
      batchN02705MinusP004Center2654‖ ≤
      ((7636809322627966402334517906666761201 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP004Factor2654, batchN02705MinusP004Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP004Factor2654 * embedPair2542 batchN02705MinusP004Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP004DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP004Factor2654, batchN02705MinusP004Error2654,
      batchC02704MinusRightP004NormUpper2654]

noncomputable def batchC02704MinusRightP005NormUpper2654 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP005NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02705MinusPosition2654‖ ≤
      batchC02704MinusRightP005NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP005Factor2654 * embedPair2542
      batchN02705MinusP005Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP005Factor2654, batchN02705MinusP005Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP005Factor2654 * embedPair2542 batchN02705MinusP005Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP005DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP005Factor2654, batchN02705MinusP005Error2654,
      batchC02704MinusRightP005NormUpper2654]

noncomputable def batchC02704MinusRightP006NormUpper2654 : ℝ := ((9973167728007414374729 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP006NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02705MinusPosition2654‖ ≤
      batchC02704MinusRightP006NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP006Factor2654 * embedPair2542
      batchN02705MinusP006Center2654‖ ≤
      ((9973167728007411470569 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP006Factor2654, batchN02705MinusP006Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP006Factor2654 * embedPair2542 batchN02705MinusP006Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP006DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP006Factor2654, batchN02705MinusP006Error2654,
      batchC02704MinusRightP006NormUpper2654]

noncomputable def batchC02704MinusRightP007NormUpper2654 : ℝ :=
    ((254962208314464747905036266482923 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02704MinusRightP007NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02705MinusPosition2654‖ ≤
      batchC02704MinusRightP007NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP007Factor2654 * embedPair2542
      batchN02705MinusP007Center2654‖ ≤
      ((254962208314464715846863778939041 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP007Factor2654, batchN02705MinusP007Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP007Factor2654 * embedPair2542 batchN02705MinusP007Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP007DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP007Factor2654, batchN02705MinusP007Error2654,
      batchC02704MinusRightP007NormUpper2654]

noncomputable def batchC02704MinusRightP008NormUpper2654 : ℝ := ((2917255027854638069 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP008NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02705MinusPosition2654‖ ≤
      batchC02704MinusRightP008NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP008Factor2654 * embedPair2542
      batchN02705MinusP008Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP008Factor2654, batchN02705MinusP008Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP008Factor2654 * embedPair2542 batchN02705MinusP008Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP008DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP008Factor2654, batchN02705MinusP008Error2654,
      batchC02704MinusRightP008NormUpper2654]

noncomputable def batchC02704MinusRightP009NormUpper2654 : ℝ := ((1458654094408236017 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02704MinusRightP009NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02705MinusPosition2654‖ ≤
      batchC02704MinusRightP009NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP009Factor2654 * embedPair2542
      batchN02705MinusP009Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP009Factor2654, batchN02705MinusP009Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP009Factor2654 * embedPair2542 batchN02705MinusP009Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP009DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP009Factor2654, batchN02705MinusP009Error2654,
      batchC02704MinusRightP009NormUpper2654]

noncomputable def batchC02704MinusRightP010NormUpper2654 : ℝ := ((2917338976921867973 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP010NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP010NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP010Factor2654 * embedPair2542
      batchN02705MinusP010Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP010Factor2654, batchN02705MinusP010Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP010Factor2654 * embedPair2542 batchN02705MinusP010Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP010DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP010Factor2654, batchN02705MinusP010Error2654,
      batchC02704MinusRightP010NormUpper2654]

noncomputable def batchC02704MinusRightP011NormUpper2654 : ℝ := ((1458679752076606813 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02704MinusRightP011NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP011NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP011Factor2654 * embedPair2542
      batchN02705MinusP011Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP011Factor2654, batchN02705MinusP011Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP011Factor2654 * embedPair2542 batchN02705MinusP011Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP011DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP011Factor2654, batchN02705MinusP011Error2654,
      batchC02704MinusRightP011NormUpper2654]

noncomputable def batchC02704MinusRightP012NormUpper2654 : ℝ := ((1458690382619796253 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02704MinusRightP012NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP012NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP012Factor2654 * embedPair2542
      batchN02705MinusP012Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP012Factor2654, batchN02705MinusP012Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP012Factor2654 * embedPair2542 batchN02705MinusP012Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP012DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP012Factor2654, batchN02705MinusP012Error2654,
      batchC02704MinusRightP012NormUpper2654]

noncomputable def batchC02704MinusRightP013NormUpper2654 : ℝ := ((2917400140070642533 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP013NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP013NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP013Factor2654 * embedPair2542
      batchN02705MinusP013Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP013Factor2654, batchN02705MinusP013Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP013Factor2654 * embedPair2542 batchN02705MinusP013Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP013DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP013Factor2654, batchN02705MinusP013Error2654,
      batchC02704MinusRightP013NormUpper2654]

noncomputable def batchC02704MinusRightP014NormUpper2654 : ℝ := ((1458718019710760889 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02704MinusRightP014NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP014NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP014Factor2654 * embedPair2542
      batchN02705MinusP014Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP014Factor2654, batchN02705MinusP014Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP014Factor2654 * embedPair2542 batchN02705MinusP014Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP014DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP014Factor2654, batchN02705MinusP014Error2654,
      batchC02704MinusRightP014NormUpper2654]

noncomputable def batchC02704MinusRightP015NormUpper2654 : ℝ := ((1458730880623758097 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02704MinusRightP015NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP015NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP015Factor2654 * embedPair2542
      batchN02705MinusP015Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP015Factor2654, batchN02705MinusP015Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP015Factor2654 * embedPair2542 batchN02705MinusP015Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP015DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP015Factor2654, batchN02705MinusP015Error2654,
      batchC02704MinusRightP015NormUpper2654]

noncomputable def batchC02704MinusRightP016NormUpper2654 : ℝ := ((364685043719195761 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem batchC02704MinusRightP016NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP016NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP016Factor2654 * embedPair2542
      batchN02705MinusP016Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP016Factor2654, batchN02705MinusP016Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP016Factor2654 * embedPair2542 batchN02705MinusP016Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP016DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP016Factor2654, batchN02705MinusP016Error2654,
      batchC02704MinusRightP016NormUpper2654]

noncomputable def batchC02704MinusRightP017NormUpper2654 : ℝ := ((364689557067349569 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem batchC02704MinusRightP017NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP017NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP017Factor2654 * embedPair2542
      batchN02705MinusP017Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP017Factor2654, batchN02705MinusP017Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP017Factor2654 * embedPair2542 batchN02705MinusP017Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP017DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP017Factor2654, batchN02705MinusP017Error2654,
      batchC02704MinusRightP017NormUpper2654]

noncomputable def batchC02704MinusRightP018NormUpper2654 : ℝ := ((2917530107668370119 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP018NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP018NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP018Factor2654 * embedPair2542
      batchN02705MinusP018Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP018Factor2654, batchN02705MinusP018Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP018Factor2654 * embedPair2542 batchN02705MinusP018Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP018DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP018Factor2654, batchN02705MinusP018Error2654,
      batchC02704MinusRightP018NormUpper2654]

noncomputable def batchC02704MinusRightP019NormUpper2654 : ℝ := ((364694347358337599 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem batchC02704MinusRightP019NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP019NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP019Factor2654 * embedPair2542
      batchN02705MinusP019Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP019Factor2654, batchN02705MinusP019Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP019Factor2654 * embedPair2542 batchN02705MinusP019Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP019DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP019Factor2654, batchN02705MinusP019Error2654,
      batchC02704MinusRightP019NormUpper2654]

noncomputable def batchC02704MinusRightP020NormUpper2654 : ℝ := ((1458790803332244383 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02704MinusRightP020NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP020NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP020Factor2654 * embedPair2542
      batchN02705MinusP020Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP020Factor2654, batchN02705MinusP020Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP020Factor2654 * embedPair2542 batchN02705MinusP020Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP020DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP020Factor2654, batchN02705MinusP020Error2654,
      batchC02704MinusRightP020NormUpper2654]

noncomputable def batchC02704MinusRightP021NormUpper2654 : ℝ := ((2917603995384546287 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP021NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP021NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP021Factor2654 * embedPair2542
      batchN02705MinusP021Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP021Factor2654, batchN02705MinusP021Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP021Factor2654 * embedPair2542 batchN02705MinusP021Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP021DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP021Factor2654, batchN02705MinusP021Error2654,
      batchC02704MinusRightP021NormUpper2654]

noncomputable def batchC02704MinusRightP022NormUpper2654 : ℝ := ((2917615454712781091 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP022NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP022NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP022Factor2654 * embedPair2542
      batchN02705MinusP022Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP022Factor2654, batchN02705MinusP022Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP022Factor2654 * embedPair2542 batchN02705MinusP022Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP022DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP022Factor2654, batchN02705MinusP022Error2654,
      batchC02704MinusRightP022NormUpper2654]

noncomputable def batchC02704MinusRightP023NormUpper2654 : ℝ := ((2917648493917484009 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP023NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP023NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP023Factor2654 * embedPair2542
      batchN02705MinusP023Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP023Factor2654, batchN02705MinusP023Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP023Factor2654 * embedPair2542 batchN02705MinusP023Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP023DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP023Factor2654, batchN02705MinusP023Error2654,
      batchC02704MinusRightP023NormUpper2654]

noncomputable def batchC02704MinusRightP024NormUpper2654 : ℝ := ((2917663677314350109 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP024NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP024NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP024Factor2654 * embedPair2542
      batchN02705MinusP024Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP024Factor2654, batchN02705MinusP024Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP024Factor2654 * embedPair2542 batchN02705MinusP024Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP024DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP024Factor2654, batchN02705MinusP024Error2654,
      batchC02704MinusRightP024NormUpper2654]

noncomputable def batchC02704MinusRightP025NormUpper2654 : ℝ := ((1458841357216740923 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02704MinusRightP025NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP025NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP025Factor2654 * embedPair2542
      batchN02705MinusP025Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP025Factor2654, batchN02705MinusP025Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP025Factor2654 * embedPair2542 batchN02705MinusP025Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP025DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP025Factor2654, batchN02705MinusP025Error2654,
      batchC02704MinusRightP025NormUpper2654]

noncomputable def batchC02704MinusRightP026NormUpper2654 : ℝ := ((1458851084755065157 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02704MinusRightP026NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP026NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP026Factor2654 * embedPair2542
      batchN02705MinusP026Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP026Factor2654, batchN02705MinusP026Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP026Factor2654 * embedPair2542 batchN02705MinusP026Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP026DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP026Factor2654, batchN02705MinusP026Error2654,
      batchC02704MinusRightP026NormUpper2654]

noncomputable def batchC02704MinusRightP027NormUpper2654 : ℝ := ((2917730243667436367 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP027NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP027NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP027Factor2654 * embedPair2542
      batchN02705MinusP027Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP027Factor2654, batchN02705MinusP027Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP027Factor2654 * embedPair2542 batchN02705MinusP027Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP027DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP027Factor2654, batchN02705MinusP027Error2654,
      batchC02704MinusRightP027NormUpper2654]

noncomputable def batchC02704MinusRightP028NormUpper2654 : ℝ := ((1458870679281391969 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02704MinusRightP028NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP028NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP028Factor2654 * embedPair2542
      batchN02705MinusP028Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP028Factor2654, batchN02705MinusP028Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP028Factor2654 * embedPair2542 batchN02705MinusP028Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP028DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP028Factor2654, batchN02705MinusP028Error2654,
      batchC02704MinusRightP028NormUpper2654]

noncomputable def batchC02704MinusRightP029NormUpper2654 : ℝ := ((2917758280223109091 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02704MinusRightP029NormBound2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02705MinusPosition2654‖
        ≤
      batchC02704MinusRightP029NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02705MinusP029Factor2654 * embedPair2542
      batchN02705MinusP029Center2654‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02705MinusP029Factor2654, batchN02705MinusP029Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02705MinusPosition2654)
    (embedPair2542 batchN02705MinusP029Factor2654 * embedPair2542 batchN02705MinusP029Center2654)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02705MinusP029DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02705MinusP029Factor2654, batchN02705MinusP029Error2654,
      batchC02704MinusRightP029NormUpper2654]

noncomputable def batchC02704MinusRightNormUpper2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02704MinusRightP000NormUpper2654
  | 1 => batchC02704MinusRightP001NormUpper2654
  | 2 => batchC02704MinusRightP002NormUpper2654
  | 3 => batchC02704MinusRightP003NormUpper2654
  | 4 => batchC02704MinusRightP004NormUpper2654
  | 5 => batchC02704MinusRightP005NormUpper2654
  | 6 => batchC02704MinusRightP006NormUpper2654
  | 7 => batchC02704MinusRightP007NormUpper2654
  | 8 => batchC02704MinusRightP008NormUpper2654
  | 9 => batchC02704MinusRightP009NormUpper2654
  | 10 => batchC02704MinusRightP010NormUpper2654
  | 11 => batchC02704MinusRightP011NormUpper2654
  | 12 => batchC02704MinusRightP012NormUpper2654
  | 13 => batchC02704MinusRightP013NormUpper2654
  | 14 => batchC02704MinusRightP014NormUpper2654
  | 15 => batchC02704MinusRightP015NormUpper2654
  | 16 => batchC02704MinusRightP016NormUpper2654
  | 17 => batchC02704MinusRightP017NormUpper2654
  | 18 => batchC02704MinusRightP018NormUpper2654
  | 19 => batchC02704MinusRightP019NormUpper2654
  | 20 => batchC02704MinusRightP020NormUpper2654
  | 21 => batchC02704MinusRightP021NormUpper2654
  | 22 => batchC02704MinusRightP022NormUpper2654
  | 23 => batchC02704MinusRightP023NormUpper2654
  | 24 => batchC02704MinusRightP024NormUpper2654
  | 25 => batchC02704MinusRightP025NormUpper2654
  | 26 => batchC02704MinusRightP026NormUpper2654
  | 27 => batchC02704MinusRightP027NormUpper2654
  | 28 => batchC02704MinusRightP028NormUpper2654
  | 29 => batchC02704MinusRightP029NormUpper2654
  | _ => 0

theorem batchC02704MinusRightNormBound2654 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 i batchN02705MinusPosition2654‖ ≤
        batchC02704MinusRightNormUpper2654 i := by
  fin_cases i
  · exact batchC02704MinusRightP000NormBound2654
  · exact batchC02704MinusRightP001NormBound2654
  · exact batchC02704MinusRightP002NormBound2654
  · exact batchC02704MinusRightP003NormBound2654
  · exact batchC02704MinusRightP004NormBound2654
  · exact batchC02704MinusRightP005NormBound2654
  · exact batchC02704MinusRightP006NormBound2654
  · exact batchC02704MinusRightP007NormBound2654
  · exact batchC02704MinusRightP008NormBound2654
  · exact batchC02704MinusRightP009NormBound2654
  · exact batchC02704MinusRightP010NormBound2654
  · exact batchC02704MinusRightP011NormBound2654
  · exact batchC02704MinusRightP012NormBound2654
  · exact batchC02704MinusRightP013NormBound2654
  · exact batchC02704MinusRightP014NormBound2654
  · exact batchC02704MinusRightP015NormBound2654
  · exact batchC02704MinusRightP016NormBound2654
  · exact batchC02704MinusRightP017NormBound2654
  · exact batchC02704MinusRightP018NormBound2654
  · exact batchC02704MinusRightP019NormBound2654
  · exact batchC02704MinusRightP020NormBound2654
  · exact batchC02704MinusRightP021NormBound2654
  · exact batchC02704MinusRightP022NormBound2654
  · exact batchC02704MinusRightP023NormBound2654
  · exact batchC02704MinusRightP024NormBound2654
  · exact batchC02704MinusRightP025NormBound2654
  · exact batchC02704MinusRightP026NormBound2654
  · exact batchC02704MinusRightP027NormBound2654
  · exact batchC02704MinusRightP028NormBound2654
  · exact batchC02704MinusRightP029NormBound2654

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP000NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP001NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP002NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP003NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP004NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP005NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP006NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP007NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP008NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP009NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP010NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP011NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP012NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP013NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP014NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP015NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP016NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP017NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP018NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP019NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP020NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP021NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP022NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP023NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP024NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP025NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP026NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP027NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP028NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusRightP029NormBound2654
