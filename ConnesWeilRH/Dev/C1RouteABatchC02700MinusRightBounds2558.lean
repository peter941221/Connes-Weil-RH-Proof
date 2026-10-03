import ConnesWeilRH.Dev.C1RouteAKernelN02701Minus2555
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC02700MinusRightP000NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusRightP000NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP000NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP000Factor2555 * embedPair2542
      kernelN02701MinusP000Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP000Factor2555, kernelN02701MinusP000Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP000Factor2555 * embedPair2542
        kernelN02701MinusP000Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP000DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP000Factor2555, kernelN02701MinusP000Error2555,
      batchC02700MinusRightP000NormUpper2558]

noncomputable def batchC02700MinusRightP001NormUpper2558 : ℝ := ((361556499 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700MinusRightP001NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP001NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP001Factor2555 * embedPair2542
      kernelN02701MinusP001Center2555‖ ≤
      ((13468069 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP001Factor2555, kernelN02701MinusP001Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP001Factor2555 * embedPair2542
        kernelN02701MinusP001Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP001DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP001Factor2555, kernelN02701MinusP001Error2555,
      batchC02700MinusRightP001NormUpper2558]

noncomputable def batchC02700MinusRightP002NormUpper2558 : ℝ := ((1235199423550871437752229825 :
    ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700MinusRightP002NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP002NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP002Factor2555 * embedPair2542
      kernelN02701MinusP002Center2555‖ ≤
      ((1235199423550865593208927009 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP002Factor2555, kernelN02701MinusP002Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP002Factor2555 * embedPair2542
        kernelN02701MinusP002Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP002DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP002Factor2555, kernelN02701MinusP002Error2555,
      batchC02700MinusRightP002NormUpper2558]

noncomputable def batchC02700MinusRightP003NormUpper2558 : ℝ :=
    ((8486739226906453819719853226206563 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700MinusRightP003NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP003NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP003Factor2555 * embedPair2542
      kernelN02701MinusP003Center2555‖ ≤
      ((8486739226906417064474299634720581 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP003Factor2555, kernelN02701MinusP003Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP003Factor2555 * embedPair2542
        kernelN02701MinusP003Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP003DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP003Factor2555, kernelN02701MinusP003Error2555,
      batchC02700MinusRightP003NormUpper2558]

noncomputable def batchC02700MinusRightP004NormUpper2558 : ℝ :=
    ((7383533733095679986401782506841343267 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusRightP004NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP004NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP004Factor2555 * embedPair2542
      kernelN02701MinusP004Center2555‖ ≤
      ((7383533733095649312714575643558095703 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP004Factor2555, kernelN02701MinusP004Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP004Factor2555 * embedPair2542
        kernelN02701MinusP004Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP004DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP004Factor2555, kernelN02701MinusP004Error2555,
      batchC02700MinusRightP004NormUpper2558]

noncomputable def batchC02700MinusRightP005NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusRightP005NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP005NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP005Factor2555 * embedPair2542
      kernelN02701MinusP005Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP005Factor2555, kernelN02701MinusP005Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP005Factor2555 * embedPair2542
        kernelN02701MinusP005Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP005DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP005Factor2555, kernelN02701MinusP005Error2555,
      batchC02700MinusRightP005NormUpper2558]

noncomputable def batchC02700MinusRightP006NormUpper2558 : ℝ := ((7170097764641688865953 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusRightP006NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP006NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP006Factor2555 * embedPair2542
      kernelN02701MinusP006Center2555‖ ≤
      ((7170097764641686568149 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP006Factor2555, kernelN02701MinusP006Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP006Factor2555 * embedPair2542
        kernelN02701MinusP006Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP006DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP006Factor2555, kernelN02701MinusP006Error2555,
      batchC02700MinusRightP006NormUpper2558]

noncomputable def batchC02700MinusRightP007NormUpper2558 : ℝ :=
    ((482945556064872263286596431308083 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusRightP007NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP007NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP007Factor2555 * embedPair2542
      kernelN02701MinusP007Center2555‖ ≤
      ((482945556064872202495462727410123 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP007Factor2555, kernelN02701MinusP007Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP007Factor2555 * embedPair2542
        kernelN02701MinusP007Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP007DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP007Factor2555, kernelN02701MinusP007Error2555,
      batchC02700MinusRightP007NormUpper2558]

noncomputable def batchC02700MinusRightP008NormUpper2558 : ℝ := ((45618912747157703442083 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusRightP008NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP008NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP008Factor2555 * embedPair2542
      kernelN02701MinusP008Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP008Factor2555, kernelN02701MinusP008Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP008Factor2555 * embedPair2542
        kernelN02701MinusP008Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP008DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP008Factor2555, kernelN02701MinusP008Error2555,
      batchC02700MinusRightP008NormUpper2558]

noncomputable def batchC02700MinusRightP009NormUpper2558 : ℝ := ((45618945985096166062559 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusRightP009NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP009NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP009Factor2555 * embedPair2542
      kernelN02701MinusP009Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP009Factor2555, kernelN02701MinusP009Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP009Factor2555 * embedPair2542
        kernelN02701MinusP009Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP009DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP009Factor2555, kernelN02701MinusP009Error2555,
      batchC02700MinusRightP009NormUpper2558]

noncomputable def batchC02700MinusRightP010NormUpper2558 : ℝ := ((2851185327186526170463 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

theorem batchC02700MinusRightP010NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP010NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP010Factor2555 * embedPair2542
      kernelN02701MinusP010Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP010Factor2555, kernelN02701MinusP010Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP010Factor2555 * embedPair2542
        kernelN02701MinusP010Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP010DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP010Factor2555, kernelN02701MinusP010Error2555,
      batchC02700MinusRightP010NormUpper2558]

noncomputable def batchC02700MinusRightP011NormUpper2558 : ℝ := ((22809489034729133265767 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700MinusRightP011NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP011NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP011Factor2555 * embedPair2542
      kernelN02701MinusP011Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP011Factor2555, kernelN02701MinusP011Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP011Factor2555 * embedPair2542
        kernelN02701MinusP011Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP011DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP011Factor2555, kernelN02701MinusP011Error2555,
      batchC02700MinusRightP011NormUpper2558]

noncomputable def batchC02700MinusRightP012NormUpper2558 : ℝ := ((2851186960176847178915 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

theorem batchC02700MinusRightP012NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP012NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP012Factor2555 * embedPair2542
      kernelN02701MinusP012Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP012Factor2555, kernelN02701MinusP012Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP012Factor2555 * embedPair2542
        kernelN02701MinusP012Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP012DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP012Factor2555, kernelN02701MinusP012Error2555,
      batchC02700MinusRightP012NormUpper2558]

noncomputable def batchC02700MinusRightP013NormUpper2558 : ℝ := ((45619003476884601303229 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusRightP013NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP013NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP013Factor2555 * embedPair2542
      kernelN02701MinusP013Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP013Factor2555, kernelN02701MinusP013Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP013Factor2555 * embedPair2542
        kernelN02701MinusP013Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP013DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP013Factor2555, kernelN02701MinusP013Error2555,
      batchC02700MinusRightP013NormUpper2558]

noncomputable def batchC02700MinusRightP014NormUpper2558 : ℝ := ((45619025922982229339245 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusRightP014NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP014NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP014Factor2555 * embedPair2542
      kernelN02701MinusP014Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP014Factor2555, kernelN02701MinusP014Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP014Factor2555 * embedPair2542
        kernelN02701MinusP014Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP014DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP014Factor2555, kernelN02701MinusP014Error2555,
      batchC02700MinusRightP014NormUpper2558]

noncomputable def batchC02700MinusRightP015NormUpper2558 : ℝ := ((11404760501420761982733 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02700MinusRightP015NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP015NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP015Factor2555 * embedPair2542
      kernelN02701MinusP015Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP015Factor2555, kernelN02701MinusP015Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP015Factor2555 * embedPair2542
        kernelN02701MinusP015Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP015DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP015Factor2555, kernelN02701MinusP015Error2555,
      batchC02700MinusRightP015NormUpper2558]

noncomputable def batchC02700MinusRightP016NormUpper2558 : ℝ := ((22809526814148126619119 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700MinusRightP016NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP016NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP016Factor2555 * embedPair2542
      kernelN02701MinusP016Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP016Factor2555, kernelN02701MinusP016Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP016Factor2555 * embedPair2542
        kernelN02701MinusP016Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP016DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP016Factor2555, kernelN02701MinusP016Error2555,
      batchC02700MinusRightP016NormUpper2558]

noncomputable def batchC02700MinusRightP017NormUpper2558 : ℝ := ((712798065695158348613 : ℝ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984))

theorem batchC02700MinusRightP017NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP017NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP017Factor2555 * embedPair2542
      kernelN02701MinusP017Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP017Factor2555, kernelN02701MinusP017Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP017Factor2555 * embedPair2542
        kernelN02701MinusP017Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP017DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP017Factor2555, kernelN02701MinusP017Error2555,
      batchC02700MinusRightP017NormUpper2558]

noncomputable def batchC02700MinusRightP018NormUpper2558 : ℝ := ((45619084740066704802325 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusRightP018NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP018NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP018Factor2555 * embedPair2542
      kernelN02701MinusP018Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP018Factor2555, kernelN02701MinusP018Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP018Factor2555 * embedPair2542
        kernelN02701MinusP018Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP018DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP018Factor2555, kernelN02701MinusP018Error2555,
      batchC02700MinusRightP018NormUpper2558]

noncomputable def batchC02700MinusRightP019NormUpper2558 : ℝ := ((22809550083086932451073 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700MinusRightP019NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP019NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP019Factor2555 * embedPair2542
      kernelN02701MinusP019Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP019Factor2555, kernelN02701MinusP019Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP019Factor2555 * embedPair2542
        kernelN02701MinusP019Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP019DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP019Factor2555, kernelN02701MinusP019Error2555,
      batchC02700MinusRightP019NormUpper2558]

noncomputable def batchC02700MinusRightP020NormUpper2558 : ℝ := ((11404779235207023645841 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02700MinusRightP020NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP020NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP020Factor2555 * embedPair2542
      kernelN02701MinusP020Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP020Factor2555, kernelN02701MinusP020Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP020Factor2555 * embedPair2542
        kernelN02701MinusP020Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP020DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP020Factor2555, kernelN02701MinusP020Error2555,
      batchC02700MinusRightP020NormUpper2558]

noncomputable def batchC02700MinusRightP021NormUpper2558 : ℝ := ((22809565469964815092255 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700MinusRightP021NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP021NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP021Factor2555 * embedPair2542
      kernelN02701MinusP021Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP021Factor2555, kernelN02701MinusP021Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP021Factor2555 * embedPair2542
        kernelN02701MinusP021Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP021DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP021Factor2555, kernelN02701MinusP021Error2555,
      batchC02700MinusRightP021NormUpper2558]

noncomputable def batchC02700MinusRightP022NormUpper2558 : ℝ := ((22809569052592466874461 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700MinusRightP022NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP022NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP022Factor2555 * embedPair2542
      kernelN02701MinusP022Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP022Factor2555, kernelN02701MinusP022Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP022Factor2555 * embedPair2542
        kernelN02701MinusP022Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP022DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP022Factor2555, kernelN02701MinusP022Error2555,
      batchC02700MinusRightP022NormUpper2558]

noncomputable def batchC02700MinusRightP023NormUpper2558 : ℝ := ((45619158763943236990055 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusRightP023NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP023NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP023Factor2555 * embedPair2542
      kernelN02701MinusP023Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP023Factor2555, kernelN02701MinusP023Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP023Factor2555 * embedPair2542
        kernelN02701MinusP023Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP023DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP023Factor2555, kernelN02701MinusP023Error2555,
      batchC02700MinusRightP023NormUpper2558]

noncomputable def batchC02700MinusRightP024NormUpper2558 : ℝ := ((22809584128934933923209 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700MinusRightP024NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP024NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP024Factor2555 * embedPair2542
      kernelN02701MinusP024Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP024Factor2555, kernelN02701MinusP024Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP024Factor2555 * embedPair2542
        kernelN02701MinusP024Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP024DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP024Factor2555, kernelN02701MinusP024Error2555,
      batchC02700MinusRightP024NormUpper2558]

noncomputable def batchC02700MinusRightP025NormUpper2558 : ℝ := ((45619180161509901998743 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusRightP025NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP025NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP025Factor2555 * embedPair2542
      kernelN02701MinusP025Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP025Factor2555, kernelN02701MinusP025Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP025Factor2555 * embedPair2542
        kernelN02701MinusP025Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP025DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP025Factor2555, kernelN02701MinusP025Error2555,
      batchC02700MinusRightP025NormUpper2558]

noncomputable def batchC02700MinusRightP026NormUpper2558 : ℝ := ((45619192326544199992447 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusRightP026NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP026NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP026Factor2555 * embedPair2542
      kernelN02701MinusP026Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP026Factor2555, kernelN02701MinusP026Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP026Factor2555 * embedPair2542
        kernelN02701MinusP026Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP026DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP026Factor2555, kernelN02701MinusP026Error2555,
      batchC02700MinusRightP026NormUpper2558]

noncomputable def batchC02700MinusRightP027NormUpper2558 : ℝ := ((11404802470270356478591 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02700MinusRightP027NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP027NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP027Factor2555 * embedPair2542
      kernelN02701MinusP027Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP027Factor2555, kernelN02701MinusP027Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP027Factor2555 * embedPair2542
        kernelN02701MinusP027Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP027DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP027Factor2555, kernelN02701MinusP027Error2555,
      batchC02700MinusRightP027NormUpper2558]

noncomputable def batchC02700MinusRightP028NormUpper2558 : ℝ := ((22809608415581492712393 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700MinusRightP028NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP028NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP028Factor2555 * embedPair2542
      kernelN02701MinusP028Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP028Factor2555, kernelN02701MinusP028Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP028Factor2555 * embedPair2542
        kernelN02701MinusP028Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP028DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP028Factor2555, kernelN02701MinusP028Error2555,
      batchC02700MinusRightP028NormUpper2558]

noncomputable def batchC02700MinusRightP029NormUpper2558 : ℝ := ((22809613706107288803771 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700MinusRightP029NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN02701MinusPosition2555‖
        ≤
      batchC02700MinusRightP029NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701MinusP029Factor2555 * embedPair2542
      kernelN02701MinusP029Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701MinusP029Factor2555, kernelN02701MinusP029Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN02701MinusPosition2555)
    (embedPair2542 kernelN02701MinusP029Factor2555 * embedPair2542
        kernelN02701MinusP029Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701MinusP029DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701MinusP029Factor2555, kernelN02701MinusP029Error2555,
      batchC02700MinusRightP029NormUpper2558]

noncomputable def batchC02700MinusRightNormUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02700MinusRightP000NormUpper2558
  | 1 => batchC02700MinusRightP001NormUpper2558
  | 2 => batchC02700MinusRightP002NormUpper2558
  | 3 => batchC02700MinusRightP003NormUpper2558
  | 4 => batchC02700MinusRightP004NormUpper2558
  | 5 => batchC02700MinusRightP005NormUpper2558
  | 6 => batchC02700MinusRightP006NormUpper2558
  | 7 => batchC02700MinusRightP007NormUpper2558
  | 8 => batchC02700MinusRightP008NormUpper2558
  | 9 => batchC02700MinusRightP009NormUpper2558
  | 10 => batchC02700MinusRightP010NormUpper2558
  | 11 => batchC02700MinusRightP011NormUpper2558
  | 12 => batchC02700MinusRightP012NormUpper2558
  | 13 => batchC02700MinusRightP013NormUpper2558
  | 14 => batchC02700MinusRightP014NormUpper2558
  | 15 => batchC02700MinusRightP015NormUpper2558
  | 16 => batchC02700MinusRightP016NormUpper2558
  | 17 => batchC02700MinusRightP017NormUpper2558
  | 18 => batchC02700MinusRightP018NormUpper2558
  | 19 => batchC02700MinusRightP019NormUpper2558
  | 20 => batchC02700MinusRightP020NormUpper2558
  | 21 => batchC02700MinusRightP021NormUpper2558
  | 22 => batchC02700MinusRightP022NormUpper2558
  | 23 => batchC02700MinusRightP023NormUpper2558
  | 24 => batchC02700MinusRightP024NormUpper2558
  | 25 => batchC02700MinusRightP025NormUpper2558
  | 26 => batchC02700MinusRightP026NormUpper2558
  | 27 => batchC02700MinusRightP027NormUpper2558
  | 28 => batchC02700MinusRightP028NormUpper2558
  | 29 => batchC02700MinusRightP029NormUpper2558
  | _ => 0

theorem batchC02700MinusRightNormBound2558 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 i kernelN02701MinusPosition2555‖ ≤
        batchC02700MinusRightNormUpper2558 i := by
  fin_cases i
  · exact batchC02700MinusRightP000NormBound2558
  · exact batchC02700MinusRightP001NormBound2558
  · exact batchC02700MinusRightP002NormBound2558
  · exact batchC02700MinusRightP003NormBound2558
  · exact batchC02700MinusRightP004NormBound2558
  · exact batchC02700MinusRightP005NormBound2558
  · exact batchC02700MinusRightP006NormBound2558
  · exact batchC02700MinusRightP007NormBound2558
  · exact batchC02700MinusRightP008NormBound2558
  · exact batchC02700MinusRightP009NormBound2558
  · exact batchC02700MinusRightP010NormBound2558
  · exact batchC02700MinusRightP011NormBound2558
  · exact batchC02700MinusRightP012NormBound2558
  · exact batchC02700MinusRightP013NormBound2558
  · exact batchC02700MinusRightP014NormBound2558
  · exact batchC02700MinusRightP015NormBound2558
  · exact batchC02700MinusRightP016NormBound2558
  · exact batchC02700MinusRightP017NormBound2558
  · exact batchC02700MinusRightP018NormBound2558
  · exact batchC02700MinusRightP019NormBound2558
  · exact batchC02700MinusRightP020NormBound2558
  · exact batchC02700MinusRightP021NormBound2558
  · exact batchC02700MinusRightP022NormBound2558
  · exact batchC02700MinusRightP023NormBound2558
  · exact batchC02700MinusRightP024NormBound2558
  · exact batchC02700MinusRightP025NormBound2558
  · exact batchC02700MinusRightP026NormBound2558
  · exact batchC02700MinusRightP027NormBound2558
  · exact batchC02700MinusRightP028NormBound2558
  · exact batchC02700MinusRightP029NormBound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP000NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP001NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP002NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP003NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP004NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP005NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP006NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP007NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP008NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP009NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP010NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP011NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP012NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP013NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP014NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP015NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP016NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP017NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP018NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP019NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP020NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP021NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP022NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP023NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP024NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP025NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP026NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP027NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP028NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusRightP029NormBound2558
