import ConnesWeilRH.Dev.C1RouteAKernelN02700Minus2555
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC02700MinusLeftP000NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP000NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP000NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP000Factor2555 * embedPair2542
      kernelN02700MinusP000Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP000Factor2555, kernelN02700MinusP000Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP000Factor2555 * embedPair2542
        kernelN02700MinusP000Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP000DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP000Factor2555, kernelN02700MinusP000Error2555,
      batchC02700MinusLeftP000NormUpper2558]

noncomputable def batchC02700MinusLeftP001NormUpper2558 : ℝ := ((742079873 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP001NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP001NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP001Factor2555 * embedPair2542
      kernelN02700MinusP001Center2555‖
      ≤
      ((110662455 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP001Factor2555, kernelN02700MinusP001Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP001Factor2555 * embedPair2542
        kernelN02700MinusP001Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP001DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP001Factor2555, kernelN02700MinusP001Error2555,
      batchC02700MinusLeftP001NormUpper2558]

noncomputable def batchC02700MinusLeftP002NormUpper2558 : ℝ := ((1175522530302986208558282339 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700MinusLeftP002NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP002NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP002Factor2555 * embedPair2542
      kernelN02700MinusP002Center2555‖
      ≤
      ((1175522530302980689054209511 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP002Factor2555, kernelN02700MinusP002Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP002Factor2555 * embedPair2542
        kernelN02700MinusP002Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP002DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP002Factor2555, kernelN02700MinusP002Error2555,
      batchC02700MinusLeftP002NormUpper2558]

noncomputable def batchC02700MinusLeftP003NormUpper2558 : ℝ :=
    ((16682833626079396861462566966003753 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP003NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP003NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP003Factor2555 * embedPair2542
      kernelN02700MinusP003Center2555‖
      ≤
      ((16682833626079325189788869235847613 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP003Factor2555, kernelN02700MinusP003Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP003Factor2555 * embedPair2542
        kernelN02700MinusP003Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP003DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP003Factor2555, kernelN02700MinusP003Error2555,
      batchC02700MinusLeftP003NormUpper2558]

noncomputable def batchC02700MinusLeftP004NormUpper2558 : ℝ :=
    ((1830348071931591951587199956100222069 :
    ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02700MinusLeftP004NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP004NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP004Factor2555 * embedPair2542
      kernelN02700MinusP004Center2555‖
      ≤
      ((7321392287726337624245258646892974185 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP004Factor2555, kernelN02700MinusP004Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP004Factor2555 * embedPair2542
        kernelN02700MinusP004Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP004DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP004Factor2555, kernelN02700MinusP004Error2555,
      batchC02700MinusLeftP004NormUpper2558]

noncomputable def batchC02700MinusLeftP005NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP005NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP005NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP005Factor2555 * embedPair2542
      kernelN02700MinusP005Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP005Factor2555, kernelN02700MinusP005Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP005Factor2555 * embedPair2542
        kernelN02700MinusP005Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP005DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP005Factor2555, kernelN02700MinusP005Error2555,
      batchC02700MinusLeftP005NormUpper2558]

noncomputable def batchC02700MinusLeftP006NormUpper2558 : ℝ := ((6598145902879392974635 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP006NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP006NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP006Factor2555 * embedPair2542
      kernelN02700MinusP006Center2555‖
      ≤
      ((1649536475719847699893 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP006Factor2555, kernelN02700MinusP006Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP006Factor2555 * embedPair2542
        kernelN02700MinusP006Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP006DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP006Factor2555, kernelN02700MinusP006Error2555,
      batchC02700MinusLeftP006NormUpper2558]

noncomputable def batchC02700MinusLeftP007NormUpper2558 : ℝ := ((476401352090970615276070840427495
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP007NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP007NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP007Factor2555 * embedPair2542
      kernelN02700MinusP007Center2555‖
      ≤
      ((476401352090970555292099421596639 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP007Factor2555, kernelN02700MinusP007Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP007Factor2555 * embedPair2542
        kernelN02700MinusP007Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP007DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP007Factor2555, kernelN02700MinusP007Error2555,
      batchC02700MinusLeftP007NormUpper2558]

noncomputable def batchC02700MinusLeftP008NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP008NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP008NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP008Factor2555 * embedPair2542
      kernelN02700MinusP008Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP008Factor2555, kernelN02700MinusP008Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP008Factor2555 * embedPair2542
        kernelN02700MinusP008Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP008DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP008Factor2555, kernelN02700MinusP008Error2555,
      batchC02700MinusLeftP008NormUpper2558]

noncomputable def batchC02700MinusLeftP009NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP009NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP009NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP009Factor2555 * embedPair2542
      kernelN02700MinusP009Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP009Factor2555, kernelN02700MinusP009Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP009Factor2555 * embedPair2542
        kernelN02700MinusP009Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP009DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP009Factor2555, kernelN02700MinusP009Error2555,
      batchC02700MinusLeftP009NormUpper2558]

noncomputable def batchC02700MinusLeftP010NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP010NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP010NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP010Factor2555 * embedPair2542
      kernelN02700MinusP010Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP010Factor2555, kernelN02700MinusP010Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP010Factor2555 * embedPair2542
        kernelN02700MinusP010Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP010DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP010Factor2555, kernelN02700MinusP010Error2555,
      batchC02700MinusLeftP010NormUpper2558]

noncomputable def batchC02700MinusLeftP011NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP011NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP011NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP011Factor2555 * embedPair2542
      kernelN02700MinusP011Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP011Factor2555, kernelN02700MinusP011Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP011Factor2555 * embedPair2542
        kernelN02700MinusP011Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP011DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP011Factor2555, kernelN02700MinusP011Error2555,
      batchC02700MinusLeftP011NormUpper2558]

noncomputable def batchC02700MinusLeftP012NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP012NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP012NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP012Factor2555 * embedPair2542
      kernelN02700MinusP012Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP012Factor2555, kernelN02700MinusP012Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP012Factor2555 * embedPair2542
        kernelN02700MinusP012Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP012DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP012Factor2555, kernelN02700MinusP012Error2555,
      batchC02700MinusLeftP012NormUpper2558]

noncomputable def batchC02700MinusLeftP013NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP013NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP013NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP013Factor2555 * embedPair2542
      kernelN02700MinusP013Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP013Factor2555, kernelN02700MinusP013Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP013Factor2555 * embedPair2542
        kernelN02700MinusP013Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP013DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP013Factor2555, kernelN02700MinusP013Error2555,
      batchC02700MinusLeftP013NormUpper2558]

noncomputable def batchC02700MinusLeftP014NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP014NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP014NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP014Factor2555 * embedPair2542
      kernelN02700MinusP014Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP014Factor2555, kernelN02700MinusP014Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP014Factor2555 * embedPair2542
        kernelN02700MinusP014Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP014DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP014Factor2555, kernelN02700MinusP014Error2555,
      batchC02700MinusLeftP014NormUpper2558]

noncomputable def batchC02700MinusLeftP015NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP015NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP015NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP015Factor2555 * embedPair2542
      kernelN02700MinusP015Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP015Factor2555, kernelN02700MinusP015Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP015Factor2555 * embedPair2542
        kernelN02700MinusP015Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP015DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP015Factor2555, kernelN02700MinusP015Error2555,
      batchC02700MinusLeftP015NormUpper2558]

noncomputable def batchC02700MinusLeftP016NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP016NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP016NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP016Factor2555 * embedPair2542
      kernelN02700MinusP016Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP016Factor2555, kernelN02700MinusP016Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP016Factor2555 * embedPair2542
        kernelN02700MinusP016Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP016DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP016Factor2555, kernelN02700MinusP016Error2555,
      batchC02700MinusLeftP016NormUpper2558]

noncomputable def batchC02700MinusLeftP017NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP017NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP017NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP017Factor2555 * embedPair2542
      kernelN02700MinusP017Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP017Factor2555, kernelN02700MinusP017Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP017Factor2555 * embedPair2542
        kernelN02700MinusP017Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP017DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP017Factor2555, kernelN02700MinusP017Error2555,
      batchC02700MinusLeftP017NormUpper2558]

noncomputable def batchC02700MinusLeftP018NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP018NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP018NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP018Factor2555 * embedPair2542
      kernelN02700MinusP018Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP018Factor2555, kernelN02700MinusP018Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP018Factor2555 * embedPair2542
        kernelN02700MinusP018Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP018DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP018Factor2555, kernelN02700MinusP018Error2555,
      batchC02700MinusLeftP018NormUpper2558]

noncomputable def batchC02700MinusLeftP019NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP019NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP019NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP019Factor2555 * embedPair2542
      kernelN02700MinusP019Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP019Factor2555, kernelN02700MinusP019Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP019Factor2555 * embedPair2542
        kernelN02700MinusP019Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP019DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP019Factor2555, kernelN02700MinusP019Error2555,
      batchC02700MinusLeftP019NormUpper2558]

noncomputable def batchC02700MinusLeftP020NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP020NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP020NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP020Factor2555 * embedPair2542
      kernelN02700MinusP020Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP020Factor2555, kernelN02700MinusP020Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP020Factor2555 * embedPair2542
        kernelN02700MinusP020Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP020DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP020Factor2555, kernelN02700MinusP020Error2555,
      batchC02700MinusLeftP020NormUpper2558]

noncomputable def batchC02700MinusLeftP021NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP021NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP021NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP021Factor2555 * embedPair2542
      kernelN02700MinusP021Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP021Factor2555, kernelN02700MinusP021Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP021Factor2555 * embedPair2542
        kernelN02700MinusP021Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP021DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP021Factor2555, kernelN02700MinusP021Error2555,
      batchC02700MinusLeftP021NormUpper2558]

noncomputable def batchC02700MinusLeftP022NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP022NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP022NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP022Factor2555 * embedPair2542
      kernelN02700MinusP022Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP022Factor2555, kernelN02700MinusP022Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP022Factor2555 * embedPair2542
        kernelN02700MinusP022Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP022DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP022Factor2555, kernelN02700MinusP022Error2555,
      batchC02700MinusLeftP022NormUpper2558]

noncomputable def batchC02700MinusLeftP023NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP023NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP023NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP023Factor2555 * embedPair2542
      kernelN02700MinusP023Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP023Factor2555, kernelN02700MinusP023Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP023Factor2555 * embedPair2542
        kernelN02700MinusP023Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP023DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP023Factor2555, kernelN02700MinusP023Error2555,
      batchC02700MinusLeftP023NormUpper2558]

noncomputable def batchC02700MinusLeftP024NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP024NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP024NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP024Factor2555 * embedPair2542
      kernelN02700MinusP024Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP024Factor2555, kernelN02700MinusP024Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP024Factor2555 * embedPair2542
        kernelN02700MinusP024Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP024DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP024Factor2555, kernelN02700MinusP024Error2555,
      batchC02700MinusLeftP024NormUpper2558]

noncomputable def batchC02700MinusLeftP025NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP025NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP025NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP025Factor2555 * embedPair2542
      kernelN02700MinusP025Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP025Factor2555, kernelN02700MinusP025Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP025Factor2555 * embedPair2542
        kernelN02700MinusP025Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP025DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP025Factor2555, kernelN02700MinusP025Error2555,
      batchC02700MinusLeftP025NormUpper2558]

noncomputable def batchC02700MinusLeftP026NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP026NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP026NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP026Factor2555 * embedPair2542
      kernelN02700MinusP026Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP026Factor2555, kernelN02700MinusP026Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP026Factor2555 * embedPair2542
        kernelN02700MinusP026Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP026DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP026Factor2555, kernelN02700MinusP026Error2555,
      batchC02700MinusLeftP026NormUpper2558]

noncomputable def batchC02700MinusLeftP027NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP027NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP027NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP027Factor2555 * embedPair2542
      kernelN02700MinusP027Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP027Factor2555, kernelN02700MinusP027Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP027Factor2555 * embedPair2542
        kernelN02700MinusP027Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP027DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP027Factor2555, kernelN02700MinusP027Error2555,
      batchC02700MinusLeftP027NormUpper2558]

noncomputable def batchC02700MinusLeftP028NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP028NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP028NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP028Factor2555 * embedPair2542
      kernelN02700MinusP028Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP028Factor2555, kernelN02700MinusP028Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP028Factor2555 * embedPair2542
        kernelN02700MinusP028Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP028DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP028Factor2555, kernelN02700MinusP028Error2555,
      batchC02700MinusLeftP028NormUpper2558]

noncomputable def batchC02700MinusLeftP029NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700MinusLeftP029NormBound2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN02700MinusPosition2555‖
        ≤
      batchC02700MinusLeftP029NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700MinusP029Factor2555 * embedPair2542
      kernelN02700MinusP029Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700MinusP029Factor2555, kernelN02700MinusP029Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN02700MinusPosition2555)
    (embedPair2542 kernelN02700MinusP029Factor2555 * embedPair2542
        kernelN02700MinusP029Center2555) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700MinusP029DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700MinusP029Factor2555, kernelN02700MinusP029Error2555,
      batchC02700MinusLeftP029NormUpper2558]

noncomputable def batchC02700MinusLeftNormUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02700MinusLeftP000NormUpper2558
  | 1 => batchC02700MinusLeftP001NormUpper2558
  | 2 => batchC02700MinusLeftP002NormUpper2558
  | 3 => batchC02700MinusLeftP003NormUpper2558
  | 4 => batchC02700MinusLeftP004NormUpper2558
  | 5 => batchC02700MinusLeftP005NormUpper2558
  | 6 => batchC02700MinusLeftP006NormUpper2558
  | 7 => batchC02700MinusLeftP007NormUpper2558
  | 8 => batchC02700MinusLeftP008NormUpper2558
  | 9 => batchC02700MinusLeftP009NormUpper2558
  | 10 => batchC02700MinusLeftP010NormUpper2558
  | 11 => batchC02700MinusLeftP011NormUpper2558
  | 12 => batchC02700MinusLeftP012NormUpper2558
  | 13 => batchC02700MinusLeftP013NormUpper2558
  | 14 => batchC02700MinusLeftP014NormUpper2558
  | 15 => batchC02700MinusLeftP015NormUpper2558
  | 16 => batchC02700MinusLeftP016NormUpper2558
  | 17 => batchC02700MinusLeftP017NormUpper2558
  | 18 => batchC02700MinusLeftP018NormUpper2558
  | 19 => batchC02700MinusLeftP019NormUpper2558
  | 20 => batchC02700MinusLeftP020NormUpper2558
  | 21 => batchC02700MinusLeftP021NormUpper2558
  | 22 => batchC02700MinusLeftP022NormUpper2558
  | 23 => batchC02700MinusLeftP023NormUpper2558
  | 24 => batchC02700MinusLeftP024NormUpper2558
  | 25 => batchC02700MinusLeftP025NormUpper2558
  | 26 => batchC02700MinusLeftP026NormUpper2558
  | 27 => batchC02700MinusLeftP027NormUpper2558
  | 28 => batchC02700MinusLeftP028NormUpper2558
  | 29 => batchC02700MinusLeftP029NormUpper2558
  | _ => 0

theorem batchC02700MinusLeftNormBound2558 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 i kernelN02700MinusPosition2555‖ ≤
        batchC02700MinusLeftNormUpper2558 i := by
  fin_cases i
  · exact batchC02700MinusLeftP000NormBound2558
  · exact batchC02700MinusLeftP001NormBound2558
  · exact batchC02700MinusLeftP002NormBound2558
  · exact batchC02700MinusLeftP003NormBound2558
  · exact batchC02700MinusLeftP004NormBound2558
  · exact batchC02700MinusLeftP005NormBound2558
  · exact batchC02700MinusLeftP006NormBound2558
  · exact batchC02700MinusLeftP007NormBound2558
  · exact batchC02700MinusLeftP008NormBound2558
  · exact batchC02700MinusLeftP009NormBound2558
  · exact batchC02700MinusLeftP010NormBound2558
  · exact batchC02700MinusLeftP011NormBound2558
  · exact batchC02700MinusLeftP012NormBound2558
  · exact batchC02700MinusLeftP013NormBound2558
  · exact batchC02700MinusLeftP014NormBound2558
  · exact batchC02700MinusLeftP015NormBound2558
  · exact batchC02700MinusLeftP016NormBound2558
  · exact batchC02700MinusLeftP017NormBound2558
  · exact batchC02700MinusLeftP018NormBound2558
  · exact batchC02700MinusLeftP019NormBound2558
  · exact batchC02700MinusLeftP020NormBound2558
  · exact batchC02700MinusLeftP021NormBound2558
  · exact batchC02700MinusLeftP022NormBound2558
  · exact batchC02700MinusLeftP023NormBound2558
  · exact batchC02700MinusLeftP024NormBound2558
  · exact batchC02700MinusLeftP025NormBound2558
  · exact batchC02700MinusLeftP026NormBound2558
  · exact batchC02700MinusLeftP027NormBound2558
  · exact batchC02700MinusLeftP028NormBound2558
  · exact batchC02700MinusLeftP029NormBound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP000NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP001NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP002NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP003NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP004NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP005NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP006NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP007NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP008NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP009NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP010NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP011NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP012NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP013NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP014NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP015NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP016NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP017NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP018NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP019NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP020NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP021NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP022NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP023NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP024NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP025NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP026NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP027NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP028NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusLeftP029NormBound2558
