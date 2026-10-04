import ConnesWeilRH.Dev.C1RouteAKernelN02700Plus2555
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC02700PlusLeftP000NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP000NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP000NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP000Factor2555 * embedPair2542
      kernelN02700PlusP000Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP000Factor2555, kernelN02700PlusP000Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP000Factor2555 * embedPair2542 kernelN02700PlusP000Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP000DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP000Factor2555, kernelN02700PlusP000Error2555,
      batchC02700PlusLeftP000NormUpper2558]

noncomputable def batchC02700PlusLeftP001NormUpper2558 : ℝ := ((186420741 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02700PlusLeftP001NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP001NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP001Factor2555 * embedPair2542
      kernelN02700PlusP001Center2555‖
      ≤
      ((222434561 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP001Factor2555, kernelN02700PlusP001Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP001Factor2555 * embedPair2542 kernelN02700PlusP001Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP001DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP001Factor2555, kernelN02700PlusP001Error2555,
      batchC02700PlusLeftP001NormUpper2558]

noncomputable def batchC02700PlusLeftP002NormUpper2558 : ℝ := ((110130323641529837951625809 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP002NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP002NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP002Factor2555 * embedPair2542
      kernelN02700PlusP002Center2555‖
      ≤
      ((110130323641529315156074145 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP002Factor2555, kernelN02700PlusP002Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP002Factor2555 * embedPair2542 kernelN02700PlusP002Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP002DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP002Factor2555, kernelN02700PlusP002Error2555,
      batchC02700PlusLeftP002NormUpper2558]

noncomputable def batchC02700PlusLeftP003NormUpper2558 : ℝ := ((385700539197020624901761462879681
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700PlusLeftP003NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP003NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP003Factor2555 * embedPair2542
      kernelN02700PlusP003Center2555‖
      ≤
      ((771401078394037952310190327927081 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP003Factor2555, kernelN02700PlusP003Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP003Factor2555 * embedPair2542 kernelN02700PlusP003Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP003DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP003Factor2555, kernelN02700PlusP003Error2555,
      batchC02700PlusLeftP003NormUpper2558]

noncomputable def batchC02700PlusLeftP004NormUpper2558 : ℝ :=
    ((167516612222054458663584796683073605 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700PlusLeftP004NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP004NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP004Factor2555 * embedPair2542
      kernelN02700PlusP004Center2555‖
      ≤
      ((335033224444107493234479391211615069 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP004Factor2555, kernelN02700PlusP004Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP004Factor2555 * embedPair2542 kernelN02700PlusP004Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP004DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP004Factor2555, kernelN02700PlusP004Error2555,
      batchC02700PlusLeftP004NormUpper2558]

noncomputable def batchC02700PlusLeftP005NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP005NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP005NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP005Factor2555 * embedPair2542
      kernelN02700PlusP005Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP005Factor2555, kernelN02700PlusP005Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP005Factor2555 * embedPair2542 kernelN02700PlusP005Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP005DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP005Factor2555, kernelN02700PlusP005Error2555,
      batchC02700PlusLeftP005NormUpper2558]

noncomputable def batchC02700PlusLeftP006NormUpper2558 : ℝ := ((155703987299712143743 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700PlusLeftP006NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP006NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP006Factor2555 * embedPair2542
      kernelN02700PlusP006Center2555‖
      ≤
      ((311407974599423507907 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP006Factor2555, kernelN02700PlusP006Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP006Factor2555 * embedPair2542 kernelN02700PlusP006Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP006DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP006Factor2555, kernelN02700PlusP006Error2555,
      batchC02700PlusLeftP006NormUpper2558]

noncomputable def batchC02700PlusLeftP007NormUpper2558 : ℝ := ((27421781294400755873396553172483 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP007NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP007NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP007Factor2555 * embedPair2542
      kernelN02700PlusP007Center2555‖
      ≤
      ((27421781294400752249483688292697 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP007Factor2555, kernelN02700PlusP007Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP007Factor2555 * embedPair2542 kernelN02700PlusP007Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP007DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP007Factor2555, kernelN02700PlusP007Error2555,
      batchC02700PlusLeftP007NormUpper2558]

noncomputable def batchC02700PlusLeftP008NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP008NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP008NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP008Factor2555 * embedPair2542
      kernelN02700PlusP008Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP008Factor2555, kernelN02700PlusP008Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP008Factor2555 * embedPair2542 kernelN02700PlusP008Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP008DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP008Factor2555, kernelN02700PlusP008Error2555,
      batchC02700PlusLeftP008NormUpper2558]

noncomputable def batchC02700PlusLeftP009NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP009NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP009NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP009Factor2555 * embedPair2542
      kernelN02700PlusP009Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP009Factor2555, kernelN02700PlusP009Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP009Factor2555 * embedPair2542 kernelN02700PlusP009Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP009DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP009Factor2555, kernelN02700PlusP009Error2555,
      batchC02700PlusLeftP009NormUpper2558]

noncomputable def batchC02700PlusLeftP010NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP010NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP010NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP010Factor2555 * embedPair2542
      kernelN02700PlusP010Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP010Factor2555, kernelN02700PlusP010Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP010Factor2555 * embedPair2542 kernelN02700PlusP010Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP010DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP010Factor2555, kernelN02700PlusP010Error2555,
      batchC02700PlusLeftP010NormUpper2558]

noncomputable def batchC02700PlusLeftP011NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP011NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP011NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP011Factor2555 * embedPair2542
      kernelN02700PlusP011Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP011Factor2555, kernelN02700PlusP011Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP011Factor2555 * embedPair2542 kernelN02700PlusP011Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP011DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP011Factor2555, kernelN02700PlusP011Error2555,
      batchC02700PlusLeftP011NormUpper2558]

noncomputable def batchC02700PlusLeftP012NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP012NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP012NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP012Factor2555 * embedPair2542
      kernelN02700PlusP012Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP012Factor2555, kernelN02700PlusP012Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP012Factor2555 * embedPair2542 kernelN02700PlusP012Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP012DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP012Factor2555, kernelN02700PlusP012Error2555,
      batchC02700PlusLeftP012NormUpper2558]

noncomputable def batchC02700PlusLeftP013NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP013NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP013NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP013Factor2555 * embedPair2542
      kernelN02700PlusP013Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP013Factor2555, kernelN02700PlusP013Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP013Factor2555 * embedPair2542 kernelN02700PlusP013Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP013DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP013Factor2555, kernelN02700PlusP013Error2555,
      batchC02700PlusLeftP013NormUpper2558]

noncomputable def batchC02700PlusLeftP014NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP014NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP014NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP014Factor2555 * embedPair2542
      kernelN02700PlusP014Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP014Factor2555, kernelN02700PlusP014Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP014Factor2555 * embedPair2542 kernelN02700PlusP014Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP014DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP014Factor2555, kernelN02700PlusP014Error2555,
      batchC02700PlusLeftP014NormUpper2558]

noncomputable def batchC02700PlusLeftP015NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP015NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP015NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP015Factor2555 * embedPair2542
      kernelN02700PlusP015Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP015Factor2555, kernelN02700PlusP015Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP015Factor2555 * embedPair2542 kernelN02700PlusP015Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP015DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP015Factor2555, kernelN02700PlusP015Error2555,
      batchC02700PlusLeftP015NormUpper2558]

noncomputable def batchC02700PlusLeftP016NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP016NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP016NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP016Factor2555 * embedPair2542
      kernelN02700PlusP016Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP016Factor2555, kernelN02700PlusP016Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP016Factor2555 * embedPair2542 kernelN02700PlusP016Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP016DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP016Factor2555, kernelN02700PlusP016Error2555,
      batchC02700PlusLeftP016NormUpper2558]

noncomputable def batchC02700PlusLeftP017NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP017NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP017NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP017Factor2555 * embedPair2542
      kernelN02700PlusP017Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP017Factor2555, kernelN02700PlusP017Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP017Factor2555 * embedPair2542 kernelN02700PlusP017Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP017DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP017Factor2555, kernelN02700PlusP017Error2555,
      batchC02700PlusLeftP017NormUpper2558]

noncomputable def batchC02700PlusLeftP018NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP018NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP018NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP018Factor2555 * embedPair2542
      kernelN02700PlusP018Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP018Factor2555, kernelN02700PlusP018Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP018Factor2555 * embedPair2542 kernelN02700PlusP018Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP018DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP018Factor2555, kernelN02700PlusP018Error2555,
      batchC02700PlusLeftP018NormUpper2558]

noncomputable def batchC02700PlusLeftP019NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP019NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP019NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP019Factor2555 * embedPair2542
      kernelN02700PlusP019Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP019Factor2555, kernelN02700PlusP019Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP019Factor2555 * embedPair2542 kernelN02700PlusP019Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP019DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP019Factor2555, kernelN02700PlusP019Error2555,
      batchC02700PlusLeftP019NormUpper2558]

noncomputable def batchC02700PlusLeftP020NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP020NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP020NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP020Factor2555 * embedPair2542
      kernelN02700PlusP020Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP020Factor2555, kernelN02700PlusP020Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP020Factor2555 * embedPair2542 kernelN02700PlusP020Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP020DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP020Factor2555, kernelN02700PlusP020Error2555,
      batchC02700PlusLeftP020NormUpper2558]

noncomputable def batchC02700PlusLeftP021NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP021NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP021NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP021Factor2555 * embedPair2542
      kernelN02700PlusP021Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP021Factor2555, kernelN02700PlusP021Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP021Factor2555 * embedPair2542 kernelN02700PlusP021Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP021DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP021Factor2555, kernelN02700PlusP021Error2555,
      batchC02700PlusLeftP021NormUpper2558]

noncomputable def batchC02700PlusLeftP022NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP022NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP022NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP022Factor2555 * embedPair2542
      kernelN02700PlusP022Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP022Factor2555, kernelN02700PlusP022Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP022Factor2555 * embedPair2542 kernelN02700PlusP022Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP022DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP022Factor2555, kernelN02700PlusP022Error2555,
      batchC02700PlusLeftP022NormUpper2558]

noncomputable def batchC02700PlusLeftP023NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP023NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP023NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP023Factor2555 * embedPair2542
      kernelN02700PlusP023Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP023Factor2555, kernelN02700PlusP023Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP023Factor2555 * embedPair2542 kernelN02700PlusP023Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP023DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP023Factor2555, kernelN02700PlusP023Error2555,
      batchC02700PlusLeftP023NormUpper2558]

noncomputable def batchC02700PlusLeftP024NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP024NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP024NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP024Factor2555 * embedPair2542
      kernelN02700PlusP024Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP024Factor2555, kernelN02700PlusP024Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP024Factor2555 * embedPair2542 kernelN02700PlusP024Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP024DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP024Factor2555, kernelN02700PlusP024Error2555,
      batchC02700PlusLeftP024NormUpper2558]

noncomputable def batchC02700PlusLeftP025NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP025NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP025NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP025Factor2555 * embedPair2542
      kernelN02700PlusP025Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP025Factor2555, kernelN02700PlusP025Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP025Factor2555 * embedPair2542 kernelN02700PlusP025Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP025DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP025Factor2555, kernelN02700PlusP025Error2555,
      batchC02700PlusLeftP025NormUpper2558]

noncomputable def batchC02700PlusLeftP026NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP026NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP026NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP026Factor2555 * embedPair2542
      kernelN02700PlusP026Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP026Factor2555, kernelN02700PlusP026Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP026Factor2555 * embedPair2542 kernelN02700PlusP026Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP026DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP026Factor2555, kernelN02700PlusP026Error2555,
      batchC02700PlusLeftP026NormUpper2558]

noncomputable def batchC02700PlusLeftP027NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP027NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP027NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP027Factor2555 * embedPair2542
      kernelN02700PlusP027Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP027Factor2555, kernelN02700PlusP027Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP027Factor2555 * embedPair2542 kernelN02700PlusP027Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP027DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP027Factor2555, kernelN02700PlusP027Error2555,
      batchC02700PlusLeftP027NormUpper2558]

noncomputable def batchC02700PlusLeftP028NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP028NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP028NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP028Factor2555 * embedPair2542
      kernelN02700PlusP028Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP028Factor2555, kernelN02700PlusP028Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP028Factor2555 * embedPair2542 kernelN02700PlusP028Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP028DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP028Factor2555, kernelN02700PlusP028Error2555,
      batchC02700PlusLeftP028NormUpper2558]

noncomputable def batchC02700PlusLeftP029NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusLeftP029NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN02700PlusPosition2555‖ ≤
      batchC02700PlusLeftP029NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02700PlusP029Factor2555 * embedPair2542
      kernelN02700PlusP029Center2555‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02700PlusP029Factor2555, kernelN02700PlusP029Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN02700PlusPosition2555)
    (embedPair2542 kernelN02700PlusP029Factor2555 * embedPair2542 kernelN02700PlusP029Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02700PlusP029DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02700PlusP029Factor2555, kernelN02700PlusP029Error2555,
      batchC02700PlusLeftP029NormUpper2558]

noncomputable def batchC02700PlusLeftNormUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02700PlusLeftP000NormUpper2558
  | 1 => batchC02700PlusLeftP001NormUpper2558
  | 2 => batchC02700PlusLeftP002NormUpper2558
  | 3 => batchC02700PlusLeftP003NormUpper2558
  | 4 => batchC02700PlusLeftP004NormUpper2558
  | 5 => batchC02700PlusLeftP005NormUpper2558
  | 6 => batchC02700PlusLeftP006NormUpper2558
  | 7 => batchC02700PlusLeftP007NormUpper2558
  | 8 => batchC02700PlusLeftP008NormUpper2558
  | 9 => batchC02700PlusLeftP009NormUpper2558
  | 10 => batchC02700PlusLeftP010NormUpper2558
  | 11 => batchC02700PlusLeftP011NormUpper2558
  | 12 => batchC02700PlusLeftP012NormUpper2558
  | 13 => batchC02700PlusLeftP013NormUpper2558
  | 14 => batchC02700PlusLeftP014NormUpper2558
  | 15 => batchC02700PlusLeftP015NormUpper2558
  | 16 => batchC02700PlusLeftP016NormUpper2558
  | 17 => batchC02700PlusLeftP017NormUpper2558
  | 18 => batchC02700PlusLeftP018NormUpper2558
  | 19 => batchC02700PlusLeftP019NormUpper2558
  | 20 => batchC02700PlusLeftP020NormUpper2558
  | 21 => batchC02700PlusLeftP021NormUpper2558
  | 22 => batchC02700PlusLeftP022NormUpper2558
  | 23 => batchC02700PlusLeftP023NormUpper2558
  | 24 => batchC02700PlusLeftP024NormUpper2558
  | 25 => batchC02700PlusLeftP025NormUpper2558
  | 26 => batchC02700PlusLeftP026NormUpper2558
  | 27 => batchC02700PlusLeftP027NormUpper2558
  | 28 => batchC02700PlusLeftP028NormUpper2558
  | 29 => batchC02700PlusLeftP029NormUpper2558
  | _ => 0

theorem batchC02700PlusLeftNormBound2558 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 i kernelN02700PlusPosition2555‖ ≤
        batchC02700PlusLeftNormUpper2558 i := by
  fin_cases i
  · exact batchC02700PlusLeftP000NormBound2558
  · exact batchC02700PlusLeftP001NormBound2558
  · exact batchC02700PlusLeftP002NormBound2558
  · exact batchC02700PlusLeftP003NormBound2558
  · exact batchC02700PlusLeftP004NormBound2558
  · exact batchC02700PlusLeftP005NormBound2558
  · exact batchC02700PlusLeftP006NormBound2558
  · exact batchC02700PlusLeftP007NormBound2558
  · exact batchC02700PlusLeftP008NormBound2558
  · exact batchC02700PlusLeftP009NormBound2558
  · exact batchC02700PlusLeftP010NormBound2558
  · exact batchC02700PlusLeftP011NormBound2558
  · exact batchC02700PlusLeftP012NormBound2558
  · exact batchC02700PlusLeftP013NormBound2558
  · exact batchC02700PlusLeftP014NormBound2558
  · exact batchC02700PlusLeftP015NormBound2558
  · exact batchC02700PlusLeftP016NormBound2558
  · exact batchC02700PlusLeftP017NormBound2558
  · exact batchC02700PlusLeftP018NormBound2558
  · exact batchC02700PlusLeftP019NormBound2558
  · exact batchC02700PlusLeftP020NormBound2558
  · exact batchC02700PlusLeftP021NormBound2558
  · exact batchC02700PlusLeftP022NormBound2558
  · exact batchC02700PlusLeftP023NormBound2558
  · exact batchC02700PlusLeftP024NormBound2558
  · exact batchC02700PlusLeftP025NormBound2558
  · exact batchC02700PlusLeftP026NormBound2558
  · exact batchC02700PlusLeftP027NormBound2558
  · exact batchC02700PlusLeftP028NormBound2558
  · exact batchC02700PlusLeftP029NormBound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP000NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP001NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP002NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP003NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP004NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP005NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP006NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP007NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP008NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP009NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP010NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP011NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP012NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP013NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP014NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP015NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP016NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP017NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP018NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP019NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP020NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP021NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP022NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP023NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP024NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP025NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP026NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP027NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP028NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusLeftP029NormBound2558
