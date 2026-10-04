import ConnesWeilRH.Dev.C1RouteAKernelN02701Plus2555
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC02700PlusRightP000NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP000NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP000NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP000Factor2555 * embedPair2542
      kernelN02701PlusP000Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP000Factor2555, kernelN02701PlusP000Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP000Factor2555 * embedPair2542 kernelN02701PlusP000Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP000DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP000Factor2555, kernelN02701PlusP000Error2555,
      batchC02700PlusRightP000NormUpper2558]

noncomputable def batchC02700PlusRightP001NormUpper2558 : ℝ := ((90831855 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem batchC02700PlusRightP001NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP001NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP001Factor2555 * embedPair2542
      kernelN02701PlusP001Center2555‖ ≤
      ((216579187 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP001Factor2555, kernelN02701PlusP001Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP001Factor2555 * embedPair2542 kernelN02701PlusP001Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP001DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP001Factor2555, kernelN02701PlusP001Error2555,
      batchC02700PlusRightP001NormUpper2558]

noncomputable def batchC02700PlusRightP002NormUpper2558 : ℝ := ((115869405110549617164732497 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP002NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP002NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP002Factor2555 * embedPair2542
      kernelN02701PlusP002Center2555‖ ≤
      ((57934702555274531405732521 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP002Factor2555, kernelN02701PlusP002Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP002Factor2555 * embedPair2542 kernelN02701PlusP002Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP002DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP002Factor2555, kernelN02701PlusP002Error2555,
      batchC02700PlusRightP002NormUpper2558]

noncomputable def batchC02700PlusRightP003NormUpper2558 : ℝ := ((785828678998017666513534473605389
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP003NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP003NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP003Factor2555 * embedPair2542
      kernelN02701PlusP003Center2555‖ ≤
      ((785828678998014279914349582189111 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP003Factor2555, kernelN02701PlusP003Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP003Factor2555 * embedPair2542 kernelN02701PlusP003Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP003DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP003Factor2555, kernelN02701PlusP003Error2555,
      batchC02700PlusRightP003NormUpper2558]

noncomputable def batchC02700PlusRightP004NormUpper2558 : ℝ :=
    ((169152985600784522608220228766284743 :
    ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700PlusRightP004NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP004NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP004Factor2555 * embedPair2542
      kernelN02701PlusP004Center2555‖ ≤
      ((169152985600783798021986268662749479 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP004Factor2555, kernelN02701PlusP004Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP004Factor2555 * embedPair2542 kernelN02701PlusP004Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP004DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP004Factor2555, kernelN02701PlusP004Error2555,
      batchC02700PlusRightP004NormUpper2558]

noncomputable def batchC02700PlusRightP005NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP005NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP005NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP005Factor2555 * embedPair2542
      kernelN02701PlusP005Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP005Factor2555, kernelN02701PlusP005Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP005Factor2555 * embedPair2542 kernelN02701PlusP005Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP005DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP005Factor2555, kernelN02701PlusP005Error2555,
      batchC02700PlusRightP005NormUpper2558]

noncomputable def batchC02700PlusRightP006NormUpper2558 : ℝ := ((169440119894170491153 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700PlusRightP006NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP006NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP006Factor2555 * embedPair2542
      kernelN02701PlusP006Center2555‖ ≤
      ((42360029973542525319 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP006Factor2555, kernelN02701PlusP006Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP006Factor2555 * embedPair2542 kernelN02701PlusP006Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP006DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP006Factor2555, kernelN02701PlusP006Error2555,
      batchC02700PlusRightP006NormUpper2558]

noncomputable def batchC02700PlusRightP007NormUpper2558 : ℝ := ((27843335069501722188749694306721
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP007NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP007NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP007Factor2555 * embedPair2542
      kernelN02701PlusP007Center2555‖ ≤
      ((27843335069501718510218107012151 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP007Factor2555, kernelN02701PlusP007Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP007Factor2555 * embedPair2542 kernelN02701PlusP007Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP007DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP007Factor2555, kernelN02701PlusP007Error2555,
      batchC02700PlusRightP007NormUpper2558]

noncomputable def batchC02700PlusRightP008NormUpper2558 : ℝ := ((11404729393283407834189 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02700PlusRightP008NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP008NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP008Factor2555 * embedPair2542
      kernelN02701PlusP008Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP008Factor2555, kernelN02701PlusP008Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP008Factor2555 * embedPair2542 kernelN02701PlusP008Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP008DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP008Factor2555, kernelN02701PlusP008Error2555,
      batchC02700PlusRightP008NormUpper2558]

noncomputable def batchC02700PlusRightP009NormUpper2558 : ℝ := ((22809475405537218983965 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700PlusRightP009NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP009NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP009Factor2555 * embedPair2542
      kernelN02701PlusP009Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP009Factor2555, kernelN02701PlusP009Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP009Factor2555 * embedPair2542 kernelN02701PlusP009Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP009DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP009Factor2555, kernelN02701PlusP009Error2555,
      batchC02700PlusRightP009NormUpper2558]

noncomputable def batchC02700PlusRightP010NormUpper2558 : ℝ := ((45618970060964048176441 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP010NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP010NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP010Factor2555 * embedPair2542
      kernelN02701PlusP010Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP010Factor2555, kernelN02701PlusP010Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP010Factor2555 * embedPair2542 kernelN02701PlusP010Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP010DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP010Factor2555, kernelN02701PlusP010Error2555,
      batchC02700PlusRightP010NormUpper2558]

noncomputable def batchC02700PlusRightP011NormUpper2558 : ℝ := ((45618982895438801095465 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP011NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP011NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP011Factor2555 * embedPair2542
      kernelN02701PlusP011Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP011Factor2555, kernelN02701PlusP011Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP011Factor2555 * embedPair2542 kernelN02701PlusP011Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP011DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP011Factor2555, kernelN02701PlusP011Error2555,
      batchC02700PlusRightP011NormUpper2558]

noncomputable def batchC02700PlusRightP012NormUpper2558 : ℝ := ((45618996188811026904001 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP012NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP012NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP012Factor2555 * embedPair2542
      kernelN02701PlusP012Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP012Factor2555, kernelN02701PlusP012Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP012Factor2555 * embedPair2542 kernelN02701PlusP012Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP012DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP012Factor2555, kernelN02701PlusP012Error2555,
      batchC02700PlusRightP012NormUpper2558]

noncomputable def batchC02700PlusRightP013NormUpper2558 : ℝ := ((45619008302866927654155 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP013NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP013NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP013Factor2555 * embedPair2542
      kernelN02701PlusP013Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP013Factor2555, kernelN02701PlusP013Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP013Factor2555 * embedPair2542 kernelN02701PlusP013Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP013DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP013Factor2555, kernelN02701PlusP013Error2555,
      batchC02700PlusRightP013NormUpper2558]

noncomputable def batchC02700PlusRightP014NormUpper2558 : ℝ := ((45619030748966138638097 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP014NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP014NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP014Factor2555 * embedPair2542
      kernelN02701PlusP014Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP014Factor2555, kernelN02701PlusP014Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP014Factor2555 * embedPair2542 kernelN02701PlusP014Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP014DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP014Factor2555, kernelN02701PlusP014Error2555,
      batchC02700PlusRightP014NormUpper2558]

noncomputable def batchC02700PlusRightP015NormUpper2558 : ℝ := ((45619046831668091417203 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP015NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP015NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP015Factor2555 * embedPair2542
      kernelN02701PlusP015Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP015Factor2555, kernelN02701PlusP015Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP015Factor2555 * embedPair2542 kernelN02701PlusP015Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP015DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP015Factor2555, kernelN02701PlusP015Error2555,
      batchC02700PlusRightP015NormUpper2558]

noncomputable def batchC02700PlusRightP016NormUpper2558 : ℝ := ((45619058454282116376825 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP016NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP016NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP016Factor2555 * embedPair2542
      kernelN02701PlusP016Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP016Factor2555, kernelN02701PlusP016Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP016Factor2555 * embedPair2542 kernelN02701PlusP016Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP016DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP016Factor2555, kernelN02701PlusP016Error2555,
      batchC02700PlusRightP016NormUpper2558]

noncomputable def batchC02700PlusRightP017NormUpper2558 : ℝ := ((45619081030477589573003 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP017NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP017NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP017Factor2555 * embedPair2542
      kernelN02701PlusP017Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP017Factor2555, kernelN02701PlusP017Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP017Factor2555 * embedPair2542 kernelN02701PlusP017Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP017DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP017Factor2555, kernelN02701PlusP017Error2555,
      batchC02700PlusRightP017NormUpper2558]

noncomputable def batchC02700PlusRightP018NormUpper2558 : ℝ := ((11404772391513690502981 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02700PlusRightP018NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP018NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP018Factor2555 * embedPair2542
      kernelN02701PlusP018Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP018Factor2555, kernelN02701PlusP018Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP018Factor2555 * embedPair2542 kernelN02701PlusP018Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP018DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP018Factor2555, kernelN02701PlusP018Error2555,
      batchC02700PlusRightP018NormUpper2558]

noncomputable def batchC02700PlusRightP019NormUpper2558 : ℝ := ((712798515502547031175 : ℝ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984))

theorem batchC02700PlusRightP019NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP019NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP019Factor2555 * embedPair2542
      kernelN02701PlusP019Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP019Factor2555, kernelN02701PlusP019Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP019Factor2555 * embedPair2542 kernelN02701PlusP019Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP019DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP019Factor2555, kernelN02701PlusP019Error2555,
      batchC02700PlusRightP019NormUpper2558]

noncomputable def batchC02700PlusRightP020NormUpper2558 : ℝ := ((11404780441704605665639 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02700PlusRightP020NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP020NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP020Factor2555 * embedPair2542
      kernelN02701PlusP020Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP020Factor2555, kernelN02701PlusP020Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP020Factor2555 * embedPair2542 kernelN02701PlusP020Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP020DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP020Factor2555, kernelN02701PlusP020Error2555,
      batchC02700PlusRightP020NormUpper2558]

noncomputable def batchC02700PlusRightP021NormUpper2558 : ℝ := ((45619135765920945511767 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP021NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP021NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP021Factor2555 * embedPair2542
      kernelN02701PlusP021Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP021Factor2555, kernelN02701PlusP021Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP021Factor2555 * embedPair2542 kernelN02701PlusP021Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP021DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP021Factor2555, kernelN02701PlusP021Error2555,
      batchC02700PlusRightP021NormUpper2558]

noncomputable def batchC02700PlusRightP022NormUpper2558 : ℝ := ((22809571465588377193053 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700PlusRightP022NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP022NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP022Factor2555 * embedPair2542
      kernelN02701PlusP022Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP022Factor2555, kernelN02701PlusP022Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP022Factor2555 * embedPair2542 kernelN02701PlusP022Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP022DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP022Factor2555, kernelN02701PlusP022Error2555,
      batchC02700PlusRightP022NormUpper2558]

noncomputable def batchC02700PlusRightP023NormUpper2558 : ℝ := ((11404790897484128632377 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02700PlusRightP023NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP023NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP023Factor2555 * embedPair2542
      kernelN02701PlusP023Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP023Factor2555, kernelN02701PlusP023Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP023Factor2555 * embedPair2542 kernelN02701PlusP023Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP023DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP023Factor2555, kernelN02701PlusP023Error2555,
      batchC02700PlusRightP023NormUpper2558]

noncomputable def batchC02700PlusRightP024NormUpper2558 : ℝ := ((45619173083863814919083 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP024NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP024NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP024Factor2555 * embedPair2542
      kernelN02701PlusP024Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP024Factor2555, kernelN02701PlusP024Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP024Factor2555 * embedPair2542 kernelN02701PlusP024Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP024DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP024Factor2555, kernelN02701PlusP024Error2555,
      batchC02700PlusRightP024NormUpper2558]

noncomputable def batchC02700PlusRightP025NormUpper2558 : ℝ := ((45619184987504688543133 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP025NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP025NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP025Factor2555 * embedPair2542
      kernelN02701PlusP025Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP025Factor2555, kernelN02701PlusP025Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP025Factor2555 * embedPair2542 kernelN02701PlusP025Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP025DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP025Factor2555, kernelN02701PlusP025Error2555,
      batchC02700PlusRightP025NormUpper2558]

noncomputable def batchC02700PlusRightP026NormUpper2558 : ℝ := ((45619197152539844442753 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP026NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP026NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP026Factor2555 * embedPair2542
      kernelN02701PlusP026Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP026Factor2555, kernelN02701PlusP026Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP026Factor2555 * embedPair2542 kernelN02701PlusP026Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP026DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP026Factor2555, kernelN02701PlusP026Error2555,
      batchC02700PlusRightP026NormUpper2558]

noncomputable def batchC02700PlusRightP027NormUpper2558 : ℝ := ((45619214707078308350739 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP027NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP027NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP027Factor2555 * embedPair2542
      kernelN02701PlusP027Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP027Factor2555, kernelN02701PlusP027Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP027Factor2555 * embedPair2542 kernelN02701PlusP027Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP027DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP027Factor2555, kernelN02701PlusP027Error2555,
      batchC02700PlusRightP027NormUpper2558]

noncomputable def batchC02700PlusRightP028NormUpper2558 : ℝ := ((45619221657160357996833 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02700PlusRightP028NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP028NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP028Factor2555 * embedPair2542
      kernelN02701PlusP028Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP028Factor2555, kernelN02701PlusP028Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP028Factor2555 * embedPair2542 kernelN02701PlusP028Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP028DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP028Factor2555, kernelN02701PlusP028Error2555,
      batchC02700PlusRightP028NormUpper2558]

noncomputable def batchC02700PlusRightP029NormUpper2558 : ℝ := ((22809616119106348189817 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02700PlusRightP029NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      batchC02700PlusRightP029NormUpper2558 := by
  have hc : ‖embedPair2542 kernelN02701PlusP029Factor2555 * embedPair2542
      kernelN02701PlusP029Center2555‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, kernelN02701PlusP029Factor2555, kernelN02701PlusP029Center2555,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN02701PlusPosition2555)
    (embedPair2542 kernelN02701PlusP029Factor2555 * embedPair2542 kernelN02701PlusP029Center2555)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add kernelN02701PlusP029DerivativeError2555 hc)).trans
  norm_num [pairMagnitude2542, kernelN02701PlusP029Factor2555, kernelN02701PlusP029Error2555,
      batchC02700PlusRightP029NormUpper2558]

noncomputable def batchC02700PlusRightNormUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02700PlusRightP000NormUpper2558
  | 1 => batchC02700PlusRightP001NormUpper2558
  | 2 => batchC02700PlusRightP002NormUpper2558
  | 3 => batchC02700PlusRightP003NormUpper2558
  | 4 => batchC02700PlusRightP004NormUpper2558
  | 5 => batchC02700PlusRightP005NormUpper2558
  | 6 => batchC02700PlusRightP006NormUpper2558
  | 7 => batchC02700PlusRightP007NormUpper2558
  | 8 => batchC02700PlusRightP008NormUpper2558
  | 9 => batchC02700PlusRightP009NormUpper2558
  | 10 => batchC02700PlusRightP010NormUpper2558
  | 11 => batchC02700PlusRightP011NormUpper2558
  | 12 => batchC02700PlusRightP012NormUpper2558
  | 13 => batchC02700PlusRightP013NormUpper2558
  | 14 => batchC02700PlusRightP014NormUpper2558
  | 15 => batchC02700PlusRightP015NormUpper2558
  | 16 => batchC02700PlusRightP016NormUpper2558
  | 17 => batchC02700PlusRightP017NormUpper2558
  | 18 => batchC02700PlusRightP018NormUpper2558
  | 19 => batchC02700PlusRightP019NormUpper2558
  | 20 => batchC02700PlusRightP020NormUpper2558
  | 21 => batchC02700PlusRightP021NormUpper2558
  | 22 => batchC02700PlusRightP022NormUpper2558
  | 23 => batchC02700PlusRightP023NormUpper2558
  | 24 => batchC02700PlusRightP024NormUpper2558
  | 25 => batchC02700PlusRightP025NormUpper2558
  | 26 => batchC02700PlusRightP026NormUpper2558
  | 27 => batchC02700PlusRightP027NormUpper2558
  | 28 => batchC02700PlusRightP028NormUpper2558
  | 29 => batchC02700PlusRightP029NormUpper2558
  | _ => 0

theorem batchC02700PlusRightNormBound2558 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 i kernelN02701PlusPosition2555‖ ≤
        batchC02700PlusRightNormUpper2558 i := by
  fin_cases i
  · exact batchC02700PlusRightP000NormBound2558
  · exact batchC02700PlusRightP001NormBound2558
  · exact batchC02700PlusRightP002NormBound2558
  · exact batchC02700PlusRightP003NormBound2558
  · exact batchC02700PlusRightP004NormBound2558
  · exact batchC02700PlusRightP005NormBound2558
  · exact batchC02700PlusRightP006NormBound2558
  · exact batchC02700PlusRightP007NormBound2558
  · exact batchC02700PlusRightP008NormBound2558
  · exact batchC02700PlusRightP009NormBound2558
  · exact batchC02700PlusRightP010NormBound2558
  · exact batchC02700PlusRightP011NormBound2558
  · exact batchC02700PlusRightP012NormBound2558
  · exact batchC02700PlusRightP013NormBound2558
  · exact batchC02700PlusRightP014NormBound2558
  · exact batchC02700PlusRightP015NormBound2558
  · exact batchC02700PlusRightP016NormBound2558
  · exact batchC02700PlusRightP017NormBound2558
  · exact batchC02700PlusRightP018NormBound2558
  · exact batchC02700PlusRightP019NormBound2558
  · exact batchC02700PlusRightP020NormBound2558
  · exact batchC02700PlusRightP021NormBound2558
  · exact batchC02700PlusRightP022NormBound2558
  · exact batchC02700PlusRightP023NormBound2558
  · exact batchC02700PlusRightP024NormBound2558
  · exact batchC02700PlusRightP025NormBound2558
  · exact batchC02700PlusRightP026NormBound2558
  · exact batchC02700PlusRightP027NormBound2558
  · exact batchC02700PlusRightP028NormBound2558
  · exact batchC02700PlusRightP029NormBound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP000NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP001NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP002NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP003NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP004NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP005NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP006NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP007NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP008NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP009NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP010NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP011NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP012NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP013NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP014NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP015NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP016NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP017NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP018NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP019NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP020NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP021NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP022NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP023NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP024NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP025NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP026NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP027NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP028NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusRightP029NormBound2558
