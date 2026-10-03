import ConnesWeilRH.Dev.C1RouteAKernelN02701Plus2555
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def neighborLeftP000NormUpper2557 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP000NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP000NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP000Factor2555 * embedPair2542
      kernelN02701PlusP000Center2555‖
      ≤
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
      neighborLeftP000NormUpper2557]

noncomputable def neighborLeftP001NormUpper2557 : ℝ := ((90831855 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem neighborLeftP001NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP001NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP001Factor2555 * embedPair2542
      kernelN02701PlusP001Center2555‖
      ≤
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
      neighborLeftP001NormUpper2557]

noncomputable def neighborLeftP002NormUpper2557 : ℝ := ((115869405110549617164732497 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP002NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP002NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP002Factor2555 * embedPair2542
      kernelN02701PlusP002Center2555‖
      ≤
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
      neighborLeftP002NormUpper2557]

noncomputable def neighborLeftP003NormUpper2557 : ℝ := ((785828678998017666513534473605389 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP003NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP003NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP003Factor2555 * embedPair2542
      kernelN02701PlusP003Center2555‖
      ≤
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
      neighborLeftP003NormUpper2557]

noncomputable def neighborLeftP004NormUpper2557 : ℝ := ((169152985600784522608220228766284743 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem neighborLeftP004NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP004NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP004Factor2555 * embedPair2542
      kernelN02701PlusP004Center2555‖
      ≤
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
      neighborLeftP004NormUpper2557]

noncomputable def neighborLeftP005NormUpper2557 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP005NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP005NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP005Factor2555 * embedPair2542
      kernelN02701PlusP005Center2555‖
      ≤
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
      neighborLeftP005NormUpper2557]

noncomputable def neighborLeftP006NormUpper2557 : ℝ := ((169440119894170491153 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem neighborLeftP006NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP006NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP006Factor2555 * embedPair2542
      kernelN02701PlusP006Center2555‖
      ≤
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
      neighborLeftP006NormUpper2557]

noncomputable def neighborLeftP007NormUpper2557 : ℝ := ((27843335069501722188749694306721 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP007NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP007NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP007Factor2555 * embedPair2542
      kernelN02701PlusP007Center2555‖
      ≤
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
      neighborLeftP007NormUpper2557]

noncomputable def neighborLeftP008NormUpper2557 : ℝ := ((11404729393283407834189 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem neighborLeftP008NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP008NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP008Factor2555 * embedPair2542
      kernelN02701PlusP008Center2555‖
      ≤
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
      neighborLeftP008NormUpper2557]

noncomputable def neighborLeftP009NormUpper2557 : ℝ := ((22809475405537218983965 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem neighborLeftP009NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP009NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP009Factor2555 * embedPair2542
      kernelN02701PlusP009Center2555‖
      ≤
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
      neighborLeftP009NormUpper2557]

noncomputable def neighborLeftP010NormUpper2557 : ℝ := ((45618970060964048176441 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP010NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP010NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP010Factor2555 * embedPair2542
      kernelN02701PlusP010Center2555‖
      ≤
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
      neighborLeftP010NormUpper2557]

noncomputable def neighborLeftP011NormUpper2557 : ℝ := ((45618982895438801095465 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP011NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP011NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP011Factor2555 * embedPair2542
      kernelN02701PlusP011Center2555‖
      ≤
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
      neighborLeftP011NormUpper2557]

noncomputable def neighborLeftP012NormUpper2557 : ℝ := ((45618996188811026904001 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP012NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP012NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP012Factor2555 * embedPair2542
      kernelN02701PlusP012Center2555‖
      ≤
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
      neighborLeftP012NormUpper2557]

noncomputable def neighborLeftP013NormUpper2557 : ℝ := ((45619008302866927654155 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP013NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP013NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP013Factor2555 * embedPair2542
      kernelN02701PlusP013Center2555‖
      ≤
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
      neighborLeftP013NormUpper2557]

noncomputable def neighborLeftP014NormUpper2557 : ℝ := ((45619030748966138638097 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP014NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP014NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP014Factor2555 * embedPair2542
      kernelN02701PlusP014Center2555‖
      ≤
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
      neighborLeftP014NormUpper2557]

noncomputable def neighborLeftP015NormUpper2557 : ℝ := ((45619046831668091417203 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP015NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP015NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP015Factor2555 * embedPair2542
      kernelN02701PlusP015Center2555‖
      ≤
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
      neighborLeftP015NormUpper2557]

noncomputable def neighborLeftP016NormUpper2557 : ℝ := ((45619058454282116376825 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP016NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP016NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP016Factor2555 * embedPair2542
      kernelN02701PlusP016Center2555‖
      ≤
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
      neighborLeftP016NormUpper2557]

noncomputable def neighborLeftP017NormUpper2557 : ℝ := ((45619081030477589573003 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP017NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP017NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP017Factor2555 * embedPair2542
      kernelN02701PlusP017Center2555‖
      ≤
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
      neighborLeftP017NormUpper2557]

noncomputable def neighborLeftP018NormUpper2557 : ℝ := ((11404772391513690502981 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem neighborLeftP018NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP018NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP018Factor2555 * embedPair2542
      kernelN02701PlusP018Center2555‖
      ≤
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
      neighborLeftP018NormUpper2557]

noncomputable def neighborLeftP019NormUpper2557 : ℝ := ((712798515502547031175 : ℝ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984))

theorem neighborLeftP019NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP019NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP019Factor2555 * embedPair2542
      kernelN02701PlusP019Center2555‖
      ≤
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
      neighborLeftP019NormUpper2557]

noncomputable def neighborLeftP020NormUpper2557 : ℝ := ((11404780441704605665639 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem neighborLeftP020NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP020NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP020Factor2555 * embedPair2542
      kernelN02701PlusP020Center2555‖
      ≤
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
      neighborLeftP020NormUpper2557]

noncomputable def neighborLeftP021NormUpper2557 : ℝ := ((45619135765920945511767 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP021NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP021NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP021Factor2555 * embedPair2542
      kernelN02701PlusP021Center2555‖
      ≤
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
      neighborLeftP021NormUpper2557]

noncomputable def neighborLeftP022NormUpper2557 : ℝ := ((22809571465588377193053 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem neighborLeftP022NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP022NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP022Factor2555 * embedPair2542
      kernelN02701PlusP022Center2555‖
      ≤
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
      neighborLeftP022NormUpper2557]

noncomputable def neighborLeftP023NormUpper2557 : ℝ := ((11404790897484128632377 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem neighborLeftP023NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP023NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP023Factor2555 * embedPair2542
      kernelN02701PlusP023Center2555‖
      ≤
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
      neighborLeftP023NormUpper2557]

noncomputable def neighborLeftP024NormUpper2557 : ℝ := ((45619173083863814919083 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP024NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP024NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP024Factor2555 * embedPair2542
      kernelN02701PlusP024Center2555‖
      ≤
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
      neighborLeftP024NormUpper2557]

noncomputable def neighborLeftP025NormUpper2557 : ℝ := ((45619184987504688543133 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP025NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP025NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP025Factor2555 * embedPair2542
      kernelN02701PlusP025Center2555‖
      ≤
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
      neighborLeftP025NormUpper2557]

noncomputable def neighborLeftP026NormUpper2557 : ℝ := ((45619197152539844442753 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP026NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP026NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP026Factor2555 * embedPair2542
      kernelN02701PlusP026Center2555‖
      ≤
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
      neighborLeftP026NormUpper2557]

noncomputable def neighborLeftP027NormUpper2557 : ℝ := ((45619214707078308350739 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP027NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP027NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP027Factor2555 * embedPair2542
      kernelN02701PlusP027Center2555‖
      ≤
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
      neighborLeftP027NormUpper2557]

noncomputable def neighborLeftP028NormUpper2557 : ℝ := ((45619221657160357996833 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem neighborLeftP028NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP028NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP028Factor2555 * embedPair2542
      kernelN02701PlusP028Center2555‖
      ≤
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
      neighborLeftP028NormUpper2557]

noncomputable def neighborLeftP029NormUpper2557 : ℝ := ((22809616119106348189817 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem neighborLeftP029NormBound2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN02701PlusPosition2555‖ ≤
      neighborLeftP029NormUpper2557 := by
  have hc : ‖embedPair2542 kernelN02701PlusP029Factor2555 * embedPair2542
      kernelN02701PlusP029Center2555‖
      ≤
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
      neighborLeftP029NormUpper2557]

noncomputable def neighborLeftNormUpper2557 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => neighborLeftP000NormUpper2557
  | 1 => neighborLeftP001NormUpper2557
  | 2 => neighborLeftP002NormUpper2557
  | 3 => neighborLeftP003NormUpper2557
  | 4 => neighborLeftP004NormUpper2557
  | 5 => neighborLeftP005NormUpper2557
  | 6 => neighborLeftP006NormUpper2557
  | 7 => neighborLeftP007NormUpper2557
  | 8 => neighborLeftP008NormUpper2557
  | 9 => neighborLeftP009NormUpper2557
  | 10 => neighborLeftP010NormUpper2557
  | 11 => neighborLeftP011NormUpper2557
  | 12 => neighborLeftP012NormUpper2557
  | 13 => neighborLeftP013NormUpper2557
  | 14 => neighborLeftP014NormUpper2557
  | 15 => neighborLeftP015NormUpper2557
  | 16 => neighborLeftP016NormUpper2557
  | 17 => neighborLeftP017NormUpper2557
  | 18 => neighborLeftP018NormUpper2557
  | 19 => neighborLeftP019NormUpper2557
  | 20 => neighborLeftP020NormUpper2557
  | 21 => neighborLeftP021NormUpper2557
  | 22 => neighborLeftP022NormUpper2557
  | 23 => neighborLeftP023NormUpper2557
  | 24 => neighborLeftP024NormUpper2557
  | 25 => neighborLeftP025NormUpper2557
  | 26 => neighborLeftP026NormUpper2557
  | 27 => neighborLeftP027NormUpper2557
  | 28 => neighborLeftP028NormUpper2557
  | 29 => neighborLeftP029NormUpper2557
  | _ => 0

theorem neighborLeftNormBound2557 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 i kernelN02701PlusPosition2555‖ ≤
        neighborLeftNormUpper2557 i := by
  fin_cases i
  · exact neighborLeftP000NormBound2557
  · exact neighborLeftP001NormBound2557
  · exact neighborLeftP002NormBound2557
  · exact neighborLeftP003NormBound2557
  · exact neighborLeftP004NormBound2557
  · exact neighborLeftP005NormBound2557
  · exact neighborLeftP006NormBound2557
  · exact neighborLeftP007NormBound2557
  · exact neighborLeftP008NormBound2557
  · exact neighborLeftP009NormBound2557
  · exact neighborLeftP010NormBound2557
  · exact neighborLeftP011NormBound2557
  · exact neighborLeftP012NormBound2557
  · exact neighborLeftP013NormBound2557
  · exact neighborLeftP014NormBound2557
  · exact neighborLeftP015NormBound2557
  · exact neighborLeftP016NormBound2557
  · exact neighborLeftP017NormBound2557
  · exact neighborLeftP018NormBound2557
  · exact neighborLeftP019NormBound2557
  · exact neighborLeftP020NormBound2557
  · exact neighborLeftP021NormBound2557
  · exact neighborLeftP022NormBound2557
  · exact neighborLeftP023NormBound2557
  · exact neighborLeftP024NormBound2557
  · exact neighborLeftP025NormBound2557
  · exact neighborLeftP026NormBound2557
  · exact neighborLeftP027NormBound2557
  · exact neighborLeftP028NormBound2557
  · exact neighborLeftP029NormBound2557

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.neighborLeftP000NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP001NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP002NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP003NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP004NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP005NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP006NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP007NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP008NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP009NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP010NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP011NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP012NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP013NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP014NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP015NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP016NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP017NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP018NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP019NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP020NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP021NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP022NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP023NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP024NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP025NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP026NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP027NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP028NormBound2557
#print axioms ConnesWeilRH.Dev.neighborLeftP029NormBound2557
