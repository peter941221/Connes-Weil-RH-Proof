import ConnesWeilRH.Dev.C1RouteABoundaryRight2548
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def edgeRightP000NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP000NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP000NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP000Factor2548 * embedPair2542
      edgeRightP000Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP000Factor2548, edgeRightP000Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP000Factor2548 * embedPair2542 edgeRightP000Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP000DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP000Factor2548, edgeRightP000Error2548,
      edgeRightP000NormUpper2549]

noncomputable def edgeRightP001NormUpper2549 : ℝ := ((90831855 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem edgeRightP001NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP001NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP001Factor2548 * embedPair2542
      edgeRightP001Center2548‖ ≤
      ((216579187 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP001Factor2548, edgeRightP001Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP001Factor2548 * embedPair2542 edgeRightP001Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP001DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP001Factor2548, edgeRightP001Error2548,
      edgeRightP001NormUpper2549]

noncomputable def edgeRightP002NormUpper2549 : ℝ := ((115869405110549617164732497 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP002NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP002NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP002Factor2548 * embedPair2542
      edgeRightP002Center2548‖ ≤
      ((57934702555274531405732521 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP002Factor2548, edgeRightP002Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP002Factor2548 * embedPair2542 edgeRightP002Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP002DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP002Factor2548, edgeRightP002Error2548,
      edgeRightP002NormUpper2549]

noncomputable def edgeRightP003NormUpper2549 : ℝ := ((785828678998017666513534473605389 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP003NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP003NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP003Factor2548 * embedPair2542
      edgeRightP003Center2548‖ ≤
      ((785828678998014279914349582189111 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP003Factor2548, edgeRightP003Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP003Factor2548 * embedPair2542 edgeRightP003Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP003DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP003Factor2548, edgeRightP003Error2548,
      edgeRightP003NormUpper2549]

noncomputable def edgeRightP004NormUpper2549 : ℝ := ((169152985600784522608220228766284743 :
    ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem edgeRightP004NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP004NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP004Factor2548 * embedPair2542
      edgeRightP004Center2548‖ ≤
      ((169152985600783798021986268662749479 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP004Factor2548, edgeRightP004Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP004Factor2548 * embedPair2542 edgeRightP004Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP004DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP004Factor2548, edgeRightP004Error2548,
      edgeRightP004NormUpper2549]

noncomputable def edgeRightP005NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP005NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP005NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP005Factor2548 * embedPair2542
      edgeRightP005Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP005Factor2548, edgeRightP005Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP005Factor2548 * embedPair2542 edgeRightP005Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP005DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP005Factor2548, edgeRightP005Error2548,
      edgeRightP005NormUpper2549]

noncomputable def edgeRightP006NormUpper2549 : ℝ := ((169440119894170491153 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem edgeRightP006NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP006NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP006Factor2548 * embedPair2542
      edgeRightP006Center2548‖ ≤
      ((42360029973542525319 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP006Factor2548, edgeRightP006Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP006Factor2548 * embedPair2542 edgeRightP006Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP006DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP006Factor2548, edgeRightP006Error2548,
      edgeRightP006NormUpper2549]

noncomputable def edgeRightP007NormUpper2549 : ℝ := ((27843335069501722188749694306721 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP007NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP007NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP007Factor2548 * embedPair2542
      edgeRightP007Center2548‖ ≤
      ((27843335069501718510218107012151 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP007Factor2548, edgeRightP007Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP007Factor2548 * embedPair2542 edgeRightP007Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP007DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP007Factor2548, edgeRightP007Error2548,
      edgeRightP007NormUpper2549]

noncomputable def edgeRightP008NormUpper2549 : ℝ := ((11404729393283407834189 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem edgeRightP008NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP008NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP008Factor2548 * embedPair2542
      edgeRightP008Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP008Factor2548, edgeRightP008Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP008Factor2548 * embedPair2542 edgeRightP008Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP008DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP008Factor2548, edgeRightP008Error2548,
      edgeRightP008NormUpper2549]

noncomputable def edgeRightP009NormUpper2549 : ℝ := ((22809475405537218983965 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem edgeRightP009NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP009NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP009Factor2548 * embedPair2542
      edgeRightP009Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP009Factor2548, edgeRightP009Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP009Factor2548 * embedPair2542 edgeRightP009Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP009DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP009Factor2548, edgeRightP009Error2548,
      edgeRightP009NormUpper2549]

noncomputable def edgeRightP010NormUpper2549 : ℝ := ((45618970060964048176441 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP010NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP010NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP010Factor2548 * embedPair2542
      edgeRightP010Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP010Factor2548, edgeRightP010Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP010Factor2548 * embedPair2542 edgeRightP010Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP010DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP010Factor2548, edgeRightP010Error2548,
      edgeRightP010NormUpper2549]

noncomputable def edgeRightP011NormUpper2549 : ℝ := ((45618982895438801095465 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP011NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP011NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP011Factor2548 * embedPair2542
      edgeRightP011Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP011Factor2548, edgeRightP011Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP011Factor2548 * embedPair2542 edgeRightP011Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP011DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP011Factor2548, edgeRightP011Error2548,
      edgeRightP011NormUpper2549]

noncomputable def edgeRightP012NormUpper2549 : ℝ := ((45618996188811026904001 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP012NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP012NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP012Factor2548 * embedPair2542
      edgeRightP012Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP012Factor2548, edgeRightP012Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP012Factor2548 * embedPair2542 edgeRightP012Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP012DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP012Factor2548, edgeRightP012Error2548,
      edgeRightP012NormUpper2549]

noncomputable def edgeRightP013NormUpper2549 : ℝ := ((45619008302866927654155 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP013NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP013NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP013Factor2548 * embedPair2542
      edgeRightP013Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP013Factor2548, edgeRightP013Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP013Factor2548 * embedPair2542 edgeRightP013Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP013DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP013Factor2548, edgeRightP013Error2548,
      edgeRightP013NormUpper2549]

noncomputable def edgeRightP014NormUpper2549 : ℝ := ((45619030748966138638097 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP014NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP014NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP014Factor2548 * embedPair2542
      edgeRightP014Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP014Factor2548, edgeRightP014Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP014Factor2548 * embedPair2542 edgeRightP014Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP014DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP014Factor2548, edgeRightP014Error2548,
      edgeRightP014NormUpper2549]

noncomputable def edgeRightP015NormUpper2549 : ℝ := ((45619046831668091417203 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP015NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP015NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP015Factor2548 * embedPair2542
      edgeRightP015Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP015Factor2548, edgeRightP015Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP015Factor2548 * embedPair2542 edgeRightP015Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP015DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP015Factor2548, edgeRightP015Error2548,
      edgeRightP015NormUpper2549]

noncomputable def edgeRightP016NormUpper2549 : ℝ := ((45619058454282116376825 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP016NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP016NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP016Factor2548 * embedPair2542
      edgeRightP016Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP016Factor2548, edgeRightP016Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP016Factor2548 * embedPair2542 edgeRightP016Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP016DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP016Factor2548, edgeRightP016Error2548,
      edgeRightP016NormUpper2549]

noncomputable def edgeRightP017NormUpper2549 : ℝ := ((45619081030477589573003 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP017NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP017NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP017Factor2548 * embedPair2542
      edgeRightP017Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP017Factor2548, edgeRightP017Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP017Factor2548 * embedPair2542 edgeRightP017Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP017DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP017Factor2548, edgeRightP017Error2548,
      edgeRightP017NormUpper2549]

noncomputable def edgeRightP018NormUpper2549 : ℝ := ((11404772391513690502981 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem edgeRightP018NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP018NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP018Factor2548 * embedPair2542
      edgeRightP018Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP018Factor2548, edgeRightP018Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP018Factor2548 * embedPair2542 edgeRightP018Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP018DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP018Factor2548, edgeRightP018Error2548,
      edgeRightP018NormUpper2549]

noncomputable def edgeRightP019NormUpper2549 : ℝ := ((712798515502547031175 : ℝ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984))

theorem edgeRightP019NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP019NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP019Factor2548 * embedPair2542
      edgeRightP019Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP019Factor2548, edgeRightP019Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP019Factor2548 * embedPair2542 edgeRightP019Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP019DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP019Factor2548, edgeRightP019Error2548,
      edgeRightP019NormUpper2549]

noncomputable def edgeRightP020NormUpper2549 : ℝ := ((11404780441704605665639 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem edgeRightP020NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP020NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP020Factor2548 * embedPair2542
      edgeRightP020Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP020Factor2548, edgeRightP020Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP020Factor2548 * embedPair2542 edgeRightP020Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP020DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP020Factor2548, edgeRightP020Error2548,
      edgeRightP020NormUpper2549]

noncomputable def edgeRightP021NormUpper2549 : ℝ := ((45619135765920945511767 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP021NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP021NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP021Factor2548 * embedPair2542
      edgeRightP021Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP021Factor2548, edgeRightP021Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP021Factor2548 * embedPair2542 edgeRightP021Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP021DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP021Factor2548, edgeRightP021Error2548,
      edgeRightP021NormUpper2549]

noncomputable def edgeRightP022NormUpper2549 : ℝ := ((22809571465588377193053 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem edgeRightP022NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP022NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP022Factor2548 * embedPair2542
      edgeRightP022Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP022Factor2548, edgeRightP022Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP022Factor2548 * embedPair2542 edgeRightP022Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP022DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP022Factor2548, edgeRightP022Error2548,
      edgeRightP022NormUpper2549]

noncomputable def edgeRightP023NormUpper2549 : ℝ := ((11404790897484128632377 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem edgeRightP023NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP023NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP023Factor2548 * embedPair2542
      edgeRightP023Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP023Factor2548, edgeRightP023Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP023Factor2548 * embedPair2542 edgeRightP023Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP023DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP023Factor2548, edgeRightP023Error2548,
      edgeRightP023NormUpper2549]

noncomputable def edgeRightP024NormUpper2549 : ℝ := ((45619173083863814919083 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP024NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP024NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP024Factor2548 * embedPair2542
      edgeRightP024Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP024Factor2548, edgeRightP024Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP024Factor2548 * embedPair2542 edgeRightP024Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP024DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP024Factor2548, edgeRightP024Error2548,
      edgeRightP024NormUpper2549]

noncomputable def edgeRightP025NormUpper2549 : ℝ := ((45619184987504688543133 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP025NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP025NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP025Factor2548 * embedPair2542
      edgeRightP025Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP025Factor2548, edgeRightP025Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP025Factor2548 * embedPair2542 edgeRightP025Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP025DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP025Factor2548, edgeRightP025Error2548,
      edgeRightP025NormUpper2549]

noncomputable def edgeRightP026NormUpper2549 : ℝ := ((45619197152539844442753 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP026NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP026NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP026Factor2548 * embedPair2542
      edgeRightP026Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP026Factor2548, edgeRightP026Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP026Factor2548 * embedPair2542 edgeRightP026Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP026DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP026Factor2548, edgeRightP026Error2548,
      edgeRightP026NormUpper2549]

noncomputable def edgeRightP027NormUpper2549 : ℝ := ((45619214707078308350739 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP027NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP027NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP027Factor2548 * embedPair2542
      edgeRightP027Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP027Factor2548, edgeRightP027Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP027Factor2548 * embedPair2542 edgeRightP027Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP027DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP027Factor2548, edgeRightP027Error2548,
      edgeRightP027NormUpper2549]

noncomputable def edgeRightP028NormUpper2549 : ℝ := ((45619221657160357996833 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeRightP028NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP028NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP028Factor2548 * embedPair2542
      edgeRightP028Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP028Factor2548, edgeRightP028Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP028Factor2548 * embedPair2542 edgeRightP028Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP028DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP028Factor2548, edgeRightP028Error2548,
      edgeRightP028NormUpper2549]

noncomputable def edgeRightP029NormUpper2549 : ℝ := ((22809616119106348189817 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem edgeRightP029NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ edgeRightPosition2548‖ ≤
      edgeRightP029NormUpper2549 := by
  have hc : ‖embedPair2542 edgeRightP029Factor2548 * embedPair2542
      edgeRightP029Center2548‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeRightP029Factor2548, edgeRightP029Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ edgeRightPosition2548)
    (embedPair2542 edgeRightP029Factor2548 * embedPair2542 edgeRightP029Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeRightP029DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeRightP029Factor2548, edgeRightP029Error2548,
      edgeRightP029NormUpper2549]

noncomputable def edgeRightNormUpper2549 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => edgeRightP000NormUpper2549
  | 1 => edgeRightP001NormUpper2549
  | 2 => edgeRightP002NormUpper2549
  | 3 => edgeRightP003NormUpper2549
  | 4 => edgeRightP004NormUpper2549
  | 5 => edgeRightP005NormUpper2549
  | 6 => edgeRightP006NormUpper2549
  | 7 => edgeRightP007NormUpper2549
  | 8 => edgeRightP008NormUpper2549
  | 9 => edgeRightP009NormUpper2549
  | 10 => edgeRightP010NormUpper2549
  | 11 => edgeRightP011NormUpper2549
  | 12 => edgeRightP012NormUpper2549
  | 13 => edgeRightP013NormUpper2549
  | 14 => edgeRightP014NormUpper2549
  | 15 => edgeRightP015NormUpper2549
  | 16 => edgeRightP016NormUpper2549
  | 17 => edgeRightP017NormUpper2549
  | 18 => edgeRightP018NormUpper2549
  | 19 => edgeRightP019NormUpper2549
  | 20 => edgeRightP020NormUpper2549
  | 21 => edgeRightP021NormUpper2549
  | 22 => edgeRightP022NormUpper2549
  | 23 => edgeRightP023NormUpper2549
  | 24 => edgeRightP024NormUpper2549
  | 25 => edgeRightP025NormUpper2549
  | 26 => edgeRightP026NormUpper2549
  | 27 => edgeRightP027NormUpper2549
  | 28 => edgeRightP028NormUpper2549
  | 29 => edgeRightP029NormUpper2549
  | _ => 0

theorem edgeRightNormBound2549 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 i edgeRightPosition2548‖ ≤
        edgeRightNormUpper2549 i := by
  fin_cases i
  · exact edgeRightP000NormBound2549
  · exact edgeRightP001NormBound2549
  · exact edgeRightP002NormBound2549
  · exact edgeRightP003NormBound2549
  · exact edgeRightP004NormBound2549
  · exact edgeRightP005NormBound2549
  · exact edgeRightP006NormBound2549
  · exact edgeRightP007NormBound2549
  · exact edgeRightP008NormBound2549
  · exact edgeRightP009NormBound2549
  · exact edgeRightP010NormBound2549
  · exact edgeRightP011NormBound2549
  · exact edgeRightP012NormBound2549
  · exact edgeRightP013NormBound2549
  · exact edgeRightP014NormBound2549
  · exact edgeRightP015NormBound2549
  · exact edgeRightP016NormBound2549
  · exact edgeRightP017NormBound2549
  · exact edgeRightP018NormBound2549
  · exact edgeRightP019NormBound2549
  · exact edgeRightP020NormBound2549
  · exact edgeRightP021NormBound2549
  · exact edgeRightP022NormBound2549
  · exact edgeRightP023NormBound2549
  · exact edgeRightP024NormBound2549
  · exact edgeRightP025NormBound2549
  · exact edgeRightP026NormBound2549
  · exact edgeRightP027NormBound2549
  · exact edgeRightP028NormBound2549
  · exact edgeRightP029NormBound2549

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.edgeRightP000NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP001NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP002NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP003NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP004NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP005NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP006NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP007NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP008NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP009NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP010NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP011NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP012NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP013NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP014NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP015NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP016NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP017NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP018NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP019NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP020NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP021NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP022NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP023NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP024NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP025NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP026NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP027NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP028NormBound2549
#print axioms ConnesWeilRH.Dev.edgeRightP029NormBound2549
