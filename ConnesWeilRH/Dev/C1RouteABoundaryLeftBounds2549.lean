import ConnesWeilRH.Dev.C1RouteABoundaryLeft2548
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def edgeLeftP000NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP000NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP000NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP000Factor2548 * embedPair2542 edgeLeftP000Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP000Factor2548, edgeLeftP000Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP000Factor2548 * embedPair2542 edgeLeftP000Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP000DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP000Factor2548, edgeLeftP000Error2548,
      edgeLeftP000NormUpper2549]

noncomputable def edgeLeftP001NormUpper2549 : ℝ := ((186420741 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem edgeLeftP001NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP001NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP001Factor2548 * embedPair2542 edgeLeftP001Center2548‖
      ≤
      ((222434561 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP001Factor2548, edgeLeftP001Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP001Factor2548 * embedPair2542 edgeLeftP001Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP001DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP001Factor2548, edgeLeftP001Error2548,
      edgeLeftP001NormUpper2549]

noncomputable def edgeLeftP002NormUpper2549 : ℝ := ((110130323641529837951625809 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP002NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP002NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP002Factor2548 * embedPair2542 edgeLeftP002Center2548‖
      ≤
      ((110130323641529315156074145 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP002Factor2548, edgeLeftP002Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP002Factor2548 * embedPair2542 edgeLeftP002Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP002DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP002Factor2548, edgeLeftP002Error2548,
      edgeLeftP002NormUpper2549]

noncomputable def edgeLeftP003NormUpper2549 : ℝ := ((385700539197020624901761462879681 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem edgeLeftP003NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP003NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP003Factor2548 * embedPair2542 edgeLeftP003Center2548‖
      ≤
      ((771401078394037952310190327927081 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP003Factor2548, edgeLeftP003Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP003Factor2548 * embedPair2542 edgeLeftP003Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP003DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP003Factor2548, edgeLeftP003Error2548,
      edgeLeftP003NormUpper2549]

noncomputable def edgeLeftP004NormUpper2549 : ℝ := ((167516612222054458663584796683073605 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem edgeLeftP004NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP004NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP004Factor2548 * embedPair2542 edgeLeftP004Center2548‖
      ≤
      ((335033224444107493234479391211615069 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP004Factor2548, edgeLeftP004Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP004Factor2548 * embedPair2542 edgeLeftP004Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP004DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP004Factor2548, edgeLeftP004Error2548,
      edgeLeftP004NormUpper2549]

noncomputable def edgeLeftP005NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP005NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP005NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP005Factor2548 * embedPair2542 edgeLeftP005Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP005Factor2548, edgeLeftP005Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP005Factor2548 * embedPair2542 edgeLeftP005Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP005DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP005Factor2548, edgeLeftP005Error2548,
      edgeLeftP005NormUpper2549]

noncomputable def edgeLeftP006NormUpper2549 : ℝ := ((155703987299712143743 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem edgeLeftP006NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP006NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP006Factor2548 * embedPair2542 edgeLeftP006Center2548‖
      ≤
      ((311407974599423507907 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP006Factor2548, edgeLeftP006Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP006Factor2548 * embedPair2542 edgeLeftP006Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP006DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP006Factor2548, edgeLeftP006Error2548,
      edgeLeftP006NormUpper2549]

noncomputable def edgeLeftP007NormUpper2549 : ℝ := ((27421781294400755873396553172483 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP007NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP007NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP007Factor2548 * embedPair2542 edgeLeftP007Center2548‖
      ≤
      ((27421781294400752249483688292697 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP007Factor2548, edgeLeftP007Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP007Factor2548 * embedPair2542 edgeLeftP007Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP007DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP007Factor2548, edgeLeftP007Error2548,
      edgeLeftP007NormUpper2549]

noncomputable def edgeLeftP008NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP008NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP008NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP008Factor2548 * embedPair2542 edgeLeftP008Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP008Factor2548, edgeLeftP008Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP008Factor2548 * embedPair2542 edgeLeftP008Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP008DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP008Factor2548, edgeLeftP008Error2548,
      edgeLeftP008NormUpper2549]

noncomputable def edgeLeftP009NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP009NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP009NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP009Factor2548 * embedPair2542 edgeLeftP009Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP009Factor2548, edgeLeftP009Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP009Factor2548 * embedPair2542 edgeLeftP009Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP009DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP009Factor2548, edgeLeftP009Error2548,
      edgeLeftP009NormUpper2549]

noncomputable def edgeLeftP010NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP010NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP010NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP010Factor2548 * embedPair2542 edgeLeftP010Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP010Factor2548, edgeLeftP010Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP010Factor2548 * embedPair2542 edgeLeftP010Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP010DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP010Factor2548, edgeLeftP010Error2548,
      edgeLeftP010NormUpper2549]

noncomputable def edgeLeftP011NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP011NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP011NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP011Factor2548 * embedPair2542 edgeLeftP011Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP011Factor2548, edgeLeftP011Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP011Factor2548 * embedPair2542 edgeLeftP011Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP011DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP011Factor2548, edgeLeftP011Error2548,
      edgeLeftP011NormUpper2549]

noncomputable def edgeLeftP012NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP012NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP012NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP012Factor2548 * embedPair2542 edgeLeftP012Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP012Factor2548, edgeLeftP012Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP012Factor2548 * embedPair2542 edgeLeftP012Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP012DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP012Factor2548, edgeLeftP012Error2548,
      edgeLeftP012NormUpper2549]

noncomputable def edgeLeftP013NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP013NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP013NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP013Factor2548 * embedPair2542 edgeLeftP013Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP013Factor2548, edgeLeftP013Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP013Factor2548 * embedPair2542 edgeLeftP013Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP013DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP013Factor2548, edgeLeftP013Error2548,
      edgeLeftP013NormUpper2549]

noncomputable def edgeLeftP014NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP014NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP014NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP014Factor2548 * embedPair2542 edgeLeftP014Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP014Factor2548, edgeLeftP014Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP014Factor2548 * embedPair2542 edgeLeftP014Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP014DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP014Factor2548, edgeLeftP014Error2548,
      edgeLeftP014NormUpper2549]

noncomputable def edgeLeftP015NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP015NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP015NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP015Factor2548 * embedPair2542 edgeLeftP015Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP015Factor2548, edgeLeftP015Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP015Factor2548 * embedPair2542 edgeLeftP015Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP015DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP015Factor2548, edgeLeftP015Error2548,
      edgeLeftP015NormUpper2549]

noncomputable def edgeLeftP016NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP016NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP016NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP016Factor2548 * embedPair2542 edgeLeftP016Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP016Factor2548, edgeLeftP016Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP016Factor2548 * embedPair2542 edgeLeftP016Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP016DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP016Factor2548, edgeLeftP016Error2548,
      edgeLeftP016NormUpper2549]

noncomputable def edgeLeftP017NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP017NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP017NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP017Factor2548 * embedPair2542 edgeLeftP017Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP017Factor2548, edgeLeftP017Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP017Factor2548 * embedPair2542 edgeLeftP017Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP017DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP017Factor2548, edgeLeftP017Error2548,
      edgeLeftP017NormUpper2549]

noncomputable def edgeLeftP018NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP018NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP018NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP018Factor2548 * embedPair2542 edgeLeftP018Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP018Factor2548, edgeLeftP018Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP018Factor2548 * embedPair2542 edgeLeftP018Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP018DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP018Factor2548, edgeLeftP018Error2548,
      edgeLeftP018NormUpper2549]

noncomputable def edgeLeftP019NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP019NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP019NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP019Factor2548 * embedPair2542 edgeLeftP019Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP019Factor2548, edgeLeftP019Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP019Factor2548 * embedPair2542 edgeLeftP019Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP019DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP019Factor2548, edgeLeftP019Error2548,
      edgeLeftP019NormUpper2549]

noncomputable def edgeLeftP020NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP020NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP020NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP020Factor2548 * embedPair2542 edgeLeftP020Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP020Factor2548, edgeLeftP020Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP020Factor2548 * embedPair2542 edgeLeftP020Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP020DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP020Factor2548, edgeLeftP020Error2548,
      edgeLeftP020NormUpper2549]

noncomputable def edgeLeftP021NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP021NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP021NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP021Factor2548 * embedPair2542 edgeLeftP021Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP021Factor2548, edgeLeftP021Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP021Factor2548 * embedPair2542 edgeLeftP021Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP021DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP021Factor2548, edgeLeftP021Error2548,
      edgeLeftP021NormUpper2549]

noncomputable def edgeLeftP022NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP022NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP022NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP022Factor2548 * embedPair2542 edgeLeftP022Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP022Factor2548, edgeLeftP022Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP022Factor2548 * embedPair2542 edgeLeftP022Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP022DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP022Factor2548, edgeLeftP022Error2548,
      edgeLeftP022NormUpper2549]

noncomputable def edgeLeftP023NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP023NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP023NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP023Factor2548 * embedPair2542 edgeLeftP023Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP023Factor2548, edgeLeftP023Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP023Factor2548 * embedPair2542 edgeLeftP023Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP023DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP023Factor2548, edgeLeftP023Error2548,
      edgeLeftP023NormUpper2549]

noncomputable def edgeLeftP024NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP024NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP024NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP024Factor2548 * embedPair2542 edgeLeftP024Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP024Factor2548, edgeLeftP024Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP024Factor2548 * embedPair2542 edgeLeftP024Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP024DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP024Factor2548, edgeLeftP024Error2548,
      edgeLeftP024NormUpper2549]

noncomputable def edgeLeftP025NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP025NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP025NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP025Factor2548 * embedPair2542 edgeLeftP025Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP025Factor2548, edgeLeftP025Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP025Factor2548 * embedPair2542 edgeLeftP025Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP025DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP025Factor2548, edgeLeftP025Error2548,
      edgeLeftP025NormUpper2549]

noncomputable def edgeLeftP026NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP026NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP026NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP026Factor2548 * embedPair2542 edgeLeftP026Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP026Factor2548, edgeLeftP026Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP026Factor2548 * embedPair2542 edgeLeftP026Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP026DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP026Factor2548, edgeLeftP026Error2548,
      edgeLeftP026NormUpper2549]

noncomputable def edgeLeftP027NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP027NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP027NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP027Factor2548 * embedPair2542 edgeLeftP027Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP027Factor2548, edgeLeftP027Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP027Factor2548 * embedPair2542 edgeLeftP027Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP027DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP027Factor2548, edgeLeftP027Error2548,
      edgeLeftP027NormUpper2549]

noncomputable def edgeLeftP028NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP028NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP028NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP028Factor2548 * embedPair2542 edgeLeftP028Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP028Factor2548, edgeLeftP028Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP028Factor2548 * embedPair2542 edgeLeftP028Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP028DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP028Factor2548, edgeLeftP028Error2548,
      edgeLeftP028NormUpper2549]

noncomputable def edgeLeftP029NormUpper2549 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem edgeLeftP029NormBound2549 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ edgeLeftPosition2548‖ ≤
      edgeLeftP029NormUpper2549 := by
  have hc : ‖embedPair2542 edgeLeftP029Factor2548 * embedPair2542 edgeLeftP029Center2548‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, edgeLeftP029Factor2548, edgeLeftP029Center2548,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ edgeLeftPosition2548)
    (embedPair2542 edgeLeftP029Factor2548 * embedPair2542 edgeLeftP029Center2548) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add edgeLeftP029DerivativeError2548 hc)).trans
  norm_num [pairMagnitude2542, edgeLeftP029Factor2548, edgeLeftP029Error2548,
      edgeLeftP029NormUpper2549]

noncomputable def edgeLeftNormUpper2549 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => edgeLeftP000NormUpper2549
  | 1 => edgeLeftP001NormUpper2549
  | 2 => edgeLeftP002NormUpper2549
  | 3 => edgeLeftP003NormUpper2549
  | 4 => edgeLeftP004NormUpper2549
  | 5 => edgeLeftP005NormUpper2549
  | 6 => edgeLeftP006NormUpper2549
  | 7 => edgeLeftP007NormUpper2549
  | 8 => edgeLeftP008NormUpper2549
  | 9 => edgeLeftP009NormUpper2549
  | 10 => edgeLeftP010NormUpper2549
  | 11 => edgeLeftP011NormUpper2549
  | 12 => edgeLeftP012NormUpper2549
  | 13 => edgeLeftP013NormUpper2549
  | 14 => edgeLeftP014NormUpper2549
  | 15 => edgeLeftP015NormUpper2549
  | 16 => edgeLeftP016NormUpper2549
  | 17 => edgeLeftP017NormUpper2549
  | 18 => edgeLeftP018NormUpper2549
  | 19 => edgeLeftP019NormUpper2549
  | 20 => edgeLeftP020NormUpper2549
  | 21 => edgeLeftP021NormUpper2549
  | 22 => edgeLeftP022NormUpper2549
  | 23 => edgeLeftP023NormUpper2549
  | 24 => edgeLeftP024NormUpper2549
  | 25 => edgeLeftP025NormUpper2549
  | 26 => edgeLeftP026NormUpper2549
  | 27 => edgeLeftP027NormUpper2549
  | 28 => edgeLeftP028NormUpper2549
  | 29 => edgeLeftP029NormUpper2549
  | _ => 0

theorem edgeLeftNormBound2549 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 i edgeLeftPosition2548‖ ≤
        edgeLeftNormUpper2549 i := by
  fin_cases i
  · exact edgeLeftP000NormBound2549
  · exact edgeLeftP001NormBound2549
  · exact edgeLeftP002NormBound2549
  · exact edgeLeftP003NormBound2549
  · exact edgeLeftP004NormBound2549
  · exact edgeLeftP005NormBound2549
  · exact edgeLeftP006NormBound2549
  · exact edgeLeftP007NormBound2549
  · exact edgeLeftP008NormBound2549
  · exact edgeLeftP009NormBound2549
  · exact edgeLeftP010NormBound2549
  · exact edgeLeftP011NormBound2549
  · exact edgeLeftP012NormBound2549
  · exact edgeLeftP013NormBound2549
  · exact edgeLeftP014NormBound2549
  · exact edgeLeftP015NormBound2549
  · exact edgeLeftP016NormBound2549
  · exact edgeLeftP017NormBound2549
  · exact edgeLeftP018NormBound2549
  · exact edgeLeftP019NormBound2549
  · exact edgeLeftP020NormBound2549
  · exact edgeLeftP021NormBound2549
  · exact edgeLeftP022NormBound2549
  · exact edgeLeftP023NormBound2549
  · exact edgeLeftP024NormBound2549
  · exact edgeLeftP025NormBound2549
  · exact edgeLeftP026NormBound2549
  · exact edgeLeftP027NormBound2549
  · exact edgeLeftP028NormBound2549
  · exact edgeLeftP029NormBound2549

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.edgeLeftP000NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP001NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP002NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP003NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP004NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP005NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP006NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP007NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP008NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP009NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP010NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP011NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP012NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP013NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP014NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP015NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP016NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP017NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP018NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP019NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP020NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP021NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP022NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP023NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP024NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP025NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP026NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP027NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP028NormBound2549
#print axioms ConnesWeilRH.Dev.edgeLeftP029NormBound2549
