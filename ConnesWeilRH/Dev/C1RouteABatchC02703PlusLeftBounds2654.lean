import ConnesWeilRH.Dev.C1RouteABatchN02703Plus2654
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC02703PlusLeftP000NormUpper2654 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP000NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP000NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP000Factor2654 * embedPair2542
      batchN02703PlusP000Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP000Factor2654, batchN02703PlusP000Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP000Factor2654 * embedPair2542 batchN02703PlusP000Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP000DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP000Factor2654, batchN02703PlusP000Error2654,
      batchC02703PlusLeftP000NormUpper2654]

noncomputable def batchC02703PlusLeftP001NormUpper2654 : ℝ := ((690290097 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP001NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP001NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP001Factor2654 * embedPair2542
      batchN02703PlusP001Center2654‖
      ≤
      ((102699921 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP001Factor2654, batchN02703PlusP001Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP001Factor2654 * embedPair2542 batchN02703PlusP001Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP001DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP001Factor2654, batchN02703PlusP001Error2654,
      batchC02703PlusLeftP001NormUpper2654]

noncomputable def batchC02703PlusLeftP002NormUpper2654 : ℝ := ((64110006635739135109983413 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703PlusLeftP002NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP002NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP002Factor2654 * embedPair2542
      batchN02703PlusP002Center2654‖
      ≤
      ((32055003317869412209753181 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP002Factor2654, batchN02703PlusP002Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP002Factor2654 * embedPair2542 batchN02703PlusP002Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP002DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP002Factor2654, batchN02703PlusP002Error2654,
      batchC02703PlusLeftP002NormUpper2654]

noncomputable def batchC02703PlusLeftP003NormUpper2654 : ℝ := ((407722974651631805773895434170453
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703PlusLeftP003NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP003NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP003Factor2654 * embedPair2542
      batchN02703PlusP003Center2654‖
      ≤
      ((203861487325815012365860955527867 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP003Factor2654, batchN02703PlusP003Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP003Factor2654 * embedPair2542 batchN02703PlusP003Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP003DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP003Factor2654, batchN02703PlusP003Error2654,
      batchC02703PlusLeftP003NormUpper2654]

noncomputable def batchC02703PlusLeftP004NormUpper2654 : ℝ :=
    ((344939430666906449789773201983232489 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP004NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP004NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP004Factor2654 * embedPair2542
      batchN02703PlusP004Center2654‖
      ≤
      ((344939430666904953264309915807750509 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP004Factor2654, batchN02703PlusP004Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP004Factor2654 * embedPair2542 batchN02703PlusP004Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP004DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP004Factor2654, batchN02703PlusP004Error2654,
      batchC02703PlusLeftP004NormUpper2654]

noncomputable def batchC02703PlusLeftP005NormUpper2654 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP005NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP005NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP005Factor2654 * embedPair2542
      batchN02703PlusP005Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP005Factor2654, batchN02703PlusP005Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP005Factor2654 * embedPair2542 batchN02703PlusP005Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP005DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP005Factor2654, batchN02703PlusP005Error2654,
      batchC02703PlusLeftP005NormUpper2654]

noncomputable def batchC02703PlusLeftP006NormUpper2654 : ℝ := ((401002650748614001017 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP006NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP006NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP006Factor2654 * embedPair2542
      batchN02703PlusP006Center2654‖
      ≤
      ((401002650748613219091 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP006Factor2654, batchN02703PlusP006Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP006Factor2654 * embedPair2542 batchN02703PlusP006Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP006DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP006Factor2654, batchN02703PlusP006Error2654,
      batchC02703PlusLeftP006NormUpper2654]

noncomputable def batchC02703PlusLeftP007NormUpper2654 : ℝ := ((14352083678991988025223891946381 :
    ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703PlusLeftP007NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP007NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP007Factor2654 * embedPair2542
      batchN02703PlusP007Center2654‖
      ≤
      ((14352083678991986130216288398661 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP007Factor2654, batchN02703PlusP007Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP007Factor2654 * embedPair2542 batchN02703PlusP007Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP007DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP007Factor2654, batchN02703PlusP007Error2654,
      batchC02703PlusLeftP007NormUpper2654]

noncomputable def batchC02703PlusLeftP008NormUpper2654 : ℝ := ((31274086858913771191 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703PlusLeftP008NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP008NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP008Factor2654 * embedPair2542
      batchN02703PlusP008Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP008Factor2654, batchN02703PlusP008Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP008Factor2654 * embedPair2542 batchN02703PlusP008Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP008DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP008Factor2654, batchN02703PlusP008Error2654,
      batchC02703PlusLeftP008NormUpper2654]

noncomputable def batchC02703PlusLeftP009NormUpper2654 : ℝ := ((62548583972920664215 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP009NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP009NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP009Factor2654 * embedPair2542
      batchN02703PlusP009Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP009Factor2654, batchN02703PlusP009Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP009Factor2654 * embedPair2542 batchN02703PlusP009Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP009DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP009Factor2654, batchN02703PlusP009Error2654,
      batchC02703PlusLeftP009NormUpper2654]

noncomputable def batchC02703PlusLeftP010NormUpper2654 : ℝ := ((62548821573109748543 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP010NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP010NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP010Factor2654 * embedPair2542
      batchN02703PlusP010Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP010Factor2654, batchN02703PlusP010Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP010Factor2654 * embedPair2542 batchN02703PlusP010Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP010DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP010Factor2654, batchN02703PlusP010Error2654,
      batchC02703PlusLeftP010NormUpper2654]

noncomputable def batchC02703PlusLeftP011NormUpper2654 : ℝ := ((15637244996983869701 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02703PlusLeftP011NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP011NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP011Factor2654 * embedPair2542
      batchN02703PlusP011Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP011Factor2654, batchN02703PlusP011Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP011Factor2654 * embedPair2542 batchN02703PlusP011Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP011DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP011Factor2654, batchN02703PlusP011Error2654,
      batchC02703PlusLeftP011NormUpper2654]

noncomputable def batchC02703PlusLeftP012NormUpper2654 : ℝ := ((62549144066642885447 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP012NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP012NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP012Factor2654 * embedPair2542
      batchN02703PlusP012Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP012Factor2654, batchN02703PlusP012Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP012Factor2654 * embedPair2542 batchN02703PlusP012Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP012DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP012Factor2654, batchN02703PlusP012Error2654,
      batchC02703PlusLeftP012NormUpper2654]

noncomputable def batchC02703PlusLeftP013NormUpper2654 : ℝ := ((15637323397237435555 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02703PlusLeftP013NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP013NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP013Factor2654 * embedPair2542
      batchN02703PlusP013Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP013Factor2654, batchN02703PlusP013Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP013Factor2654 * embedPair2542 batchN02703PlusP013Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP013DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP013Factor2654, batchN02703PlusP013Error2654,
      batchC02703PlusLeftP013NormUpper2654]

noncomputable def batchC02703PlusLeftP014NormUpper2654 : ℝ := ((62549570637840724381 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP014NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP014NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP014Factor2654 * embedPair2542
      batchN02703PlusP014Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP014Factor2654, batchN02703PlusP014Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP014Factor2654 * embedPair2542 batchN02703PlusP014Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP014DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP014Factor2654, batchN02703PlusP014Error2654,
      batchC02703PlusLeftP014NormUpper2654]

noncomputable def batchC02703PlusLeftP015NormUpper2654 : ℝ := ((7818721142976377181 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem batchC02703PlusLeftP015NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP015NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP015Factor2654 * embedPair2542
      batchN02703PlusP015Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP015Factor2654, batchN02703PlusP015Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP015Factor2654 * embedPair2542 batchN02703PlusP015Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP015DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP015Factor2654, batchN02703PlusP015Error2654,
      batchC02703PlusLeftP015NormUpper2654]

noncomputable def batchC02703PlusLeftP016NormUpper2654 : ℝ := ((15637478149866417745 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02703PlusLeftP016NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP016NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP016Factor2654 * embedPair2542
      batchN02703PlusP016Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP016Factor2654, batchN02703PlusP016Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP016Factor2654 * embedPair2542 batchN02703PlusP016Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP016DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP016Factor2654, batchN02703PlusP016Error2654,
      batchC02703PlusLeftP016NormUpper2654]

noncomputable def batchC02703PlusLeftP017NormUpper2654 : ℝ := ((62550191252479412407 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP017NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP017NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP017Factor2654 * embedPair2542
      batchN02703PlusP017Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP017Factor2654, batchN02703PlusP017Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP017Factor2654 * embedPair2542 batchN02703PlusP017Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP017DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP017Factor2654, batchN02703PlusP017Error2654,
      batchC02703PlusLeftP017NormUpper2654]

noncomputable def batchC02703PlusLeftP018NormUpper2654 : ℝ := ((62550296605038907527 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP018NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP018NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP018Factor2654 * embedPair2542
      batchN02703PlusP018Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP018Factor2654, batchN02703PlusP018Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP018Factor2654 * embedPair2542 batchN02703PlusP018Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP018DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP018Factor2654, batchN02703PlusP018Error2654,
      batchC02703PlusLeftP018NormUpper2654]

noncomputable def batchC02703PlusLeftP019NormUpper2654 : ℝ := ((62550487005486042923 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP019NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP019NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP019Factor2654 * embedPair2542
      batchN02703PlusP019Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP019Factor2654, batchN02703PlusP019Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP019Factor2654 * embedPair2542 batchN02703PlusP019Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP019DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP019Factor2654, batchN02703PlusP019Error2654,
      batchC02703PlusLeftP019NormUpper2654]

noncomputable def batchC02703PlusLeftP020NormUpper2654 : ℝ := ((62550694050310749327 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP020NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP020NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP020Factor2654 * embedPair2542
      batchN02703PlusP020Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP020Factor2654, batchN02703PlusP020Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP020Factor2654 * embedPair2542 batchN02703PlusP020Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP020DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP020Factor2654, batchN02703PlusP020Error2654,
      batchC02703PlusLeftP020NormUpper2654]

noncomputable def batchC02703PlusLeftP021NormUpper2654 : ℝ := ((15637716709240176507 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02703PlusLeftP021NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP021NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP021Factor2654 * embedPair2542
      batchN02703PlusP021Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP021Factor2654, batchN02703PlusP021Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP021Factor2654 * embedPair2542 batchN02703PlusP021Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP021DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP021Factor2654, batchN02703PlusP021Error2654,
      batchC02703PlusLeftP021NormUpper2654]

noncomputable def batchC02703PlusLeftP022NormUpper2654 : ℝ := ((31275477637708453315 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703PlusLeftP022NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP022NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP022Factor2654 * embedPair2542
      batchN02703PlusP022Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP022Factor2654, batchN02703PlusP022Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP022Factor2654 * embedPair2542 batchN02703PlusP022Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP022DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP022Factor2654, batchN02703PlusP022Error2654,
      batchC02703PlusLeftP022NormUpper2654]

noncomputable def batchC02703PlusLeftP023NormUpper2654 : ℝ := ((62551210259453313831 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP023NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP023NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP023Factor2654 * embedPair2542
      batchN02703PlusP023Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP023Factor2654, batchN02703PlusP023Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP023Factor2654 * embedPair2542 batchN02703PlusP023Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP023DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP023Factor2654, batchN02703PlusP023Error2654,
      batchC02703PlusLeftP023NormUpper2654]

noncomputable def batchC02703PlusLeftP024NormUpper2654 : ℝ := ((62551327439558257661 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP024NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP024NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP024Factor2654 * embedPair2542
      batchN02703PlusP024Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP024Factor2654, batchN02703PlusP024Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP024Factor2654 * embedPair2542 batchN02703PlusP024Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP024DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP024Factor2654, batchN02703PlusP024Error2654,
      batchC02703PlusLeftP024NormUpper2654]

noncomputable def batchC02703PlusLeftP025NormUpper2654 : ℝ := ((31275737180850485049 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703PlusLeftP025NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP025NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP025Factor2654 * embedPair2542
      batchN02703PlusP025Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP025Factor2654, batchN02703PlusP025Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP025Factor2654 * embedPair2542 batchN02703PlusP025Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP025DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP025Factor2654, batchN02703PlusP025Error2654,
      batchC02703PlusLeftP025NormUpper2654]

noncomputable def batchC02703PlusLeftP026NormUpper2654 : ℝ := ((62551624509923274109 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02703PlusLeftP026NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP026NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP026Factor2654 * embedPair2542
      batchN02703PlusP026Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP026Factor2654, batchN02703PlusP026Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP026Factor2654 * embedPair2542 batchN02703PlusP026Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP026DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP026Factor2654, batchN02703PlusP026Error2654,
      batchC02703PlusLeftP026NormUpper2654]

noncomputable def batchC02703PlusLeftP027NormUpper2654 : ℝ := ((31275920589139464807 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703PlusLeftP027NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP027NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP027Factor2654 * embedPair2542
      batchN02703PlusP027Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP027Factor2654, batchN02703PlusP027Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP027Factor2654 * embedPair2542 batchN02703PlusP027Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP027DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP027Factor2654, batchN02703PlusP027Error2654,
      batchC02703PlusLeftP027NormUpper2654]

noncomputable def batchC02703PlusLeftP028NormUpper2654 : ℝ := ((31275963480061803093 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703PlusLeftP028NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP028NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP028Factor2654 * embedPair2542
      batchN02703PlusP028Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP028Factor2654, batchN02703PlusP028Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP028Factor2654 * embedPair2542 batchN02703PlusP028Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP028DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP028Factor2654, batchN02703PlusP028Error2654,
      batchC02703PlusLeftP028NormUpper2654]

noncomputable def batchC02703PlusLeftP029NormUpper2654 : ℝ := ((31276028778661975255 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02703PlusLeftP029NormBound2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02703PlusPosition2654‖ ≤
      batchC02703PlusLeftP029NormUpper2654 := by
  have hc : ‖embedPair2542 batchN02703PlusP029Factor2654 * embedPair2542
      batchN02703PlusP029Center2654‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP029Factor2654, batchN02703PlusP029Center2654,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02703PlusPosition2654)
    (embedPair2542 batchN02703PlusP029Factor2654 * embedPair2542 batchN02703PlusP029Center2654) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP029DerivativeError2654 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP029Factor2654, batchN02703PlusP029Error2654,
      batchC02703PlusLeftP029NormUpper2654]

noncomputable def batchC02703PlusLeftNormUpper2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02703PlusLeftP000NormUpper2654
  | 1 => batchC02703PlusLeftP001NormUpper2654
  | 2 => batchC02703PlusLeftP002NormUpper2654
  | 3 => batchC02703PlusLeftP003NormUpper2654
  | 4 => batchC02703PlusLeftP004NormUpper2654
  | 5 => batchC02703PlusLeftP005NormUpper2654
  | 6 => batchC02703PlusLeftP006NormUpper2654
  | 7 => batchC02703PlusLeftP007NormUpper2654
  | 8 => batchC02703PlusLeftP008NormUpper2654
  | 9 => batchC02703PlusLeftP009NormUpper2654
  | 10 => batchC02703PlusLeftP010NormUpper2654
  | 11 => batchC02703PlusLeftP011NormUpper2654
  | 12 => batchC02703PlusLeftP012NormUpper2654
  | 13 => batchC02703PlusLeftP013NormUpper2654
  | 14 => batchC02703PlusLeftP014NormUpper2654
  | 15 => batchC02703PlusLeftP015NormUpper2654
  | 16 => batchC02703PlusLeftP016NormUpper2654
  | 17 => batchC02703PlusLeftP017NormUpper2654
  | 18 => batchC02703PlusLeftP018NormUpper2654
  | 19 => batchC02703PlusLeftP019NormUpper2654
  | 20 => batchC02703PlusLeftP020NormUpper2654
  | 21 => batchC02703PlusLeftP021NormUpper2654
  | 22 => batchC02703PlusLeftP022NormUpper2654
  | 23 => batchC02703PlusLeftP023NormUpper2654
  | 24 => batchC02703PlusLeftP024NormUpper2654
  | 25 => batchC02703PlusLeftP025NormUpper2654
  | 26 => batchC02703PlusLeftP026NormUpper2654
  | 27 => batchC02703PlusLeftP027NormUpper2654
  | 28 => batchC02703PlusLeftP028NormUpper2654
  | 29 => batchC02703PlusLeftP029NormUpper2654
  | _ => 0

theorem batchC02703PlusLeftNormBound2654 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 i batchN02703PlusPosition2654‖ ≤
        batchC02703PlusLeftNormUpper2654 i := by
  fin_cases i
  · exact batchC02703PlusLeftP000NormBound2654
  · exact batchC02703PlusLeftP001NormBound2654
  · exact batchC02703PlusLeftP002NormBound2654
  · exact batchC02703PlusLeftP003NormBound2654
  · exact batchC02703PlusLeftP004NormBound2654
  · exact batchC02703PlusLeftP005NormBound2654
  · exact batchC02703PlusLeftP006NormBound2654
  · exact batchC02703PlusLeftP007NormBound2654
  · exact batchC02703PlusLeftP008NormBound2654
  · exact batchC02703PlusLeftP009NormBound2654
  · exact batchC02703PlusLeftP010NormBound2654
  · exact batchC02703PlusLeftP011NormBound2654
  · exact batchC02703PlusLeftP012NormBound2654
  · exact batchC02703PlusLeftP013NormBound2654
  · exact batchC02703PlusLeftP014NormBound2654
  · exact batchC02703PlusLeftP015NormBound2654
  · exact batchC02703PlusLeftP016NormBound2654
  · exact batchC02703PlusLeftP017NormBound2654
  · exact batchC02703PlusLeftP018NormBound2654
  · exact batchC02703PlusLeftP019NormBound2654
  · exact batchC02703PlusLeftP020NormBound2654
  · exact batchC02703PlusLeftP021NormBound2654
  · exact batchC02703PlusLeftP022NormBound2654
  · exact batchC02703PlusLeftP023NormBound2654
  · exact batchC02703PlusLeftP024NormBound2654
  · exact batchC02703PlusLeftP025NormBound2654
  · exact batchC02703PlusLeftP026NormBound2654
  · exact batchC02703PlusLeftP027NormBound2654
  · exact batchC02703PlusLeftP028NormBound2654
  · exact batchC02703PlusLeftP029NormBound2654

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP000NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP001NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP002NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP003NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP004NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP005NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP006NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP007NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP008NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP009NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP010NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP011NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP012NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP013NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP014NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP015NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP016NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP017NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP018NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP019NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP020NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP021NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP022NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP023NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP024NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP025NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP026NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP027NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP028NormBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusLeftP029NormBound2654
