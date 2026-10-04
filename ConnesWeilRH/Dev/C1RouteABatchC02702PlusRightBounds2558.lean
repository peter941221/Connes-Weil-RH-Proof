import ConnesWeilRH.Dev.C1RouteABatchN02703Plus2558
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC02702PlusRightP000NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP000NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP000NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP000Factor2558 * embedPair2542
      batchN02703PlusP000Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP000Factor2558, batchN02703PlusP000Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP000Factor2558 * embedPair2542 batchN02703PlusP000Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP000DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP000Factor2558, batchN02703PlusP000Error2558,
      batchC02702PlusRightP000NormUpper2558]

noncomputable def batchC02702PlusRightP001NormUpper2558 : ℝ := ((690290097 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP001NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP001NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP001Factor2558 * embedPair2542
      batchN02703PlusP001Center2558‖ ≤
      ((102699921 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP001Factor2558, batchN02703PlusP001Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP001Factor2558 * embedPair2542 batchN02703PlusP001Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP001DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP001Factor2558, batchN02703PlusP001Error2558,
      batchC02702PlusRightP001NormUpper2558]

noncomputable def batchC02702PlusRightP002NormUpper2558 : ℝ := ((64110006635739135109983413 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusRightP002NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP002NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP002Factor2558 * embedPair2542
      batchN02703PlusP002Center2558‖ ≤
      ((32055003317869412209753181 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP002Factor2558, batchN02703PlusP002Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP002Factor2558 * embedPair2542 batchN02703PlusP002Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP002DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP002Factor2558, batchN02703PlusP002Error2558,
      batchC02702PlusRightP002NormUpper2558]

noncomputable def batchC02702PlusRightP003NormUpper2558 : ℝ := ((407722974651631805773895434170453
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusRightP003NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP003NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP003Factor2558 * embedPair2542
      batchN02703PlusP003Center2558‖ ≤
      ((203861487325815012365860955527867 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP003Factor2558, batchN02703PlusP003Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP003Factor2558 * embedPair2542 batchN02703PlusP003Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP003DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP003Factor2558, batchN02703PlusP003Error2558,
      batchC02702PlusRightP003NormUpper2558]

noncomputable def batchC02702PlusRightP004NormUpper2558 : ℝ :=
    ((344939430666906449789773201983232489 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP004NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP004NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP004Factor2558 * embedPair2542
      batchN02703PlusP004Center2558‖ ≤
      ((344939430666904953264309915807750509 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP004Factor2558, batchN02703PlusP004Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP004Factor2558 * embedPair2542 batchN02703PlusP004Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP004DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP004Factor2558, batchN02703PlusP004Error2558,
      batchC02702PlusRightP004NormUpper2558]

noncomputable def batchC02702PlusRightP005NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP005NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP005NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP005Factor2558 * embedPair2542
      batchN02703PlusP005Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP005Factor2558, batchN02703PlusP005Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP005Factor2558 * embedPair2542 batchN02703PlusP005Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP005DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP005Factor2558, batchN02703PlusP005Error2558,
      batchC02702PlusRightP005NormUpper2558]

noncomputable def batchC02702PlusRightP006NormUpper2558 : ℝ := ((401002650748614001017 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP006NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP006NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP006Factor2558 * embedPair2542
      batchN02703PlusP006Center2558‖ ≤
      ((401002650748613219091 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP006Factor2558, batchN02703PlusP006Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP006Factor2558 * embedPair2542 batchN02703PlusP006Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP006DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP006Factor2558, batchN02703PlusP006Error2558,
      batchC02702PlusRightP006NormUpper2558]

noncomputable def batchC02702PlusRightP007NormUpper2558 : ℝ := ((14352083678991988025223891946381
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusRightP007NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP007NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP007Factor2558 * embedPair2542
      batchN02703PlusP007Center2558‖ ≤
      ((14352083678991986130216288398661 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP007Factor2558, batchN02703PlusP007Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP007Factor2558 * embedPair2542 batchN02703PlusP007Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP007DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP007Factor2558, batchN02703PlusP007Error2558,
      batchC02702PlusRightP007NormUpper2558]

noncomputable def batchC02702PlusRightP008NormUpper2558 : ℝ := ((31274086858913771191 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusRightP008NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP008NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP008Factor2558 * embedPair2542
      batchN02703PlusP008Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP008Factor2558, batchN02703PlusP008Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP008Factor2558 * embedPair2542 batchN02703PlusP008Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP008DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP008Factor2558, batchN02703PlusP008Error2558,
      batchC02702PlusRightP008NormUpper2558]

noncomputable def batchC02702PlusRightP009NormUpper2558 : ℝ := ((62548583972920664215 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP009NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP009NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP009Factor2558 * embedPair2542
      batchN02703PlusP009Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP009Factor2558, batchN02703PlusP009Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP009Factor2558 * embedPair2542 batchN02703PlusP009Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP009DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP009Factor2558, batchN02703PlusP009Error2558,
      batchC02702PlusRightP009NormUpper2558]

noncomputable def batchC02702PlusRightP010NormUpper2558 : ℝ := ((62548821573109748543 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP010NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP010NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP010Factor2558 * embedPair2542
      batchN02703PlusP010Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP010Factor2558, batchN02703PlusP010Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP010Factor2558 * embedPair2542 batchN02703PlusP010Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP010DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP010Factor2558, batchN02703PlusP010Error2558,
      batchC02702PlusRightP010NormUpper2558]

noncomputable def batchC02702PlusRightP011NormUpper2558 : ℝ := ((15637244996983869701 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702PlusRightP011NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP011NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP011Factor2558 * embedPair2542
      batchN02703PlusP011Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP011Factor2558, batchN02703PlusP011Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP011Factor2558 * embedPair2542 batchN02703PlusP011Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP011DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP011Factor2558, batchN02703PlusP011Error2558,
      batchC02702PlusRightP011NormUpper2558]

noncomputable def batchC02702PlusRightP012NormUpper2558 : ℝ := ((62549144066642885447 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP012NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP012NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP012Factor2558 * embedPair2542
      batchN02703PlusP012Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP012Factor2558, batchN02703PlusP012Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP012Factor2558 * embedPair2542 batchN02703PlusP012Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP012DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP012Factor2558, batchN02703PlusP012Error2558,
      batchC02702PlusRightP012NormUpper2558]

noncomputable def batchC02702PlusRightP013NormUpper2558 : ℝ := ((15637323397237435555 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702PlusRightP013NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP013NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP013Factor2558 * embedPair2542
      batchN02703PlusP013Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP013Factor2558, batchN02703PlusP013Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP013Factor2558 * embedPair2542 batchN02703PlusP013Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP013DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP013Factor2558, batchN02703PlusP013Error2558,
      batchC02702PlusRightP013NormUpper2558]

noncomputable def batchC02702PlusRightP014NormUpper2558 : ℝ := ((62549570637840724381 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP014NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP014NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP014Factor2558 * embedPair2542
      batchN02703PlusP014Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP014Factor2558, batchN02703PlusP014Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP014Factor2558 * embedPair2542 batchN02703PlusP014Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP014DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP014Factor2558, batchN02703PlusP014Error2558,
      batchC02702PlusRightP014NormUpper2558]

noncomputable def batchC02702PlusRightP015NormUpper2558 : ℝ := ((7818721142976377181 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem batchC02702PlusRightP015NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP015NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP015Factor2558 * embedPair2542
      batchN02703PlusP015Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP015Factor2558, batchN02703PlusP015Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP015Factor2558 * embedPair2542 batchN02703PlusP015Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP015DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP015Factor2558, batchN02703PlusP015Error2558,
      batchC02702PlusRightP015NormUpper2558]

noncomputable def batchC02702PlusRightP016NormUpper2558 : ℝ := ((15637478149866417745 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702PlusRightP016NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP016NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP016Factor2558 * embedPair2542
      batchN02703PlusP016Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP016Factor2558, batchN02703PlusP016Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP016Factor2558 * embedPair2542 batchN02703PlusP016Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP016DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP016Factor2558, batchN02703PlusP016Error2558,
      batchC02702PlusRightP016NormUpper2558]

noncomputable def batchC02702PlusRightP017NormUpper2558 : ℝ := ((62550191252479412407 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP017NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP017NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP017Factor2558 * embedPair2542
      batchN02703PlusP017Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP017Factor2558, batchN02703PlusP017Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP017Factor2558 * embedPair2542 batchN02703PlusP017Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP017DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP017Factor2558, batchN02703PlusP017Error2558,
      batchC02702PlusRightP017NormUpper2558]

noncomputable def batchC02702PlusRightP018NormUpper2558 : ℝ := ((62550296605038907527 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP018NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP018NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP018Factor2558 * embedPair2542
      batchN02703PlusP018Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP018Factor2558, batchN02703PlusP018Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP018Factor2558 * embedPair2542 batchN02703PlusP018Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP018DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP018Factor2558, batchN02703PlusP018Error2558,
      batchC02702PlusRightP018NormUpper2558]

noncomputable def batchC02702PlusRightP019NormUpper2558 : ℝ := ((62550487005486042923 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP019NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP019NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP019Factor2558 * embedPair2542
      batchN02703PlusP019Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP019Factor2558, batchN02703PlusP019Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP019Factor2558 * embedPair2542 batchN02703PlusP019Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP019DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP019Factor2558, batchN02703PlusP019Error2558,
      batchC02702PlusRightP019NormUpper2558]

noncomputable def batchC02702PlusRightP020NormUpper2558 : ℝ := ((62550694050310749327 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP020NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP020NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP020Factor2558 * embedPair2542
      batchN02703PlusP020Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP020Factor2558, batchN02703PlusP020Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP020Factor2558 * embedPair2542 batchN02703PlusP020Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP020DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP020Factor2558, batchN02703PlusP020Error2558,
      batchC02702PlusRightP020NormUpper2558]

noncomputable def batchC02702PlusRightP021NormUpper2558 : ℝ := ((15637716709240176507 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702PlusRightP021NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP021NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP021Factor2558 * embedPair2542
      batchN02703PlusP021Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP021Factor2558, batchN02703PlusP021Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP021Factor2558 * embedPair2542 batchN02703PlusP021Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP021DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP021Factor2558, batchN02703PlusP021Error2558,
      batchC02702PlusRightP021NormUpper2558]

noncomputable def batchC02702PlusRightP022NormUpper2558 : ℝ := ((31275477637708453315 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusRightP022NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP022NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP022Factor2558 * embedPair2542
      batchN02703PlusP022Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP022Factor2558, batchN02703PlusP022Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP022Factor2558 * embedPair2542 batchN02703PlusP022Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP022DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP022Factor2558, batchN02703PlusP022Error2558,
      batchC02702PlusRightP022NormUpper2558]

noncomputable def batchC02702PlusRightP023NormUpper2558 : ℝ := ((62551210259453313831 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP023NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP023NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP023Factor2558 * embedPair2542
      batchN02703PlusP023Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP023Factor2558, batchN02703PlusP023Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP023Factor2558 * embedPair2542 batchN02703PlusP023Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP023DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP023Factor2558, batchN02703PlusP023Error2558,
      batchC02702PlusRightP023NormUpper2558]

noncomputable def batchC02702PlusRightP024NormUpper2558 : ℝ := ((62551327439558257661 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP024NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP024NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP024Factor2558 * embedPair2542
      batchN02703PlusP024Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP024Factor2558, batchN02703PlusP024Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP024Factor2558 * embedPair2542 batchN02703PlusP024Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP024DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP024Factor2558, batchN02703PlusP024Error2558,
      batchC02702PlusRightP024NormUpper2558]

noncomputable def batchC02702PlusRightP025NormUpper2558 : ℝ := ((31275737180850485049 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusRightP025NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP025NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP025Factor2558 * embedPair2542
      batchN02703PlusP025Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP025Factor2558, batchN02703PlusP025Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP025Factor2558 * embedPair2542 batchN02703PlusP025Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP025DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP025Factor2558, batchN02703PlusP025Error2558,
      batchC02702PlusRightP025NormUpper2558]

noncomputable def batchC02702PlusRightP026NormUpper2558 : ℝ := ((62551624509923274109 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusRightP026NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP026NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP026Factor2558 * embedPair2542
      batchN02703PlusP026Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP026Factor2558, batchN02703PlusP026Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP026Factor2558 * embedPair2542 batchN02703PlusP026Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP026DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP026Factor2558, batchN02703PlusP026Error2558,
      batchC02702PlusRightP026NormUpper2558]

noncomputable def batchC02702PlusRightP027NormUpper2558 : ℝ := ((31275920589139464807 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusRightP027NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP027NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP027Factor2558 * embedPair2542
      batchN02703PlusP027Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP027Factor2558, batchN02703PlusP027Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP027Factor2558 * embedPair2542 batchN02703PlusP027Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP027DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP027Factor2558, batchN02703PlusP027Error2558,
      batchC02702PlusRightP027NormUpper2558]

noncomputable def batchC02702PlusRightP028NormUpper2558 : ℝ := ((31275963480061803093 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusRightP028NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP028NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP028Factor2558 * embedPair2542
      batchN02703PlusP028Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP028Factor2558, batchN02703PlusP028Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP028Factor2558 * embedPair2542 batchN02703PlusP028Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP028DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP028Factor2558, batchN02703PlusP028Error2558,
      batchC02702PlusRightP028NormUpper2558]

noncomputable def batchC02702PlusRightP029NormUpper2558 : ℝ := ((31276028778661975255 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusRightP029NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02703PlusPosition2558‖ ≤
      batchC02702PlusRightP029NormUpper2558 := by
  have hc : ‖embedPair2542 batchN02703PlusP029Factor2558 * embedPair2542
      batchN02703PlusP029Center2558‖ ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN02703PlusP029Factor2558, batchN02703PlusP029Center2558,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02703PlusPosition2558)
    (embedPair2542 batchN02703PlusP029Factor2558 * embedPair2542 batchN02703PlusP029Center2558) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN02703PlusP029DerivativeError2558 hc)).trans
  norm_num [pairMagnitude2542, batchN02703PlusP029Factor2558, batchN02703PlusP029Error2558,
      batchC02702PlusRightP029NormUpper2558]

noncomputable def batchC02702PlusRightNormUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02702PlusRightP000NormUpper2558
  | 1 => batchC02702PlusRightP001NormUpper2558
  | 2 => batchC02702PlusRightP002NormUpper2558
  | 3 => batchC02702PlusRightP003NormUpper2558
  | 4 => batchC02702PlusRightP004NormUpper2558
  | 5 => batchC02702PlusRightP005NormUpper2558
  | 6 => batchC02702PlusRightP006NormUpper2558
  | 7 => batchC02702PlusRightP007NormUpper2558
  | 8 => batchC02702PlusRightP008NormUpper2558
  | 9 => batchC02702PlusRightP009NormUpper2558
  | 10 => batchC02702PlusRightP010NormUpper2558
  | 11 => batchC02702PlusRightP011NormUpper2558
  | 12 => batchC02702PlusRightP012NormUpper2558
  | 13 => batchC02702PlusRightP013NormUpper2558
  | 14 => batchC02702PlusRightP014NormUpper2558
  | 15 => batchC02702PlusRightP015NormUpper2558
  | 16 => batchC02702PlusRightP016NormUpper2558
  | 17 => batchC02702PlusRightP017NormUpper2558
  | 18 => batchC02702PlusRightP018NormUpper2558
  | 19 => batchC02702PlusRightP019NormUpper2558
  | 20 => batchC02702PlusRightP020NormUpper2558
  | 21 => batchC02702PlusRightP021NormUpper2558
  | 22 => batchC02702PlusRightP022NormUpper2558
  | 23 => batchC02702PlusRightP023NormUpper2558
  | 24 => batchC02702PlusRightP024NormUpper2558
  | 25 => batchC02702PlusRightP025NormUpper2558
  | 26 => batchC02702PlusRightP026NormUpper2558
  | 27 => batchC02702PlusRightP027NormUpper2558
  | 28 => batchC02702PlusRightP028NormUpper2558
  | 29 => batchC02702PlusRightP029NormUpper2558
  | _ => 0

theorem batchC02702PlusRightNormBound2558 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 i batchN02703PlusPosition2558‖ ≤
        batchC02702PlusRightNormUpper2558 i := by
  fin_cases i
  · exact batchC02702PlusRightP000NormBound2558
  · exact batchC02702PlusRightP001NormBound2558
  · exact batchC02702PlusRightP002NormBound2558
  · exact batchC02702PlusRightP003NormBound2558
  · exact batchC02702PlusRightP004NormBound2558
  · exact batchC02702PlusRightP005NormBound2558
  · exact batchC02702PlusRightP006NormBound2558
  · exact batchC02702PlusRightP007NormBound2558
  · exact batchC02702PlusRightP008NormBound2558
  · exact batchC02702PlusRightP009NormBound2558
  · exact batchC02702PlusRightP010NormBound2558
  · exact batchC02702PlusRightP011NormBound2558
  · exact batchC02702PlusRightP012NormBound2558
  · exact batchC02702PlusRightP013NormBound2558
  · exact batchC02702PlusRightP014NormBound2558
  · exact batchC02702PlusRightP015NormBound2558
  · exact batchC02702PlusRightP016NormBound2558
  · exact batchC02702PlusRightP017NormBound2558
  · exact batchC02702PlusRightP018NormBound2558
  · exact batchC02702PlusRightP019NormBound2558
  · exact batchC02702PlusRightP020NormBound2558
  · exact batchC02702PlusRightP021NormBound2558
  · exact batchC02702PlusRightP022NormBound2558
  · exact batchC02702PlusRightP023NormBound2558
  · exact batchC02702PlusRightP024NormBound2558
  · exact batchC02702PlusRightP025NormBound2558
  · exact batchC02702PlusRightP026NormBound2558
  · exact batchC02702PlusRightP027NormBound2558
  · exact batchC02702PlusRightP028NormBound2558
  · exact batchC02702PlusRightP029NormBound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP000NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP001NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP002NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP003NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP004NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP005NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP006NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP007NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP008NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP009NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP010NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP011NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP012NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP013NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP014NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP015NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP016NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP017NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP018NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP019NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP020NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP021NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP022NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP023NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP024NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP025NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP026NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP027NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP028NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusRightP029NormBound2558
