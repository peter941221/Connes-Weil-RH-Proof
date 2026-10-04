import ConnesWeilRH.Dev.C1RouteANeighborRight2557
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC02702PlusLeftP000NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusLeftP000NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP000NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP000Factor2557 * embedPair2542
      neighborRightP000Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP000Factor2557, neighborRightP000Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP000Factor2557 * embedPair2542 neighborRightP000Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP000DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP000Factor2557, neighborRightP000Error2557,
      batchC02702PlusLeftP000NormUpper2558]

noncomputable def batchC02702PlusLeftP001NormUpper2558 : ℝ := ((354098539 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusLeftP001NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP001NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP001Factor2557 * embedPair2542
      neighborRightP001Center2557‖
      ≤
      ((210903027 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP001Factor2557, neighborRightP001Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP001Factor2557 * embedPair2542 neighborRightP001Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP001DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP001Factor2557, neighborRightP001Error2557,
      batchC02702PlusLeftP001NormUpper2558]

noncomputable def batchC02702PlusLeftP002NormUpper2558 : ℝ := ((60947379114243537446184979 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusLeftP002NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP002NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP002Factor2557 * embedPair2542
      neighborRightP002Center2557‖
      ≤
      ((30473689557121621920424773 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP002Factor2557, neighborRightP002Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP002Factor2557 * embedPair2542 neighborRightP002Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP002DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP002Factor2557, neighborRightP002Error2557,
      batchC02702PlusLeftP002NormUpper2558]

noncomputable def batchC02702PlusLeftP003NormUpper2558 : ℝ := ((400254466109616122722483066501435
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusLeftP003NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP003NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP003Factor2557 * embedPair2542
      neighborRightP003Center2557‖
      ≤
      ((800508932219228770596162640654983 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP003Factor2557, neighborRightP003Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP003Factor2557 * embedPair2542 neighborRightP003Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP003DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP003Factor2557, neighborRightP003Error2557,
      batchC02702PlusLeftP003NormUpper2558]

noncomputable def batchC02702PlusLeftP004NormUpper2558 : ℝ :=
    ((85401990378644689989153786410466723 : ℝ)
    /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702PlusLeftP004NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP004NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP004Factor2557 * embedPair2542
      neighborRightP004Center2557‖
      ≤
      ((341607961514577286624284666117268493 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP004Factor2557, neighborRightP004Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP004Factor2557 * embedPair2542 neighborRightP004Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP004DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP004Factor2557, neighborRightP004Error2557,
      batchC02702PlusLeftP004NormUpper2558]

noncomputable def batchC02702PlusLeftP005NormUpper2558 : ℝ := ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusLeftP005NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP005NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP005Factor2557 * embedPair2542
      neighborRightP005Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP005Factor2557, neighborRightP005Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP005Factor2557 * embedPair2542 neighborRightP005Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP005DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP005Factor2557, neighborRightP005Error2557,
      batchC02702PlusLeftP005NormUpper2558]

noncomputable def batchC02702PlusLeftP006NormUpper2558 : ℝ := ((184340995945022460669 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusLeftP006NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP006NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP006Factor2557 * embedPair2542
      neighborRightP006Center2557‖
      ≤
      ((23042624493127758801 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP006Factor2557, neighborRightP006Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP006Factor2557 * embedPair2542 neighborRightP006Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP006DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP006Factor2557, neighborRightP006Error2557,
      batchC02702PlusLeftP006NormUpper2558]

noncomputable def batchC02702PlusLeftP007NormUpper2558 : ℝ := ((28270772714009476255071529886321 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusLeftP007NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP007NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP007Factor2557 * embedPair2542
      neighborRightP007Center2557‖
      ≤
      ((3533846589251184065146938402813 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP007Factor2557, neighborRightP007Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP007Factor2557 * embedPair2542 neighborRightP007Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP007DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP007Factor2557, neighborRightP007Error2557,
      batchC02702PlusLeftP007NormUpper2558]

noncomputable def batchC02702PlusLeftP008NormUpper2558 : ℝ := ((712601848736291815035 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusLeftP008NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP008NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP008Factor2557 * embedPair2542
      neighborRightP008Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP008Factor2557, neighborRightP008Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP008Factor2557 * embedPair2542 neighborRightP008Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP008DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP008Factor2557, neighborRightP008Error2557,
      batchC02702PlusLeftP008NormUpper2558]

noncomputable def batchC02702PlusLeftP009NormUpper2558 : ℝ := ((356301962915841200751 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusLeftP009NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP009NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP009Factor2557 * embedPair2542
      neighborRightP009Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP009Factor2557, neighborRightP009Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP009Factor2557 * embedPair2542 neighborRightP009Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP009DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP009Factor2557, neighborRightP009Error2557,
      batchC02702PlusLeftP009NormUpper2558]

noncomputable def batchC02702PlusLeftP010NormUpper2558 : ℝ := ((356302564394302265389 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusLeftP010NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP010NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP010Factor2557 * embedPair2542
      neighborRightP010Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP010Factor2557, neighborRightP010Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP010Factor2557 * embedPair2542 neighborRightP010Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP010DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP010Factor2557, neighborRightP010Error2557,
      batchC02702PlusLeftP010NormUpper2558]

noncomputable def batchC02702PlusLeftP011NormUpper2558 : ℝ := ((178151482708812484661 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702PlusLeftP011NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP011NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP011Factor2557 * embedPair2542
      neighborRightP011Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP011Factor2557, neighborRightP011Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP011Factor2557 * embedPair2542 neighborRightP011Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP011DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP011Factor2557, neighborRightP011Error2557,
      batchC02702PlusLeftP011NormUpper2558]

noncomputable def batchC02702PlusLeftP012NormUpper2558 : ℝ := ((356303380779324535779 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusLeftP012NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP012NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP012Factor2557 * embedPair2542
      neighborRightP012Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP012Factor2557, neighborRightP012Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP012Factor2557 * embedPair2542 neighborRightP012Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP012DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP012Factor2557, neighborRightP012Error2557,
      batchC02702PlusLeftP012NormUpper2558]

noncomputable def batchC02702PlusLeftP013NormUpper2558 : ℝ := ((712607518584324641697 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusLeftP013NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP013NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP013Factor2557 * embedPair2542
      neighborRightP013Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP013Factor2557, neighborRightP013Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP013Factor2557 * embedPair2542 neighborRightP013Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP013DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP013Factor2557, neighborRightP013Error2557,
      batchC02702PlusLeftP013NormUpper2558]

noncomputable def batchC02702PlusLeftP014NormUpper2558 : ℝ := ((712608921273950982305 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusLeftP014NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP014NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP014Factor2557 * embedPair2542
      neighborRightP014Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP014Factor2557, neighborRightP014Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP014Factor2557 * embedPair2542 neighborRightP014Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP014DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP014Factor2557, neighborRightP014Error2557,
      batchC02702PlusLeftP014NormUpper2558]

noncomputable def batchC02702PlusLeftP015NormUpper2558 : ℝ := ((178152481576177623105 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702PlusLeftP015NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP015NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP015Factor2557 * embedPair2542
      neighborRightP015Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP015Factor2557, neighborRightP015Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP015Factor2557 * embedPair2542 neighborRightP015Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP015DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP015Factor2557, neighborRightP015Error2557,
      batchC02702PlusLeftP015NormUpper2558]

noncomputable def batchC02702PlusLeftP016NormUpper2558 : ℝ := ((712610652617835020151 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusLeftP016NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP016NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP016Factor2557 * embedPair2542
      neighborRightP016Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP016Factor2557, neighborRightP016Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP016Factor2557 * embedPair2542 neighborRightP016Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP016DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP016Factor2557, neighborRightP016Error2557,
      batchC02702PlusLeftP016NormUpper2558]

noncomputable def batchC02702PlusLeftP017NormUpper2558 : ℝ := ((712612063434261100337 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusLeftP017NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP017NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP017Factor2557 * embedPair2542
      neighborRightP017Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP017Factor2557, neighborRightP017Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP017Factor2557 * embedPair2542 neighborRightP017Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP017DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP017Factor2557, neighborRightP017Error2557,
      batchC02702PlusLeftP017NormUpper2558]

noncomputable def batchC02702PlusLeftP018NormUpper2558 : ℝ := ((712612596833446175787 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusLeftP018NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP018NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP018Factor2557 * embedPair2542
      neighborRightP018Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP018Factor2557, neighborRightP018Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP018Factor2557 * embedPair2542 neighborRightP018Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP018DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP018Factor2557, neighborRightP018Error2557,
      batchC02702PlusLeftP018NormUpper2558]

noncomputable def batchC02702PlusLeftP019NormUpper2558 : ℝ := ((178153390207566393769 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702PlusLeftP019NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP019NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP019Factor2557 * embedPair2542
      neighborRightP019Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP019Factor2557, neighborRightP019Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP019Factor2557 * embedPair2542 neighborRightP019Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP019DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP019Factor2557, neighborRightP019Error2557,
      batchC02702PlusLeftP019NormUpper2558]

noncomputable def batchC02702PlusLeftP020NormUpper2558 : ℝ := ((712614609098745796981 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusLeftP020NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP020NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP020Factor2557 * embedPair2542
      neighborRightP020Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP020Factor2557, neighborRightP020Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP020Factor2557 * embedPair2542 neighborRightP020Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP020DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP020Factor2557, neighborRightP020Error2557,
      batchC02702PlusLeftP020NormUpper2558]

noncomputable def batchC02702PlusLeftP021NormUpper2558 : ℝ := ((178153870979745728943 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702PlusLeftP021NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP021NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP021Factor2557 * embedPair2542
      neighborRightP021Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP021Factor2557, neighborRightP021Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP021Factor2557 * embedPair2542 neighborRightP021Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP021DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP021Factor2557, neighborRightP021Error2557,
      batchC02702PlusLeftP021NormUpper2558]

noncomputable def batchC02702PlusLeftP022NormUpper2558 : ℝ := ((44538495730247754395 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

theorem batchC02702PlusLeftP022NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP022NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP022Factor2557 * embedPair2542
      neighborRightP022Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP022Factor2557, neighborRightP022Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP022Factor2557 * embedPair2542 neighborRightP022Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP022DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP022Factor2557, neighborRightP022Error2557,
      batchC02702PlusLeftP022NormUpper2558]

noncomputable def batchC02702PlusLeftP023NormUpper2558 : ℝ := ((178154305668139858845 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702PlusLeftP023NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP023NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP023Factor2557 * embedPair2542
      neighborRightP023Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP023Factor2557, neighborRightP023Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP023Factor2557 * embedPair2542 neighborRightP023Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP023DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP023Factor2557, neighborRightP023Error2557,
      batchC02702PlusLeftP023NormUpper2558]

noncomputable def batchC02702PlusLeftP024NormUpper2558 : ℝ := ((712617815958115309047 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusLeftP024NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP024NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP024Factor2557 * embedPair2542
      neighborRightP024Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP024Factor2557, neighborRightP024Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP024Factor2557 * embedPair2542 neighborRightP024Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP024DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP024Factor2557, neighborRightP024Error2557,
      batchC02702PlusLeftP024NormUpper2558]

noncomputable def batchC02702PlusLeftP025NormUpper2558 : ℝ := ((178154639957217863133 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702PlusLeftP025NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP025NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP025Factor2557 * embedPair2542
      neighborRightP025Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP025Factor2557, neighborRightP025Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP025Factor2557 * embedPair2542 neighborRightP025Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP025DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP025Factor2557, neighborRightP025Error2557,
      batchC02702PlusLeftP025NormUpper2558]

noncomputable def batchC02702PlusLeftP026NormUpper2558 : ℝ := ((356309660017011949897 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC02702PlusLeftP026NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP026NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP026Factor2557 * embedPair2542
      neighborRightP026Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP026Factor2557, neighborRightP026Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP026Factor2557 * embedPair2542 neighborRightP026Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP026DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP026Factor2557, neighborRightP026Error2557,
      batchC02702PlusLeftP026NormUpper2558]

noncomputable def batchC02702PlusLeftP027NormUpper2558 : ℝ := ((712620417033886467781 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC02702PlusLeftP027NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP027NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP027Factor2557 * embedPair2542
      neighborRightP027Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP027Factor2557, neighborRightP027Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP027Factor2557 * embedPair2542 neighborRightP027Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP027DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP027Factor2557, neighborRightP027Error2557,
      batchC02702PlusLeftP027NormUpper2558]

noncomputable def batchC02702PlusLeftP028NormUpper2558 : ℝ := ((2783675200589506045 : ℝ) /
        (570899 * 10^40
        + 770823839524233143877797980545530986496))

theorem batchC02702PlusLeftP028NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP028NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP028Factor2557 * embedPair2542
      neighborRightP028Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP028Factor2557, neighborRightP028Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP028Factor2557 * embedPair2542 neighborRightP028Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP028DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP028Factor2557, neighborRightP028Error2557,
      batchC02702PlusLeftP028NormUpper2558]

noncomputable def batchC02702PlusLeftP029NormUpper2558 : ℝ := ((178155378142590829865 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC02702PlusLeftP029NormBound2558 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ neighborRightPosition2557‖ ≤
      batchC02702PlusLeftP029NormUpper2558 := by
  have hc : ‖embedPair2542 neighborRightP029Factor2557 * embedPair2542
      neighborRightP029Center2557‖
      ≤
      ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, neighborRightP029Factor2557, neighborRightP029Center2557,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ neighborRightPosition2557)
    (embedPair2542 neighborRightP029Factor2557 * embedPair2542 neighborRightP029Center2557) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add neighborRightP029DerivativeError2557 hc)).trans
  norm_num [pairMagnitude2542, neighborRightP029Factor2557, neighborRightP029Error2557,
      batchC02702PlusLeftP029NormUpper2558]

noncomputable def batchC02702PlusLeftNormUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02702PlusLeftP000NormUpper2558
  | 1 => batchC02702PlusLeftP001NormUpper2558
  | 2 => batchC02702PlusLeftP002NormUpper2558
  | 3 => batchC02702PlusLeftP003NormUpper2558
  | 4 => batchC02702PlusLeftP004NormUpper2558
  | 5 => batchC02702PlusLeftP005NormUpper2558
  | 6 => batchC02702PlusLeftP006NormUpper2558
  | 7 => batchC02702PlusLeftP007NormUpper2558
  | 8 => batchC02702PlusLeftP008NormUpper2558
  | 9 => batchC02702PlusLeftP009NormUpper2558
  | 10 => batchC02702PlusLeftP010NormUpper2558
  | 11 => batchC02702PlusLeftP011NormUpper2558
  | 12 => batchC02702PlusLeftP012NormUpper2558
  | 13 => batchC02702PlusLeftP013NormUpper2558
  | 14 => batchC02702PlusLeftP014NormUpper2558
  | 15 => batchC02702PlusLeftP015NormUpper2558
  | 16 => batchC02702PlusLeftP016NormUpper2558
  | 17 => batchC02702PlusLeftP017NormUpper2558
  | 18 => batchC02702PlusLeftP018NormUpper2558
  | 19 => batchC02702PlusLeftP019NormUpper2558
  | 20 => batchC02702PlusLeftP020NormUpper2558
  | 21 => batchC02702PlusLeftP021NormUpper2558
  | 22 => batchC02702PlusLeftP022NormUpper2558
  | 23 => batchC02702PlusLeftP023NormUpper2558
  | 24 => batchC02702PlusLeftP024NormUpper2558
  | 25 => batchC02702PlusLeftP025NormUpper2558
  | 26 => batchC02702PlusLeftP026NormUpper2558
  | 27 => batchC02702PlusLeftP027NormUpper2558
  | 28 => batchC02702PlusLeftP028NormUpper2558
  | 29 => batchC02702PlusLeftP029NormUpper2558
  | _ => 0

theorem batchC02702PlusLeftNormBound2558 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 i neighborRightPosition2557‖ ≤
        batchC02702PlusLeftNormUpper2558 i := by
  fin_cases i
  · exact batchC02702PlusLeftP000NormBound2558
  · exact batchC02702PlusLeftP001NormBound2558
  · exact batchC02702PlusLeftP002NormBound2558
  · exact batchC02702PlusLeftP003NormBound2558
  · exact batchC02702PlusLeftP004NormBound2558
  · exact batchC02702PlusLeftP005NormBound2558
  · exact batchC02702PlusLeftP006NormBound2558
  · exact batchC02702PlusLeftP007NormBound2558
  · exact batchC02702PlusLeftP008NormBound2558
  · exact batchC02702PlusLeftP009NormBound2558
  · exact batchC02702PlusLeftP010NormBound2558
  · exact batchC02702PlusLeftP011NormBound2558
  · exact batchC02702PlusLeftP012NormBound2558
  · exact batchC02702PlusLeftP013NormBound2558
  · exact batchC02702PlusLeftP014NormBound2558
  · exact batchC02702PlusLeftP015NormBound2558
  · exact batchC02702PlusLeftP016NormBound2558
  · exact batchC02702PlusLeftP017NormBound2558
  · exact batchC02702PlusLeftP018NormBound2558
  · exact batchC02702PlusLeftP019NormBound2558
  · exact batchC02702PlusLeftP020NormBound2558
  · exact batchC02702PlusLeftP021NormBound2558
  · exact batchC02702PlusLeftP022NormBound2558
  · exact batchC02702PlusLeftP023NormBound2558
  · exact batchC02702PlusLeftP024NormBound2558
  · exact batchC02702PlusLeftP025NormBound2558
  · exact batchC02702PlusLeftP026NormBound2558
  · exact batchC02702PlusLeftP027NormBound2558
  · exact batchC02702PlusLeftP028NormBound2558
  · exact batchC02702PlusLeftP029NormBound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP000NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP001NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP002NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP003NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP004NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP005NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP006NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP007NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP008NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP009NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP010NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP011NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP012NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP013NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP014NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP015NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP016NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP017NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP018NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP019NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP020NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP021NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP022NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP023NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP024NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP025NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP026NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP027NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP028NormBound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusLeftP029NormBound2558
