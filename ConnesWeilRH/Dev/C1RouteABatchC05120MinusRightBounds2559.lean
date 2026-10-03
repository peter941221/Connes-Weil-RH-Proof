import ConnesWeilRH.Dev.C1RouteABatchN05121Minus2559
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC05120MinusRightP000NormUpper2559 : ℝ :=
    ((8415199449009615135624416878331432859361
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusRightP000NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05121MinusPosition2559‖ ≤
      batchC05120MinusRightP000NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP000Factor2559 * embedPair2542
      batchN05121MinusP000Center2559‖ ≤
      ((8415199449009614386927829563907908403963 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP000Factor2559, batchN05121MinusP000Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP000Factor2559 * embedPair2542 batchN05121MinusP000Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP000DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP000Factor2559, batchN05121MinusP000Error2559,
      batchC05120MinusRightP000NormUpper2559]

noncomputable def batchC05120MinusRightP001NormUpper2559 : ℝ :=
    ((4176049931452073587594044230231284340587
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusRightP001NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05121MinusPosition2559‖ ≤
      batchC05120MinusRightP001NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP001Factor2559 * embedPair2542
      batchN05121MinusP001Center2559‖ ≤
      ((8352099862904146432234250960556761878473 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP001Factor2559, batchN05121MinusP001Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP001Factor2559 * embedPair2542 batchN05121MinusP001Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP001DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP001Factor2559, batchN05121MinusP001Error2559,
      batchC05120MinusRightP001NormUpper2559]

noncomputable def batchC05120MinusRightP002NormUpper2559 : ℝ :=
    ((2079861145514603611126869544806470346863
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05120MinusRightP002NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05121MinusPosition2559‖ ≤
      batchC05120MinusRightP002NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP002Factor2559 * embedPair2542
      batchN05121MinusP002Center2559‖ ≤
      ((8319444582058413704525149637723439864947 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP002Factor2559, batchN05121MinusP002Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP002Factor2559 * embedPair2542 batchN05121MinusP002Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP002DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP002Factor2559, batchN05121MinusP002Error2559,
      batchC05120MinusRightP002NormUpper2559]

noncomputable def batchC05120MinusRightP003NormUpper2559 : ℝ :=
    ((2075296798489611400273434901369828432753
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05120MinusRightP003NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05121MinusPosition2559‖ ≤
      batchC05120MinusRightP003NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP003Factor2559 * embedPair2542
      batchN05121MinusP003Center2559‖ ≤
      ((518824199622402803923288967068054089867 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP003Factor2559, batchN05121MinusP003Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP003Factor2559 * embedPair2542 batchN05121MinusP003Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP003DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP003Factor2559, batchN05121MinusP003Error2559,
      batchC05120MinusRightP003NormUpper2559]

noncomputable def batchC05120MinusRightP004NormUpper2559 : ℝ :=
    ((8290338113139996994008632944683214067917
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusRightP004NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05121MinusPosition2559‖ ≤
      batchC05120MinusRightP004NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP004Factor2559 * embedPair2542
      batchN05121MinusP004Center2559‖ ≤
      ((2072584528284999064168652554349359301307 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP004Factor2559, batchN05121MinusP004Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP004Factor2559 * embedPair2542 batchN05121MinusP004Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP004DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP004Factor2559, batchN05121MinusP004Error2559,
      batchC05120MinusRightP004NormUpper2559]

noncomputable def batchC05120MinusRightP005NormUpper2559 : ℝ :=
    ((24278909937708257957981000458573141 : ℝ)
    /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984))

theorem batchC05120MinusRightP005NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05121MinusPosition2559‖ ≤
      batchC05120MinusRightP005NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP005Factor2559 * embedPair2542
      batchN05121MinusP005Center2559‖ ≤
      ((1553850236013328382335561440312275301 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP005Factor2559, batchN05121MinusP005Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP005Factor2559 * embedPair2542 batchN05121MinusP005Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP005DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP005Factor2559, batchN05121MinusP005Error2559,
      batchC05120MinusRightP005NormUpper2559]

noncomputable def batchC05120MinusRightP006NormUpper2559 : ℝ :=
    ((379049245970890432278100361829819135 :
    ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusRightP006NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05121MinusPosition2559‖ ≤
      batchC05120MinusRightP006NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP006Factor2559 * embedPair2542
      batchN05121MinusP006Center2559‖ ≤
      ((758098491941780802607041655578390427 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP006Factor2559, batchN05121MinusP006Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP006Factor2559 * embedPair2542 batchN05121MinusP006Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP006DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP006Factor2559, batchN05121MinusP006Error2559,
      batchC05120MinusRightP006NormUpper2559]

noncomputable def batchC05120MinusRightP007NormUpper2559 : ℝ :=
    ((204670322744498203856470272114247285 :
    ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusRightP007NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05121MinusPosition2559‖ ≤
      batchC05120MinusRightP007NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP007Factor2559 * embedPair2542
      batchN05121MinusP007Center2559‖ ≤
      ((102335161372249093565763788312166547 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP007Factor2559, batchN05121MinusP007Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP007Factor2559 * embedPair2542 batchN05121MinusP007Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP007DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP007Factor2559, batchN05121MinusP007Error2559,
      batchC05120MinusRightP007NormUpper2559]

noncomputable def batchC05120MinusRightP008NormUpper2559 : ℝ :=
    ((422890266700328931016966879550633828855
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusRightP008NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05121MinusPosition2559‖ ≤
      batchC05120MinusRightP008NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP008Factor2559 * embedPair2542
      batchN05121MinusP008Center2559‖ ≤
      ((825957552149079868099529213079207737 : ℝ) /
        (285449 * 10^40
        + 5385411919762116571938898990272765493248)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP008Factor2559, batchN05121MinusP008Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP008Factor2559 * embedPair2542 batchN05121MinusP008Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP008DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP008Factor2559, batchN05121MinusP008Error2559,
      batchC05120MinusRightP008NormUpper2559]

noncomputable def batchC05120MinusRightP009NormUpper2559 : ℝ :=
    ((1324690476947203029934975794403092808665
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusRightP009NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05121MinusPosition2559‖ ≤
      batchC05120MinusRightP009NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP009Factor2559 * embedPair2542
      batchN05121MinusP009Center2559‖ ≤
      ((1324690476947202911303265912340674499087 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP009Factor2559, batchN05121MinusP009Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP009Factor2559 * embedPair2542 batchN05121MinusP009Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP009DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP009Factor2559, batchN05121MinusP009Error2559,
      batchC05120MinusRightP009NormUpper2559]

noncomputable def batchC05120MinusRightP010NormUpper2559 : ℝ :=
    ((2203720177529501399666174755749536827061
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusRightP010NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP010NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP010Factor2559 * embedPair2542
      batchN05121MinusP010Center2559‖ ≤
      ((550930044382375300805106081041845329877 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP010Factor2559, batchN05121MinusP010Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP010Factor2559 * embedPair2542 batchN05121MinusP010Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP010DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP010Factor2559, batchN05121MinusP010Error2559,
      batchC05120MinusRightP010NormUpper2559]

noncomputable def batchC05120MinusRightP011NormUpper2559 : ℝ :=
    ((1483949562269253720694631505298727353057
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusRightP011NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP011NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP011Factor2559 * embedPair2542
      batchN05121MinusP011Center2559‖ ≤
      ((185493695283656698579964403455422715935 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP011Factor2559, batchN05121MinusP011Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP011Factor2559 * embedPair2542 batchN05121MinusP011Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP011DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP011Factor2559, batchN05121MinusP011Error2559,
      batchC05120MinusRightP011NormUpper2559]

noncomputable def batchC05120MinusRightP012NormUpper2559 : ℝ :=
    ((1964395584626541910524075790492236581765
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusRightP012NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP012NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP012Factor2559 * embedPair2542
      batchN05121MinusP012Center2559‖ ≤
      ((3928791169253083471768720861172985321569 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP012Factor2559, batchN05121MinusP012Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP012Factor2559 * embedPair2542 batchN05121MinusP012Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP012DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP012Factor2559, batchN05121MinusP012Error2559,
      batchC05120MinusRightP012NormUpper2559]

noncomputable def batchC05120MinusRightP013NormUpper2559 : ℝ :=
    ((2484428628609969283873242152977906794351
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusRightP013NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP013NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP013Factor2559 * embedPair2542
      batchN05121MinusP013Center2559‖ ≤
      ((2484428628609969063071118038927250839691 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP013Factor2559, batchN05121MinusP013Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP013Factor2559 * embedPair2542 batchN05121MinusP013Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP013DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP013Factor2559, batchN05121MinusP013Error2559,
      batchC05120MinusRightP013NormUpper2559]

noncomputable def batchC05120MinusRightP014NormUpper2559 : ℝ :=
    ((1838883157183776992894969712299290380133
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05120MinusRightP014NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP014NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP014Factor2559 * embedPair2542
      batchN05121MinusP014Center2559‖ ≤
      ((7355532628735107317537600159256020499215 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP014Factor2559, batchN05121MinusP014Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP014Factor2559 * embedPair2542 batchN05121MinusP014Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP014DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP014Factor2559, batchN05121MinusP014Error2559,
      batchC05120MinusRightP014NormUpper2559]

noncomputable def batchC05120MinusRightP015NormUpper2559 : ℝ :=
    ((2367706125360137297759150641587004944439
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05120MinusRightP015NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP015NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP015Factor2559 * embedPair2542
      batchN05121MinusP015Center2559‖ ≤
      ((4735412250720274174027674850970085559111 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP015Factor2559, batchN05121MinusP015Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP015Factor2559 * embedPair2542 batchN05121MinusP015Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP015DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP015Factor2559, batchN05121MinusP015Error2559,
      batchC05120MinusRightP015NormUpper2559]

noncomputable def batchC05120MinusRightP016NormUpper2559 : ℝ :=
    ((5614860468757558762543517581566684334677
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusRightP016NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP016NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP016Factor2559 * embedPair2542
      batchN05121MinusP016Center2559‖ ≤
      ((5614860468757558262278744551069260490735 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP016Factor2559, batchN05121MinusP016Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP016Factor2559 * embedPair2542 batchN05121MinusP016Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP016DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP016Factor2559, batchN05121MinusP016Error2559,
      batchC05120MinusRightP016NormUpper2559]

noncomputable def batchC05120MinusRightP017NormUpper2559 : ℝ := (((1 * 10^40
        + 5245476170536488303701533244825584082683) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusRightP017NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP017NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP017Factor2559 * embedPair2542
      batchN05121MinusP017Center2559‖ ≤
      (((1 * 10^40
        + 5245476170536486942085535516000689519205) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP017Factor2559, batchN05121MinusP017Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP017Factor2559 * embedPair2542 batchN05121MinusP017Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP017DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP017Factor2559, batchN05121MinusP017Error2559,
      batchC05120MinusRightP017NormUpper2559]

noncomputable def batchC05120MinusRightP018NormUpper2559 : ℝ := (((1 * 10^40
        + 6983645751217753281771810912165633183397) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusRightP018NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP018NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP018Factor2559 * embedPair2542
      batchN05121MinusP018Center2559‖ ≤
      (((1 * 10^40
        + 6983645751217751763309961536050318721955) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP018Factor2559, batchN05121MinusP018Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP018Factor2559 * embedPair2542 batchN05121MinusP018Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP018DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP018Factor2559, batchN05121MinusP018Error2559,
      batchC05120MinusRightP018NormUpper2559]

noncomputable def batchC05120MinusRightP019NormUpper2559 : ℝ := (((1 * 10^40
        + 225995419759600456638380917445779435739) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusRightP019NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP019NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP019Factor2559 * embedPair2542
      batchN05121MinusP019Center2559‖ ≤
      (((2 * 10^40
        + 451990839519199080926057401575895179945) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP019Factor2559, batchN05121MinusP019Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP019Factor2559 * embedPair2542 batchN05121MinusP019Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP019DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP019Factor2559, batchN05121MinusP019Error2559,
      batchC05120MinusRightP019NormUpper2559]

noncomputable def batchC05120MinusRightP020NormUpper2559 : ℝ := (((2 * 10^40
        + 4728147877503495667332325859348231214737) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusRightP020NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP020NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP020Factor2559 * embedPair2542
      batchN05121MinusP020Center2559‖ ≤
      (((2 * 10^40
        + 4728147877503493446426154887845072934295) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP020Factor2559, batchN05121MinusP020Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP020Factor2559 * embedPair2542 batchN05121MinusP020Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP020DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP020Factor2559, batchN05121MinusP020Error2559,
      batchC05120MinusRightP020NormUpper2559]

noncomputable def batchC05120MinusRightP021NormUpper2559 : ℝ := (((2 * 10^40
        + 8723424364025913539207157635755680015135) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusRightP021NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP021NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP021Factor2559 * embedPair2542
      batchN05121MinusP021Center2559‖ ≤
      (((2 * 10^40
        + 8723424364025910953840864060848211881505) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP021Factor2559, batchN05121MinusP021Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP021Factor2559 * embedPair2542 batchN05121MinusP021Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP021DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP021Factor2559, batchN05121MinusP021Error2559,
      batchC05120MinusRightP021NormUpper2559]

noncomputable def batchC05120MinusRightP022NormUpper2559 : ℝ := (((1 * 10^40
        + 5462769025572778233420331290617945713963) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusRightP022NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP022NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP022Factor2559 * embedPair2542
      batchN05121MinusP022Center2559‖ ≤
      (((3 * 10^40
        + 925538051145553680041579339566506584247) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP022Factor2559, batchN05121MinusP022Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP022Factor2559 * embedPair2542 batchN05121MinusP022Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP022DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP022Factor2559, batchN05121MinusP022Error2559,
      batchC05120MinusRightP022NormUpper2559]

noncomputable def batchC05120MinusRightP023NormUpper2559 : ℝ :=
    ((9474916798970437644440609774671022434961
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05120MinusRightP023NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP023NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP023Factor2559 * embedPair2542
      batchN05121MinusP023Center2559‖ ≤
      (((3 * 10^40
        + 7899667195881747150633554324748393138891) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP023Factor2559, batchN05121MinusP023Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP023Factor2559 * embedPair2542 batchN05121MinusP023Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP023DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP023Factor2559, batchN05121MinusP023Error2559,
      batchC05120MinusRightP023NormUpper2559]

noncomputable def batchC05120MinusRightP024NormUpper2559 : ℝ :=
    ((5178620182712570764913173074247930350943
    : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem batchC05120MinusRightP024NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP024NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP024Factor2559 * embedPair2542
      batchN05121MinusP024Center2559‖ ≤
      (((4 * 10^40
        + 1428961461700562366839493907653052406925) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP024Factor2559, batchN05121MinusP024Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP024Factor2559 * embedPair2542 batchN05121MinusP024Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP024DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP024Factor2559, batchN05121MinusP024Error2559,
      batchC05120MinusRightP024NormUpper2559]

noncomputable def batchC05120MinusRightP025NormUpper2559 : ℝ := (((2 * 10^40
        + 3077797191618761874045465878156717228699) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusRightP025NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP025NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP025Factor2559 * embedPair2542
      batchN05121MinusP025Center2559‖ ≤
      ((1442362324476172486207728186594515780691 : ℝ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP025Factor2559, batchN05121MinusP025Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP025Factor2559 * embedPair2542 batchN05121MinusP025Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP025DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP025Factor2559, batchN05121MinusP025Error2559,
      batchC05120MinusRightP025NormUpper2559]

noncomputable def batchC05120MinusRightP026NormUpper2559 : ℝ := (((5 * 10^40
        + 1344607467212014049729351760603060628711) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusRightP026NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP026NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP026Factor2559 * embedPair2542
      batchN05121MinusP026Center2559‖ ≤
      (((5 * 10^40
        + 1344607467212009378982100803340463242825) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP026Factor2559, batchN05121MinusP026Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP026Factor2559 * embedPair2542 batchN05121MinusP026Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP026DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP026Factor2559, batchN05121MinusP026Error2559,
      batchC05120MinusRightP026NormUpper2559]

noncomputable def batchC05120MinusRightP027NormUpper2559 : ℝ := (((5 * 10^40
        + 9497868950841625310226824882938109721519) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusRightP027NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP027NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP027Factor2559 * embedPair2542
      batchN05121MinusP027Center2559‖ ≤
      (((5 * 10^40
        + 9497868950841619880114679975147358442627) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP027Factor2559, batchN05121MinusP027Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP027Factor2559 * embedPair2542 batchN05121MinusP027Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP027DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP027Factor2559, batchN05121MinusP027Error2559,
      batchC05120MinusRightP027NormUpper2559]

noncomputable def batchC05120MinusRightP028NormUpper2559 : ℝ := (((6 * 10^40
        + 2950648591581278789906225971493712799249) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusRightP028NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP028NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP028Factor2559 * embedPair2542
      batchN05121MinusP028Center2559‖ ≤
      (((1 * 10^40
        + 5737662147895318259283344451279085782273) : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP028Factor2559, batchN05121MinusP028Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP028Factor2559 * embedPair2542 batchN05121MinusP028Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP028DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP028Factor2559, batchN05121MinusP028Error2559,
      batchC05120MinusRightP028NormUpper2559]

noncomputable def batchC05120MinusRightP029NormUpper2559 : ℝ := (((6 * 10^40
        + 8460037048423505198021927515887215803911) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusRightP029NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05121MinusPosition2559‖
        ≤
      batchC05120MinusRightP029NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121MinusP029Factor2559 * embedPair2542
      batchN05121MinusP029Center2559‖ ≤
      (((6 * 10^40
        + 8460037048423498929138154818732832612443) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121MinusP029Factor2559, batchN05121MinusP029Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05121MinusPosition2559)
    (embedPair2542 batchN05121MinusP029Factor2559 * embedPair2542 batchN05121MinusP029Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121MinusP029DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121MinusP029Factor2559, batchN05121MinusP029Error2559,
      batchC05120MinusRightP029NormUpper2559]

noncomputable def batchC05120MinusRightNormUpper2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05120MinusRightP000NormUpper2559
  | 1 => batchC05120MinusRightP001NormUpper2559
  | 2 => batchC05120MinusRightP002NormUpper2559
  | 3 => batchC05120MinusRightP003NormUpper2559
  | 4 => batchC05120MinusRightP004NormUpper2559
  | 5 => batchC05120MinusRightP005NormUpper2559
  | 6 => batchC05120MinusRightP006NormUpper2559
  | 7 => batchC05120MinusRightP007NormUpper2559
  | 8 => batchC05120MinusRightP008NormUpper2559
  | 9 => batchC05120MinusRightP009NormUpper2559
  | 10 => batchC05120MinusRightP010NormUpper2559
  | 11 => batchC05120MinusRightP011NormUpper2559
  | 12 => batchC05120MinusRightP012NormUpper2559
  | 13 => batchC05120MinusRightP013NormUpper2559
  | 14 => batchC05120MinusRightP014NormUpper2559
  | 15 => batchC05120MinusRightP015NormUpper2559
  | 16 => batchC05120MinusRightP016NormUpper2559
  | 17 => batchC05120MinusRightP017NormUpper2559
  | 18 => batchC05120MinusRightP018NormUpper2559
  | 19 => batchC05120MinusRightP019NormUpper2559
  | 20 => batchC05120MinusRightP020NormUpper2559
  | 21 => batchC05120MinusRightP021NormUpper2559
  | 22 => batchC05120MinusRightP022NormUpper2559
  | 23 => batchC05120MinusRightP023NormUpper2559
  | 24 => batchC05120MinusRightP024NormUpper2559
  | 25 => batchC05120MinusRightP025NormUpper2559
  | 26 => batchC05120MinusRightP026NormUpper2559
  | 27 => batchC05120MinusRightP027NormUpper2559
  | 28 => batchC05120MinusRightP028NormUpper2559
  | 29 => batchC05120MinusRightP029NormUpper2559
  | _ => 0

theorem batchC05120MinusRightNormBound2559 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 i batchN05121MinusPosition2559‖ ≤
        batchC05120MinusRightNormUpper2559 i := by
  fin_cases i
  · exact batchC05120MinusRightP000NormBound2559
  · exact batchC05120MinusRightP001NormBound2559
  · exact batchC05120MinusRightP002NormBound2559
  · exact batchC05120MinusRightP003NormBound2559
  · exact batchC05120MinusRightP004NormBound2559
  · exact batchC05120MinusRightP005NormBound2559
  · exact batchC05120MinusRightP006NormBound2559
  · exact batchC05120MinusRightP007NormBound2559
  · exact batchC05120MinusRightP008NormBound2559
  · exact batchC05120MinusRightP009NormBound2559
  · exact batchC05120MinusRightP010NormBound2559
  · exact batchC05120MinusRightP011NormBound2559
  · exact batchC05120MinusRightP012NormBound2559
  · exact batchC05120MinusRightP013NormBound2559
  · exact batchC05120MinusRightP014NormBound2559
  · exact batchC05120MinusRightP015NormBound2559
  · exact batchC05120MinusRightP016NormBound2559
  · exact batchC05120MinusRightP017NormBound2559
  · exact batchC05120MinusRightP018NormBound2559
  · exact batchC05120MinusRightP019NormBound2559
  · exact batchC05120MinusRightP020NormBound2559
  · exact batchC05120MinusRightP021NormBound2559
  · exact batchC05120MinusRightP022NormBound2559
  · exact batchC05120MinusRightP023NormBound2559
  · exact batchC05120MinusRightP024NormBound2559
  · exact batchC05120MinusRightP025NormBound2559
  · exact batchC05120MinusRightP026NormBound2559
  · exact batchC05120MinusRightP027NormBound2559
  · exact batchC05120MinusRightP028NormBound2559
  · exact batchC05120MinusRightP029NormBound2559

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP000NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP001NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP002NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP003NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP004NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP005NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP006NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP007NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP008NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP009NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP010NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP011NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP012NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP013NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP014NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP015NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP016NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP017NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP018NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP019NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP020NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP021NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP022NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP023NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP024NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP025NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP026NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP027NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP028NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusRightP029NormBound2559
