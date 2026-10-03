import ConnesWeilRH.Dev.C1RouteABatchN05119Plus2559
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC05119PlusLeftP000NormUpper2559 : ℝ :=
    ((8415199449009615135624416878331432856269
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP000NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP000NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP000Factor2559 * embedPair2542
      batchN05119PlusP000Center2559‖
      ≤
      ((8415199449009614386927829563907908400871 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP000Factor2559, batchN05119PlusP000Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP000Factor2559 * embedPair2542 batchN05119PlusP000Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP000DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP000Factor2559, batchN05119PlusP000Error2559,
      batchC05119PlusLeftP000NormUpper2559]

noncomputable def batchC05119PlusLeftP001NormUpper2559 : ℝ :=
    ((8352099862904147175188088460462568678105
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP001NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP001NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP001Factor2559 * embedPair2542
      batchN05119PlusP001Center2559‖
      ≤
      ((2088024965726036608058562740139190468851 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP001Factor2559, batchN05119PlusP001Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP001Factor2559 * embedPair2542 batchN05119PlusP001Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP001DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP001Factor2559, batchN05119PlusP001Error2559,
      batchC05119PlusLeftP001NormUpper2559]

noncomputable def batchC05119PlusLeftP002NormUpper2559 : ℝ :=
    ((8319444582058414444507478179225881390509
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP002NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP002NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP002Factor2559 * embedPair2542
      batchN05119PlusP002Center2559‖
      ≤
      ((2079861145514603426131287409430859967001 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP002Factor2559, batchN05119PlusP002Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP002Factor2559 * embedPair2542 batchN05119PlusP002Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP002DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP002Factor2559, batchN05119PlusP002Error2559,
      batchC05119PlusLeftP002NormUpper2559]

noncomputable def batchC05119PlusLeftP003NormUpper2559 : ℝ :=
    ((4150593596979222800546869802739656867031
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05119PlusLeftP003NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP003NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP003Factor2559 * embedPair2542
      batchN05119PlusP003Center2559‖
      ≤
      ((4150593596979222431386311736544432720461 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP003Factor2559, batchN05119PlusP003Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP003Factor2559 * embedPair2542 batchN05119PlusP003Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP003DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP003Factor2559, batchN05119PlusP003Error2559,
      batchC05119PlusLeftP003NormUpper2559]

noncomputable def batchC05119PlusLeftP004NormUpper2559 : ℝ :=
    ((4145169056569998497004316472341607032435
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05119PlusLeftP004NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP004NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP004Factor2559 * embedPair2542
      batchN05119PlusP004Center2559‖
      ≤
      ((8290338113139996256674610217397437202181 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP004Factor2559, batchN05119PlusP004Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP004Factor2559 * embedPair2542 batchN05119PlusP004Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP004DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP004Factor2559, batchN05119PlusP004Error2559,
      batchC05119PlusLeftP004NormUpper2559]

noncomputable def batchC05119PlusLeftP005NormUpper2559 : ℝ :=
    ((24278909937708257957981000458573141 : ℝ)
    /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984))

theorem batchC05119PlusLeftP005NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP005NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP005Factor2559 * embedPair2542
      batchN05119PlusP005Center2559‖
      ≤
      ((1553850236013328382335561440312275301 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP005Factor2559, batchN05119PlusP005Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP005Factor2559 * embedPair2542 batchN05119PlusP005Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP005DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP005Factor2559, batchN05119PlusP005Error2559,
      batchC05119PlusLeftP005NormUpper2559]

noncomputable def batchC05119PlusLeftP006NormUpper2559 : ℝ :=
    ((379049245970890432278100361829819135 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05119PlusLeftP006NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP006NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP006Factor2559 * embedPair2542
      batchN05119PlusP006Center2559‖
      ≤
      ((758098491941780802607041655578390427 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP006Factor2559, batchN05119PlusP006Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP006Factor2559 * embedPair2542 batchN05119PlusP006Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP006DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP006Factor2559, batchN05119PlusP006Error2559,
      batchC05119PlusLeftP006NormUpper2559]

noncomputable def batchC05119PlusLeftP007NormUpper2559 : ℝ :=
    ((204670322744498203856470272114247285 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05119PlusLeftP007NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP007NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP007Factor2559 * embedPair2542
      batchN05119PlusP007Center2559‖
      ≤
      ((102335161372249093565763788312166547 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP007Factor2559, batchN05119PlusP007Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP007Factor2559 * embedPair2542 batchN05119PlusP007Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP007DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP007Factor2559, batchN05119PlusP007Error2559,
      batchC05119PlusLeftP007NormUpper2559]

noncomputable def batchC05119PlusLeftP008NormUpper2559 : ℝ :=
    ((6607660417192639547140107492978653575 :
    ℝ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984))

theorem batchC05119PlusLeftP008NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP008NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP008Factor2559 * embedPair2542
      batchN05119PlusP008Center2559‖
      ≤
      ((422890266700328892466958957096554361289 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP008Factor2559, batchN05119PlusP008Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP008Factor2559 * embedPair2542 batchN05119PlusP008Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP008DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP008Factor2559, batchN05119PlusP008Error2559,
      batchC05119PlusLeftP008NormUpper2559]

noncomputable def batchC05119PlusLeftP009NormUpper2559 : ℝ :=
    ((1324690476947203029934975794403092808405
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP009NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP009NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP009Factor2559 * embedPair2542
      batchN05119PlusP009Center2559‖
      ≤
      ((1324690476947202911303265912340674498827 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP009Factor2559, batchN05119PlusP009Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP009Factor2559 * embedPair2542 batchN05119PlusP009Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP009DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP009Factor2559, batchN05119PlusP009Error2559,
      batchC05119PlusLeftP009NormUpper2559]

noncomputable def batchC05119PlusLeftP010NormUpper2559 : ℝ :=
    ((2203720177529501399666174755749536826545
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP010NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP010NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP010Factor2559 * embedPair2542
      batchN05119PlusP010Center2559‖
      ≤
      ((137732511095593825201276520260461332437 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP010Factor2559, batchN05119PlusP010Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP010Factor2559 * embedPair2542 batchN05119PlusP010Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP010DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP010Factor2559, batchN05119PlusP010Error2559,
      batchC05119PlusLeftP010NormUpper2559]

noncomputable def batchC05119PlusLeftP011NormUpper2559 : ℝ :=
    ((2967899124538507441389263010597454705345
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP011NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP011NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP011Factor2559 * embedPair2542
      batchN05119PlusP011Center2559‖
      ≤
      ((2967899124538507177279430455286763454191 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP011Factor2559, batchN05119PlusP011Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP011Factor2559 * embedPair2542 batchN05119PlusP011Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP011DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP011Factor2559, batchN05119PlusP011Error2559,
      batchC05119PlusLeftP011NormUpper2559]

noncomputable def batchC05119PlusLeftP012NormUpper2559 : ℝ :=
    ((3928791169253083821048151580984473162411
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP012NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP012NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP012Factor2559 * embedPair2542
      batchN05119PlusP012Center2559‖
      ≤
      ((1964395584626541735884360430586492660225 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP012Factor2559, batchN05119PlusP012Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP012Factor2559 * embedPair2542 batchN05119PlusP012Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP012DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP012Factor2559, batchN05119PlusP012Error2559,
      batchC05119PlusLeftP012NormUpper2559]

noncomputable def batchC05119PlusLeftP013NormUpper2559 : ℝ :=
    ((2484428628609969283873242152977906793585
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05119PlusLeftP013NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP013NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP013Factor2559 * embedPair2542
      batchN05119PlusP013Center2559‖
      ≤
      ((2484428628609969063071118038927250838925 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP013Factor2559, batchN05119PlusP013Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP013Factor2559 * embedPair2542 batchN05119PlusP013Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP013DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP013Factor2559, batchN05119PlusP013Error2559,
      batchC05119PlusLeftP013NormUpper2559]

noncomputable def batchC05119PlusLeftP014NormUpper2559 : ℝ :=
    ((919441578591888496447484856149645189743 :
    ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem batchC05119PlusLeftP014NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP014NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP014Factor2559 * embedPair2542
      batchN05119PlusP014Center2559‖
      ≤
      ((7355532628735107317537600159256020496627 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP014Factor2559, batchN05119PlusP014Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP014Factor2559 * embedPair2542 batchN05119PlusP014Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP014DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP014Factor2559, batchN05119PlusP014Error2559,
      batchC05119PlusLeftP014NormUpper2559]

noncomputable def batchC05119PlusLeftP015NormUpper2559 : ℝ :=
    ((9470824501440549191036602566348019774129
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP015NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP015NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP015Factor2559 * embedPair2542
      batchN05119PlusP015Center2559‖
      ≤
      ((9470824501440548348055349701940171114595 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP015Factor2559, batchN05119PlusP015Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP015Factor2559 * embedPair2542 batchN05119PlusP015Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP015DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP015Factor2559, batchN05119PlusP015Error2559,
      batchC05119PlusLeftP015NormUpper2559]

noncomputable def batchC05119PlusLeftP016NormUpper2559 : ℝ := (((1 * 10^40
        + 1229720937515117525087035163133368664799) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP016NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP016NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP016Factor2559 * embedPair2542
      batchN05119PlusP016Center2559‖
      ≤
      (((1 * 10^40
        + 1229720937515116524557489102138520976915) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP016Factor2559, batchN05119PlusP016Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP016Factor2559 * embedPair2542 batchN05119PlusP016Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP016DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP016Factor2559, batchN05119PlusP016Error2559,
      batchC05119PlusLeftP016NormUpper2559]

noncomputable def batchC05119PlusLeftP017NormUpper2559 : ℝ := (((1 * 10^40
        + 5245476170536488303701533244825584075833) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP017NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP017NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP017Factor2559 * embedPair2542
      batchN05119PlusP017Center2559‖
      ≤
      (((1 * 10^40
        + 5245476170536486942085535516000689512355) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP017Factor2559, batchN05119PlusP017Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP017Factor2559 * embedPair2542 batchN05119PlusP017Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP017DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP017Factor2559, batchN05119PlusP017Error2559,
      batchC05119PlusLeftP017NormUpper2559]

noncomputable def batchC05119PlusLeftP018NormUpper2559 : ℝ :=
    ((8491822875608876640885905456082816587743
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05119PlusLeftP018NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP018NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP018Factor2559 * embedPair2542
      batchN05119PlusP018Center2559‖
      ≤
      ((4245911437804437940827490384012579678511 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP018Factor2559, batchN05119PlusP018Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP018Factor2559 * embedPair2542 batchN05119PlusP018Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP018DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP018Factor2559, batchN05119PlusP018Error2559,
      batchC05119PlusLeftP018NormUpper2559]

noncomputable def batchC05119PlusLeftP019NormUpper2559 : ℝ :=
    ((5112997709879800228319190458722889715335
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05119PlusLeftP019NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP019NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP019Factor2559 * embedPair2542
      batchN05119PlusP019Center2559‖
      ≤
      (((2 * 10^40
        + 451990839519199080926057401575895169807) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP019Factor2559, batchN05119PlusP019Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP019Factor2559 * embedPair2542 batchN05119PlusP019Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP019DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP019Factor2559, batchN05119PlusP019Error2559,
      batchC05119PlusLeftP019NormUpper2559]

noncomputable def batchC05119PlusLeftP020NormUpper2559 : ℝ :=
    ((6182036969375873916833081464837057800419
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05119PlusLeftP020NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP020NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP020Factor2559 * embedPair2542
      batchN05119PlusP020Center2559‖
      ≤
      (((1 * 10^40
        + 2364073938751746723213077443922536460617) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP020Factor2559, batchN05119PlusP020Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP020Factor2559 * embedPair2542 batchN05119PlusP020Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP020DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP020Factor2559, batchN05119PlusP020Error2559,
      batchC05119PlusLeftP020NormUpper2559]

noncomputable def batchC05119PlusLeftP021NormUpper2559 : ℝ := (((1 * 10^40
        + 4361712182012956769603578817877839999593) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05119PlusLeftP021NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP021NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP021Factor2559 * embedPair2542
      batchN05119PlusP021Center2559‖
      ≤
      ((7180856091006477738460216015212052966389 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP021Factor2559, batchN05119PlusP021Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP021Factor2559 * embedPair2542 batchN05119PlusP021Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP021DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP021Factor2559, batchN05119PlusP021Error2559,
      batchC05119PlusLeftP021NormUpper2559]

noncomputable def batchC05119PlusLeftP022NormUpper2559 : ℝ := (((3 * 10^40
        + 925538051145556466840662581235891410325) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP022NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP022NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP022Factor2559 * embedPair2542
      batchN05119PlusP022Center2559‖
      ≤
      (((1 * 10^40
        + 5462769025572776840020789669783253283323) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP022Factor2559, batchN05119PlusP022Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP022Factor2559 * embedPair2542 batchN05119PlusP022Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP022DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP022Factor2559, batchN05119PlusP022Error2559,
      batchC05119PlusLeftP022NormUpper2559]

noncomputable def batchC05119PlusLeftP023NormUpper2559 : ℝ := (((3 * 10^40
        + 7899667195881750577762439098684089716759) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP023NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP023NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP023Factor2559 * embedPair2542
      batchN05119PlusP023Center2559‖
      ≤
      (((1 * 10^40
        + 8949833597940873575316777162374196557903) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP023Factor2559, batchN05119PlusP023Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP023Factor2559 * embedPair2542 batchN05119PlusP023Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP023DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP023Factor2559, batchN05119PlusP023Error2559,
      batchC05119PlusLeftP023NormUpper2559]

noncomputable def batchC05119PlusLeftP024NormUpper2559 : ℝ := (((4 * 10^40
        + 1428961461700566119305384593983442781549) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP024NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP024NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP024Factor2559 * embedPair2542
      batchN05119PlusP024Center2559‖
      ≤
      (((2 * 10^40
        + 714480730850281183419746953826526190465) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP024Factor2559, batchN05119PlusP024Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP024Factor2559 * embedPair2542 batchN05119PlusP024Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP024DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP024Factor2559, batchN05119PlusP024Error2559,
      batchC05119PlusLeftP024NormUpper2559]

noncomputable def batchC05119PlusLeftP025NormUpper2559 : ℝ :=
    ((2884724648952345234255683234769589651711
    : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

theorem batchC05119PlusLeftP025NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP025NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP025Factor2559 * embedPair2542
      batchN05119PlusP025Center2559‖
      ≤
      (((2 * 10^40
        + 3077797191618759779323650985512252476045) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP025Factor2559, batchN05119PlusP025Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP025Factor2559 * embedPair2542 batchN05119PlusP025Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP025DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP025Factor2559, batchN05119PlusP025Error2559,
      batchC05119PlusLeftP025NormUpper2559]

noncomputable def batchC05119PlusLeftP026NormUpper2559 : ℝ := (((2 * 10^40
        + 5672303733606007024864675880301530297053) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05119PlusLeftP026NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP026NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP026Factor2559 * embedPair2542
      batchN05119PlusP026Center2559‖
      ≤
      (((1 * 10^40
        + 2836151866803002344745525200835115802055) : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP026Factor2559, batchN05119PlusP026Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP026Factor2559 * embedPair2542 batchN05119PlusP026Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP026DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP026Factor2559, batchN05119PlusP026Error2559,
      batchC05119PlusLeftP026NormUpper2559]

noncomputable def batchC05119PlusLeftP027NormUpper2559 : ℝ := (((5 * 10^40
        + 9497868950841625310226824882938109679401) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP027NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP027NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP027Factor2559 * embedPair2542
      batchN05119PlusP027Center2559‖
      ≤
      (((5 * 10^40
        + 9497868950841619880114679975147358400509) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP027Factor2559, batchN05119PlusP027Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP027Factor2559 * embedPair2542 batchN05119PlusP027Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP027DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP027Factor2559, batchN05119PlusP027Error2559,
      batchC05119PlusLeftP027NormUpper2559]

noncomputable def batchC05119PlusLeftP028NormUpper2559 : ℝ := (((6 * 10^40
        + 2950648591581278789906225971493712753841) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP028NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP028NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP028Factor2559 * embedPair2542
      batchN05119PlusP028Center2559‖
      ≤
      (((1 * 10^40
        + 5737662147895318259283344451279085770921) : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP028Factor2559, batchN05119PlusP028Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP028Factor2559 * embedPair2542 batchN05119PlusP028Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP028DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP028Factor2559, batchN05119PlusP028Error2559,
      batchC05119PlusLeftP028NormUpper2559]

noncomputable def batchC05119PlusLeftP029NormUpper2559 : ℝ := (((6 * 10^40
        + 8460037048423505198021927515887215753131) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119PlusLeftP029NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05119PlusPosition2559‖ ≤
      batchC05119PlusLeftP029NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119PlusP029Factor2559 * embedPair2542
      batchN05119PlusP029Center2559‖
      ≤
      (((6 * 10^40
        + 8460037048423498929138154818732832561663) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119PlusP029Factor2559, batchN05119PlusP029Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05119PlusPosition2559)
    (embedPair2542 batchN05119PlusP029Factor2559 * embedPair2542 batchN05119PlusP029Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119PlusP029DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119PlusP029Factor2559, batchN05119PlusP029Error2559,
      batchC05119PlusLeftP029NormUpper2559]

noncomputable def batchC05119PlusLeftNormUpper2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05119PlusLeftP000NormUpper2559
  | 1 => batchC05119PlusLeftP001NormUpper2559
  | 2 => batchC05119PlusLeftP002NormUpper2559
  | 3 => batchC05119PlusLeftP003NormUpper2559
  | 4 => batchC05119PlusLeftP004NormUpper2559
  | 5 => batchC05119PlusLeftP005NormUpper2559
  | 6 => batchC05119PlusLeftP006NormUpper2559
  | 7 => batchC05119PlusLeftP007NormUpper2559
  | 8 => batchC05119PlusLeftP008NormUpper2559
  | 9 => batchC05119PlusLeftP009NormUpper2559
  | 10 => batchC05119PlusLeftP010NormUpper2559
  | 11 => batchC05119PlusLeftP011NormUpper2559
  | 12 => batchC05119PlusLeftP012NormUpper2559
  | 13 => batchC05119PlusLeftP013NormUpper2559
  | 14 => batchC05119PlusLeftP014NormUpper2559
  | 15 => batchC05119PlusLeftP015NormUpper2559
  | 16 => batchC05119PlusLeftP016NormUpper2559
  | 17 => batchC05119PlusLeftP017NormUpper2559
  | 18 => batchC05119PlusLeftP018NormUpper2559
  | 19 => batchC05119PlusLeftP019NormUpper2559
  | 20 => batchC05119PlusLeftP020NormUpper2559
  | 21 => batchC05119PlusLeftP021NormUpper2559
  | 22 => batchC05119PlusLeftP022NormUpper2559
  | 23 => batchC05119PlusLeftP023NormUpper2559
  | 24 => batchC05119PlusLeftP024NormUpper2559
  | 25 => batchC05119PlusLeftP025NormUpper2559
  | 26 => batchC05119PlusLeftP026NormUpper2559
  | 27 => batchC05119PlusLeftP027NormUpper2559
  | 28 => batchC05119PlusLeftP028NormUpper2559
  | 29 => batchC05119PlusLeftP029NormUpper2559
  | _ => 0

theorem batchC05119PlusLeftNormBound2559 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 i batchN05119PlusPosition2559‖ ≤
        batchC05119PlusLeftNormUpper2559 i := by
  fin_cases i
  · exact batchC05119PlusLeftP000NormBound2559
  · exact batchC05119PlusLeftP001NormBound2559
  · exact batchC05119PlusLeftP002NormBound2559
  · exact batchC05119PlusLeftP003NormBound2559
  · exact batchC05119PlusLeftP004NormBound2559
  · exact batchC05119PlusLeftP005NormBound2559
  · exact batchC05119PlusLeftP006NormBound2559
  · exact batchC05119PlusLeftP007NormBound2559
  · exact batchC05119PlusLeftP008NormBound2559
  · exact batchC05119PlusLeftP009NormBound2559
  · exact batchC05119PlusLeftP010NormBound2559
  · exact batchC05119PlusLeftP011NormBound2559
  · exact batchC05119PlusLeftP012NormBound2559
  · exact batchC05119PlusLeftP013NormBound2559
  · exact batchC05119PlusLeftP014NormBound2559
  · exact batchC05119PlusLeftP015NormBound2559
  · exact batchC05119PlusLeftP016NormBound2559
  · exact batchC05119PlusLeftP017NormBound2559
  · exact batchC05119PlusLeftP018NormBound2559
  · exact batchC05119PlusLeftP019NormBound2559
  · exact batchC05119PlusLeftP020NormBound2559
  · exact batchC05119PlusLeftP021NormBound2559
  · exact batchC05119PlusLeftP022NormBound2559
  · exact batchC05119PlusLeftP023NormBound2559
  · exact batchC05119PlusLeftP024NormBound2559
  · exact batchC05119PlusLeftP025NormBound2559
  · exact batchC05119PlusLeftP026NormBound2559
  · exact batchC05119PlusLeftP027NormBound2559
  · exact batchC05119PlusLeftP028NormBound2559
  · exact batchC05119PlusLeftP029NormBound2559

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP000NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP001NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP002NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP003NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP004NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP005NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP006NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP007NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP008NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP009NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP010NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP011NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP012NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP013NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP014NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP015NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP016NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP017NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP018NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP019NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP020NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP021NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP022NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP023NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP024NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP025NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP026NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP027NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP028NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusLeftP029NormBound2559
