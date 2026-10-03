import ConnesWeilRH.Dev.C1RouteABatchN05121Plus2559
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC05120PlusRightP000NormUpper2559 : ℝ :=
    ((8425792448240356856179396507625368369961
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP000NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP000NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP000Factor2559 * embedPair2542
      batchN05121PlusP000Center2559‖ ≤
      ((4212896224120178053899557389365114877615 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP000Factor2559, batchN05121PlusP000Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP000Factor2559 * embedPair2542 batchN05121PlusP000Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP000DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP000Factor2559, batchN05121PlusP000Error2559,
      batchC05120PlusRightP000NormUpper2559]

noncomputable def batchC05120PlusRightP001NormUpper2559 : ℝ :=
    ((8362690571481186356945134807095467924803
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP001NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP001NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP001Factor2559 * embedPair2542
      batchN05121PlusP001Center2559‖ ≤
      ((2090672642870296403444930987584283162133 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP001Factor2559, batchN05121PlusP001Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP001Factor2559 * embedPair2542 batchN05121PlusP001Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP001DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP001Factor2559, batchN05121PlusP001Error2559,
      batchC05120PlusRightP001NormUpper2559]

noncomputable def batchC05120PlusRightP002NormUpper2559 : ℝ :=
    ((8330034599983188082309626671460247783083
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP002NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP002NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP002Factor2559 * embedPair2542
      batchN05121PlusP002Center2559‖ ≤
      ((2082508649995796835460887784707183658303 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP002Factor2559, batchN05121PlusP002Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP002Factor2559 * embedPair2542 batchN05121PlusP002Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP002DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP002Factor2559, batchN05121PlusP002Error2559,
      batchC05120PlusRightP002NormUpper2559]

noncomputable def batchC05120PlusRightP003NormUpper2559 : ℝ :=
    ((519486060966788972446968626063048748491
    : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

theorem batchC05120PlusRightP003NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP003NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP003Factor2559 * embedPair2542
      batchN05121PlusP003Center2559‖ ≤
      ((1038972121933577852524345697790519197083 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP003Factor2559, batchN05121PlusP003Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP003Factor2559 * embedPair2542 batchN05121PlusP003Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP003DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP003Factor2559, batchN05121PlusP003Error2559,
      batchC05120PlusRightP003NormUpper2559]

noncomputable def batchC05120PlusRightP004NormUpper2559 : ℝ :=
    ((8300927805522046300097058100457580014225
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP004NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP004NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP004Factor2559 * embedPair2542
      batchN05121PlusP004Center2559‖ ≤
      ((8300927805522045562037276243265774074851 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP004Factor2559, batchN05121PlusP004Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP004Factor2559 * embedPair2542 batchN05121PlusP004Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP004DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP004Factor2559, batchN05121PlusP004Error2559,
      batchC05120PlusRightP004NormUpper2559]

noncomputable def batchC05120PlusRightP005NormUpper2559 : ℝ :=
    ((375542370072449103279329275409028601 :
    ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05120PlusRightP005NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP005NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP005Factor2559 * embedPair2542
      batchN05121PlusP005Center2559‖ ≤
      ((375542370072449072592543907355523221 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP005Factor2559, batchN05121PlusP005Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP005Factor2559 * embedPair2542 batchN05121PlusP005Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP005DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP005Factor2559, batchN05121PlusP005Error2559,
      batchC05120PlusRightP005NormUpper2559]

noncomputable def batchC05120PlusRightP006NormUpper2559 : ℝ :=
    ((746260436457409163764556358512908505 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP006NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP006NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP006Factor2559 * embedPair2542
      batchN05121PlusP006Center2559‖ ≤
      ((746260436457409102785201031471804221 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP006Factor2559, batchN05121PlusP006Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP006Factor2559 * embedPair2542 batchN05121PlusP006Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP006DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP006Factor2559, batchN05121PlusP006Error2559,
      batchC05120PlusRightP006NormUpper2559]

noncomputable def batchC05120PlusRightP007NormUpper2559 : ℝ :=
    ((203100739585498542008286713283217277 :
    ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120PlusRightP007NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP007NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP007Factor2559 * embedPair2542
      batchN05121PlusP007Center2559‖ ≤
      ((101550369792749262706134358029910767 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP007Factor2559, batchN05121PlusP007Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP007Factor2559 * embedPair2542 batchN05121PlusP007Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP007DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP007Factor2559, batchN05121PlusP007Error2559,
      batchC05120PlusRightP007NormUpper2559]

noncomputable def batchC05120PlusRightP008NormUpper2559 : ℝ :=
    ((423389568624478151967871569230771115341
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP008NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP008NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP008Factor2559 * embedPair2542
      batchN05121PlusP008Center2559‖ ≤
      ((211694784312239056737269215966560045999 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP008Factor2559, batchN05121PlusP008Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP008Factor2559 * embedPair2542 batchN05121PlusP008Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP008DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP008Factor2559, batchN05121PlusP008Error2559,
      batchC05120PlusRightP008NormUpper2559]

noncomputable def batchC05120PlusRightP009NormUpper2559 : ℝ :=
    ((1326321029338784301380243680071718145991
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP009NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP009NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP009Factor2559 * embedPair2542
      batchN05121PlusP009Center2559‖ ≤
      ((663160514669392091418184047467064768147 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP009Factor2559, batchN05121PlusP009Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP009Factor2559 * embedPair2542 batchN05121PlusP009Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP009DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP009Factor2559, batchN05121PlusP009Error2559,
      batchC05120PlusRightP009NormUpper2559]

noncomputable def batchC05120PlusRightP010NormUpper2559 : ℝ :=
    ((551615767872443151032989792333416061005
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05120PlusRightP010NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP010NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP010Factor2559 * embedPair2542
      batchN05121PlusP010Center2559‖ ≤
      ((551615767872443101944526388087821683699 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP010Factor2559, batchN05121PlusP010Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP010Factor2559 * embedPair2542 batchN05121PlusP010Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP010DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP010Factor2559, batchN05121PlusP010Error2559,
      batchC05120PlusRightP010NormUpper2559]

noncomputable def batchC05120PlusRightP011NormUpper2559 : ℝ :=
    ((742902957341746032044453557818779025569
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05120PlusRightP011NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP011NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP011Factor2559 * embedPair2542
      batchN05121PlusP011Center2559‖ ≤
      ((2971611829366983864153362280719590445311 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP011Factor2559, batchN05121PlusP011Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP011Factor2559 * embedPair2542 batchN05121PlusP011Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP011DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP011Factor2559, batchN05121PlusP011Error2559,
      batchC05120PlusRightP011NormUpper2559]

noncomputable def batchC05120PlusRightP012NormUpper2559 : ℝ :=
    ((1966862678096541432666778572563668825113
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120PlusRightP012NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP012NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP012Factor2559 * embedPair2542
      batchN05121PlusP012Center2559‖ ≤
      ((983431339048270629030717843241917754801 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP012Factor2559, batchN05121PlusP012Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP012Factor2559 * embedPair2542 batchN05121PlusP012Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP012DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP012Factor2559, batchN05121PlusP012Error2559,
      batchC05120PlusRightP012NormUpper2559]

noncomputable def batchC05120PlusRightP013NormUpper2559 : ℝ :=
    ((4975115180639872910027535079730077431141
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP013NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP013NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP013Factor2559 * embedPair2542
      batchN05121PlusP013Center2559‖ ≤
      ((310944698789992029279157292190737769299 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP013Factor2559, batchN05121PlusP013Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP013Factor2559 * embedPair2542 batchN05121PlusP013Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP013DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP013Factor2559, batchN05121PlusP013Error2559,
      batchC05120PlusRightP013NormUpper2559]

noncomputable def batchC05120PlusRightP014NormUpper2559 : ℝ :=
    ((7364831937805688775261078711046803852033
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP014NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP014NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP014Factor2559 * embedPair2542
      batchN05121PlusP014Center2559‖ ≤
      ((3682415968902844060591776309602103062517 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP014Factor2559, batchN05121PlusP014Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP014Factor2559 * embedPair2542 batchN05121PlusP014Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP014DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP014Factor2559, batchN05121PlusP014Error2559,
      batchC05120PlusRightP014NormUpper2559]

noncomputable def batchC05120PlusRightP015NormUpper2559 : ℝ :=
    ((4741411015991815735455413179506863801849
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120PlusRightP015NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP015NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP015Factor2559 * embedPair2542
      batchN05121PlusP015Center2559‖ ≤
      ((9482822031983630627808797563970921091337 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP015Factor2559, batchN05121PlusP015Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP015Factor2559 * embedPair2542 batchN05121PlusP015Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP015DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP015Factor2559, batchN05121PlusP015Error2559,
      batchC05120PlusRightP015NormUpper2559]

noncomputable def batchC05120PlusRightP016NormUpper2559 : ℝ :=
    ((5621981648985158811184547723812728450857
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120PlusRightP016NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP016NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP016Factor2559 * embedPair2542
      batchN05121PlusP016Center2559‖ ≤
      (((1 * 10^40
        + 1243963297970316621639452868597322255391) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP016Factor2559, batchN05121PlusP016Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP016Factor2559 * embedPair2542 batchN05121PlusP016Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP016DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP016Factor2559, batchN05121PlusP016Error2559,
      batchC05120PlusRightP016NormUpper2559]

noncomputable def batchC05120PlusRightP017NormUpper2559 : ℝ := (((1 * 10^40
        + 5264846474741507581380311132732582134191) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP017NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP017NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP017Factor2559 * embedPair2542
      batchN05121PlusP017Center2559‖ ≤
      ((7632423237370753109681285079157790525209 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP017Factor2559, batchN05121PlusP017Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP017Factor2559 * embedPair2542 batchN05121PlusP017Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP017DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP017Factor2559, batchN05121PlusP017Error2559,
      batchC05120PlusRightP017NormUpper2559]

noncomputable def batchC05120PlusRightP018NormUpper2559 : ℝ := (((1 * 10^40
        + 7005236478192982415746126661341856454499) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP018NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP018NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP018Factor2559 * embedPair2542
      batchN05121PlusP018Center2559‖ ≤
      (((1 * 10^40
        + 7005236478192980896788278969092846826273) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP018Factor2559, batchN05121PlusP018Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP018Factor2559 * embedPair2542 batchN05121PlusP018Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP018DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP018Factor2559, batchN05121PlusP018Error2559,
      batchC05120PlusRightP018NormUpper2559]

noncomputable def batchC05120PlusRightP019NormUpper2559 : ℝ := (((2 * 10^40
        + 478013309952623035040535348346027500735) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP019NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP019NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP019Factor2559 * embedPair2542
      batchN05121PlusP019Center2559‖ ≤
      ((2559751663744077650249483678039482351643 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP019Factor2559, batchN05121PlusP019Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP019Factor2559 * embedPair2542 batchN05121PlusP019Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP019DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP019Factor2559, batchN05121PlusP019Error2559,
      batchC05120PlusRightP019NormUpper2559]

noncomputable def batchC05120PlusRightP020NormUpper2559 : ℝ := (((2 * 10^40
        + 4759635837427922354296032029594614181955) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP020NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP020NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP020Factor2559 * embedPair2542
      batchN05121PlusP020Center2559‖ ≤
      ((6189908959356980033109243801334312833307 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP020Factor2559, batchN05121PlusP020Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP020Factor2559 * embedPair2542 batchN05121PlusP020Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP020DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP020Factor2559, batchN05121PlusP020Error2559,
      batchC05120PlusRightP020NormUpper2559]

noncomputable def batchC05120PlusRightP021NormUpper2559 : ℝ :=
    ((7190004991197448015368539636266700243535
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05120PlusRightP021NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP021NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP021Factor2559 * embedPair2542
      batchN05121PlusP021Center2559‖ ≤
      (((2 * 10^40
        + 8760019964789789474901062454916169510913) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP021Factor2559, batchN05121PlusP021Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP021Factor2559 * embedPair2542 batchN05121PlusP021Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP021DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP021Factor2559, batchN05121PlusP021Error2559,
      batchC05120PlusRightP021NormUpper2559]

noncomputable def batchC05120PlusRightP022NormUpper2559 : ℝ := (((1 * 10^40
        + 5482474628496562244692460815331240565469) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120PlusRightP022NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP022NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP022Factor2559 * embedPair2542
      batchN05121PlusP022Center2559‖ ≤
      (((3 * 10^40
        + 964949256993121701234871792999971500187) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP022Factor2559, batchN05121PlusP022Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP022Factor2559 * embedPair2542 batchN05121PlusP022Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP022DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP022Factor2559, batchN05121PlusP022Error2559,
      batchC05120PlusRightP022NormUpper2559]

noncomputable def batchC05120PlusRightP023NormUpper2559 : ℝ :=
    ((9486999216687741750143545750072429993003
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05120PlusRightP023NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP023NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP023Factor2559 * embedPair2542
      batchN05121PlusP023Center2559‖ ≤
      (((1 * 10^40
        + 8973998433375481785810561386235241403857) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP023Factor2559, batchN05121PlusP023Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP023Factor2559 * embedPair2542 batchN05121PlusP023Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP023DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP023Factor2559, batchN05121PlusP023Error2559,
      batchC05120PlusRightP023NormUpper2559]

noncomputable def batchC05120PlusRightP024NormUpper2559 : ℝ := (((1 * 10^40
        + 370451257070865302769841121635007275351) : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05120PlusRightP024NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP024NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP024Factor2559 * embedPair2542
      batchN05121PlusP024Center2559‖ ≤
      (((2 * 10^40
        + 740902514141728728270744695297917171305) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP024Factor2559, batchN05121PlusP024Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP024Factor2559 * embedPair2542 batchN05121PlusP024Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP024DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP024Factor2559, batchN05121PlusP024Error2559,
      batchC05120PlusRightP024NormUpper2559]

noncomputable def batchC05120PlusRightP025NormUpper2559 : ℝ := (((2 * 10^40
        + 3107241887223714123630263116664071000219) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120PlusRightP025NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP025NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP025Factor2559 * embedPair2542
      batchN05121PlusP025Center2559‖ ≤
      ((2888405235902964003462844367142624025139 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP025Factor2559, batchN05121PlusP025Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP025Factor2559 * embedPair2542 batchN05121PlusP025Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP025DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP025Factor2559, batchN05121PlusP025Error2559,
      batchC05120PlusRightP025NormUpper2559]

noncomputable def batchC05120PlusRightP026NormUpper2559 : ℝ := (((1 * 10^40
        + 2852533683061104252915340203657037114235) : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05120PlusRightP026NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP026NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP026Factor2559 * embedPair2542
      batchN05121PlusP026Center2559‖ ≤
      ((3213133420765275771132581621547686029819 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP026Factor2559, batchN05121PlusP026Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP026Factor2559 * embedPair2542 batchN05121PlusP026Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP026DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP026Factor2559, batchN05121PlusP026Error2559,
      batchC05120PlusRightP026NormUpper2559]

noncomputable def batchC05120PlusRightP027NormUpper2559 : ℝ := (((5 * 10^40
        + 9573827076686913391019416560179332830513) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP027NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP027NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP027Factor2559 * embedPair2542
      batchN05121PlusP027Center2559‖ ≤
      (((5 * 10^40
        + 9573827076686907957498966702562978954483) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP027Factor2559, batchN05121PlusP027Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP027Factor2559 * embedPair2542 batchN05121PlusP027Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP027DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP027Factor2559, batchN05121PlusP027Error2559,
      batchC05120PlusRightP027NormUpper2559]

noncomputable def batchC05120PlusRightP028NormUpper2559 : ℝ := (((6 * 10^40
        + 3031024356863635159361760130371533476935) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP028NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP028NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP028Factor2559 * embedPair2542
      batchN05121PlusP028Center2559‖ ≤
      (((6 * 10^40
        + 3031024356863629402914646931492730980511) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP028Factor2559, batchN05121PlusP028Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP028Factor2559 * embedPair2542 batchN05121PlusP028Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP028DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP028Factor2559, batchN05121PlusP028Error2559,
      batchC05120PlusRightP028NormUpper2559]

noncomputable def batchC05120PlusRightP029NormUpper2559 : ℝ := (((6 * 10^40
        + 8547462118377202954783759829114996128819) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120PlusRightP029NormBound2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05121PlusPosition2559‖ ≤
      batchC05120PlusRightP029NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05121PlusP029Factor2559 * embedPair2542
      batchN05121PlusP029Center2559‖ ≤
      (((6 * 10^40
        + 8547462118377196681795478063208854066927) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05121PlusP029Factor2559, batchN05121PlusP029Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05121PlusPosition2559)
    (embedPair2542 batchN05121PlusP029Factor2559 * embedPair2542 batchN05121PlusP029Center2559) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05121PlusP029DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05121PlusP029Factor2559, batchN05121PlusP029Error2559,
      batchC05120PlusRightP029NormUpper2559]

noncomputable def batchC05120PlusRightNormUpper2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05120PlusRightP000NormUpper2559
  | 1 => batchC05120PlusRightP001NormUpper2559
  | 2 => batchC05120PlusRightP002NormUpper2559
  | 3 => batchC05120PlusRightP003NormUpper2559
  | 4 => batchC05120PlusRightP004NormUpper2559
  | 5 => batchC05120PlusRightP005NormUpper2559
  | 6 => batchC05120PlusRightP006NormUpper2559
  | 7 => batchC05120PlusRightP007NormUpper2559
  | 8 => batchC05120PlusRightP008NormUpper2559
  | 9 => batchC05120PlusRightP009NormUpper2559
  | 10 => batchC05120PlusRightP010NormUpper2559
  | 11 => batchC05120PlusRightP011NormUpper2559
  | 12 => batchC05120PlusRightP012NormUpper2559
  | 13 => batchC05120PlusRightP013NormUpper2559
  | 14 => batchC05120PlusRightP014NormUpper2559
  | 15 => batchC05120PlusRightP015NormUpper2559
  | 16 => batchC05120PlusRightP016NormUpper2559
  | 17 => batchC05120PlusRightP017NormUpper2559
  | 18 => batchC05120PlusRightP018NormUpper2559
  | 19 => batchC05120PlusRightP019NormUpper2559
  | 20 => batchC05120PlusRightP020NormUpper2559
  | 21 => batchC05120PlusRightP021NormUpper2559
  | 22 => batchC05120PlusRightP022NormUpper2559
  | 23 => batchC05120PlusRightP023NormUpper2559
  | 24 => batchC05120PlusRightP024NormUpper2559
  | 25 => batchC05120PlusRightP025NormUpper2559
  | 26 => batchC05120PlusRightP026NormUpper2559
  | 27 => batchC05120PlusRightP027NormUpper2559
  | 28 => batchC05120PlusRightP028NormUpper2559
  | 29 => batchC05120PlusRightP029NormUpper2559
  | _ => 0

theorem batchC05120PlusRightNormBound2559 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 i batchN05121PlusPosition2559‖ ≤
        batchC05120PlusRightNormUpper2559 i := by
  fin_cases i
  · exact batchC05120PlusRightP000NormBound2559
  · exact batchC05120PlusRightP001NormBound2559
  · exact batchC05120PlusRightP002NormBound2559
  · exact batchC05120PlusRightP003NormBound2559
  · exact batchC05120PlusRightP004NormBound2559
  · exact batchC05120PlusRightP005NormBound2559
  · exact batchC05120PlusRightP006NormBound2559
  · exact batchC05120PlusRightP007NormBound2559
  · exact batchC05120PlusRightP008NormBound2559
  · exact batchC05120PlusRightP009NormBound2559
  · exact batchC05120PlusRightP010NormBound2559
  · exact batchC05120PlusRightP011NormBound2559
  · exact batchC05120PlusRightP012NormBound2559
  · exact batchC05120PlusRightP013NormBound2559
  · exact batchC05120PlusRightP014NormBound2559
  · exact batchC05120PlusRightP015NormBound2559
  · exact batchC05120PlusRightP016NormBound2559
  · exact batchC05120PlusRightP017NormBound2559
  · exact batchC05120PlusRightP018NormBound2559
  · exact batchC05120PlusRightP019NormBound2559
  · exact batchC05120PlusRightP020NormBound2559
  · exact batchC05120PlusRightP021NormBound2559
  · exact batchC05120PlusRightP022NormBound2559
  · exact batchC05120PlusRightP023NormBound2559
  · exact batchC05120PlusRightP024NormBound2559
  · exact batchC05120PlusRightP025NormBound2559
  · exact batchC05120PlusRightP026NormBound2559
  · exact batchC05120PlusRightP027NormBound2559
  · exact batchC05120PlusRightP028NormBound2559
  · exact batchC05120PlusRightP029NormBound2559

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP000NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP001NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP002NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP003NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP004NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP005NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP006NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP007NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP008NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP009NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP010NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP011NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP012NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP013NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP014NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP015NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP016NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP017NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP018NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP019NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP020NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP021NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP022NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP023NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP024NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP025NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP026NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP027NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP028NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusRightP029NormBound2559
