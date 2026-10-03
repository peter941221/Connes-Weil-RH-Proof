import ConnesWeilRH.Dev.C1RouteABatchN05119Minus2559
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC05119MinusLeftP000NormUpper2559 : ℝ :=
    ((8425792448240356856179396507625368366869
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP000NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05119MinusPosition2559‖ ≤
      batchC05119MinusLeftP000NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP000Factor2559 * embedPair2542
      batchN05119MinusP000Center2559‖
      ≤
      ((4212896224120178053899557389365114876069 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP000Factor2559, batchN05119MinusP000Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP000Factor2559 * embedPair2542 batchN05119MinusP000Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP000DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP000Factor2559, batchN05119MinusP000Error2559,
      batchC05119MinusLeftP000NormUpper2559]

noncomputable def batchC05119MinusLeftP001NormUpper2559 : ℝ :=
    ((4181345285740593178472567403547733960867
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05119MinusLeftP001NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05119MinusPosition2559‖ ≤
      batchC05119MinusLeftP001NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP001Factor2559 * embedPair2542
      batchN05119MinusP001Center2559‖
      ≤
      ((8362690571481185613779723950337132645463 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP001Factor2559, batchN05119MinusP001Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP001Factor2559 * embedPair2542 batchN05119MinusP001Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP001DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP001Factor2559, batchN05119MinusP001Error2559,
      batchC05119MinusLeftP001NormUpper2559]

noncomputable def batchC05119MinusLeftP002NormUpper2559 : ℝ :=
    ((2082508649995797020577406667865061946535
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05119MinusLeftP002NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05119MinusPosition2559‖ ≤
      batchC05119MinusLeftP002NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP002Factor2559 * embedPair2542
      batchN05119MinusP002Center2559‖
      ≤
      ((8330034599983187341843551138828734636269 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP002Factor2559, batchN05119MinusP002Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP002Factor2559 * embedPair2542 batchN05119MinusP002Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP002DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP002Factor2559, batchN05119MinusP002Error2559,
      batchC05119MinusLeftP002NormUpper2559]

noncomputable def batchC05119MinusLeftP003NormUpper2559 : ℝ :=
    ((8311776975468623559151498017008779978907
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP003NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05119MinusPosition2559‖ ≤
      batchC05119MinusLeftP003NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP003Factor2559 * embedPair2542
      batchN05119MinusP003Center2559‖
      ≤
      ((8311776975468622820194765582324153579715 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP003Factor2559, batchN05119MinusP003Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP003Factor2559 * embedPair2542 batchN05119MinusP003Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP003DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP003Factor2559, batchN05119MinusP003Error2559,
      batchC05119MinusLeftP003NormUpper2559]

noncomputable def batchC05119MinusLeftP004NormUpper2559 : ℝ :=
    ((8300927805522046300097058100457580011179
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP004NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05119MinusPosition2559‖ ≤
      batchC05119MinusLeftP004NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP004Factor2559 * embedPair2542
      batchN05119MinusP004Center2559‖
      ≤
      ((8300927805522045562037276243265774071805 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP004Factor2559, batchN05119MinusP004Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP004Factor2559 * embedPair2542 batchN05119MinusP004Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP004DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP004Factor2559, batchN05119MinusP004Error2559,
      batchC05119MinusLeftP004NormUpper2559]

noncomputable def batchC05119MinusLeftP005NormUpper2559 : ℝ :=
    ((375542370072449103279329275409028601 : ℝ)
    /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05119MinusLeftP005NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05119MinusPosition2559‖ ≤
      batchC05119MinusLeftP005NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP005Factor2559 * embedPair2542
      batchN05119MinusP005Center2559‖
      ≤
      ((375542370072449072592543907355523221 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP005Factor2559, batchN05119MinusP005Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP005Factor2559 * embedPair2542 batchN05119MinusP005Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP005DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP005Factor2559, batchN05119MinusP005Error2559,
      batchC05119MinusLeftP005NormUpper2559]

noncomputable def batchC05119MinusLeftP006NormUpper2559 : ℝ :=
    ((746260436457409163764556358512908505 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP006NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05119MinusPosition2559‖ ≤
      batchC05119MinusLeftP006NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP006Factor2559 * embedPair2542
      batchN05119MinusP006Center2559‖
      ≤
      ((746260436457409102785201031471804221 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP006Factor2559, batchN05119MinusP006Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP006Factor2559 * embedPair2542 batchN05119MinusP006Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP006DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP006Factor2559, batchN05119MinusP006Error2559,
      batchC05119MinusLeftP006NormUpper2559]

noncomputable def batchC05119MinusLeftP007NormUpper2559 : ℝ :=
    ((203100739585498542008286713283217277 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05119MinusLeftP007NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05119MinusPosition2559‖ ≤
      batchC05119MinusLeftP007NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP007Factor2559 * embedPair2542
      batchN05119MinusP007Center2559‖
      ≤
      ((101550369792749262706134358029910767 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP007Factor2559, batchN05119MinusP007Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP007Factor2559 * embedPair2542 batchN05119MinusP007Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP007DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP007Factor2559, batchN05119MinusP007Error2559,
      batchC05119MinusLeftP007NormUpper2559]

noncomputable def batchC05119MinusLeftP008NormUpper2559 : ℝ :=
    ((423389568624478151967871569230771115285 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP008NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05119MinusPosition2559‖ ≤
      batchC05119MinusLeftP008NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP008Factor2559 * embedPair2542
      batchN05119MinusP008Center2559‖
      ≤
      ((211694784312239056737269215966560045971 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP008Factor2559, batchN05119MinusP008Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP008Factor2559 * embedPair2542 batchN05119MinusP008Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP008DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP008Factor2559, batchN05119MinusP008Error2559,
      batchC05119MinusLeftP008NormUpper2559]

noncomputable def batchC05119MinusLeftP009NormUpper2559 : ℝ :=
    ((663160514669392150690121840035859072865 :
    ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05119MinusLeftP009NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05119MinusPosition2559‖ ≤
      batchC05119MinusLeftP009NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP009Factor2559 * embedPair2542
      batchN05119MinusP009Center2559‖
      ≤
      ((1326321029338784182836368094934129536033 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP009Factor2559, batchN05119MinusP009Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP009Factor2559 * embedPair2542 batchN05119MinusP009Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP009DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP009Factor2559, batchN05119MinusP009Error2559,
      batchC05119MinusLeftP009NormUpper2559]

noncomputable def batchC05119MinusLeftP010NormUpper2559 : ℝ :=
    ((137903941968110787758247448083354015219 :
    ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

theorem batchC05119MinusLeftP010NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP010NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP010Factor2559 * embedPair2542
      batchN05119MinusP010Center2559‖
      ≤
      ((275807883936221550972263194043910841785 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP010Factor2559, batchN05119MinusP010Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP010Factor2559 * embedPair2542 batchN05119MinusP010Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP010DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP010Factor2559, batchN05119MinusP010Error2559,
      batchC05119MinusLeftP010NormUpper2559]

noncomputable def batchC05119MinusLeftP011NormUpper2559 : ℝ :=
    ((2971611829366984128177814231275116101507
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP011NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP011NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP011Factor2559 * embedPair2542
      batchN05119MinusP011Center2559‖
      ≤
      ((1485805914683491932076681140359795222271 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP011Factor2559, batchN05119MinusP011Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP011Factor2559 * embedPair2542 batchN05119MinusP011Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP011DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP011Factor2559, batchN05119MinusP011Error2559,
      batchC05119MinusLeftP011NormUpper2559]

noncomputable def batchC05119MinusLeftP012NormUpper2559 : ℝ :=
    ((3933725356193082865333557145127337649107
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP012NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP012NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP012Factor2559 * embedPair2542
      batchN05119MinusP012Center2559‖
      ≤
      ((3933725356193082516122871372967671018085 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP012Factor2559, batchN05119MinusP012Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP012Factor2559 * embedPair2542 batchN05119MinusP012Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP012DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP012Factor2559, batchN05119MinusP012Error2559,
      batchC05119MinusLeftP012NormUpper2559]

noncomputable def batchC05119MinusLeftP013NormUpper2559 : ℝ :=
    ((4975115180639872910027535079730077429609
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP013NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP013NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP013Factor2559 * embedPair2542
      batchN05119MinusP013Center2559‖
      ≤
      ((1243778795159968117116629168762951076813 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP013Factor2559, batchN05119MinusP013Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP013Factor2559 * embedPair2542 batchN05119MinusP013Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP013DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP013Factor2559, batchN05119MinusP013Error2559,
      batchC05119MinusLeftP013NormUpper2559]

noncomputable def batchC05119MinusLeftP014NormUpper2559 : ℝ :=
    ((7364831937805688775261078711046803849445
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP014NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP014NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP014Factor2559 * embedPair2542
      batchN05119MinusP014Center2559‖
      ≤
      ((3682415968902844060591776309602103061223 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP014Factor2559, batchN05119MinusP014Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP014Factor2559 * embedPair2542 batchN05119MinusP014Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP014DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP014Factor2559, batchN05119MinusP014Error2559,
      batchC05119MinusLeftP014NormUpper2559]

noncomputable def batchC05119MinusLeftP015NormUpper2559 : ℝ :=
    ((9482822031983631470910826359013727600071
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP015NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP015NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP015Factor2559 * embedPair2542
      batchN05119MinusP015Center2559‖
      ≤
      ((4741411015991815313904398781985460543855 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP015Factor2559, batchN05119MinusP015Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP015Factor2559 * embedPair2542 batchN05119MinusP015Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP015DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP015Factor2559, batchN05119MinusP015Error2559,
      batchC05119MinusLeftP015NormUpper2559]

noncomputable def batchC05119MinusLeftP016NormUpper2559 : ℝ := (((1 * 10^40
        + 1243963297970317622369095447625456897159) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP016NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP016NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP016Factor2559 * embedPair2542
      batchN05119MinusP016Center2559‖
      ≤
      ((2810990824492579155409863217149330562709 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP016Factor2559, batchN05119MinusP016Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP016Factor2559 * embedPair2542 batchN05119MinusP016Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP016DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP016Factor2559, batchN05119MinusP016Error2559,
      batchC05119MinusLeftP016NormUpper2559]

noncomputable def batchC05119MinusLeftP017NormUpper2559 : ℝ := (((1 * 10^40
        + 5264846474741507581380311132732582127341) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP017NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP017NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP017Factor2559 * embedPair2542
      batchN05119MinusP017Center2559‖
      ≤
      ((954052904671344138710160634894723815223 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP017Factor2559, batchN05119MinusP017Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP017Factor2559 * embedPair2542 batchN05119MinusP017Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP017DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP017Factor2559, batchN05119MinusP017Error2559,
      batchC05119MinusLeftP017NormUpper2559]

noncomputable def batchC05119MinusLeftP018NormUpper2559 : ℝ := (((1 * 10^40
        + 7005236478192982415746126661341856446587) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP018NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP018NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP018Factor2559 * embedPair2542
      batchN05119MinusP018Center2559‖
      ≤
      (((1 * 10^40
        + 7005236478192980896788278969092846818361) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP018Factor2559, batchN05119MinusP018Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP018Factor2559 * embedPair2542 batchN05119MinusP018Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP018DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP018Factor2559, batchN05119MinusP018Error2559,
      batchC05119MinusLeftP018NormUpper2559]

noncomputable def batchC05119MinusLeftP019NormUpper2559 : ℝ := (((2 * 10^40
        + 478013309952623035040535348346027490597) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP019NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP019NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP019Factor2559 * embedPair2542
      batchN05119MinusP019Center2559‖
      ≤
      (((1 * 10^40
        + 239006654976310600997934712157929401503) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP019Factor2559, batchN05119MinusP019Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP019Factor2559 * embedPair2542 batchN05119MinusP019Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP019DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP019Factor2559, batchN05119MinusP019Error2559,
      batchC05119MinusLeftP019NormUpper2559]

noncomputable def batchC05119MinusLeftP020NormUpper2559 : ℝ := (((2 * 10^40
        + 4759635837427922354296032029594614168895) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP020NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP020NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP020Factor2559 * embedPair2542
      batchN05119MinusP020Center2559‖
      ≤
      ((3094954479678490016554621900667156415021 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP020Factor2559, batchN05119MinusP020Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP020Factor2559 * embedPair2542 batchN05119MinusP020Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP020DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP020Factor2559, batchN05119MinusP020Error2559,
      batchC05119MinusLeftP020NormUpper2559]

noncomputable def batchC05119MinusLeftP021NormUpper2559 : ℝ := (((2 * 10^40
        + 8760019964789792061474158545066800958191) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP021NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP021NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP021Factor2559 * embedPair2542
      batchN05119MinusP021Center2559‖
      ≤
      ((7190004991197447368725265613729042373741 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP021Factor2559, batchN05119MinusP021Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP021Factor2559 * embedPair2542 batchN05119MinusP021Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP021DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP021Factor2559, batchN05119MinusP021Error2559,
      batchC05119MinusLeftP021NormUpper2559]

noncomputable def batchC05119MinusLeftP022NormUpper2559 : ℝ := (((3 * 10^40
        + 964949256993124489384921630662481113337) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP022NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP022NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP022Factor2559 * embedPair2542
      batchN05119MinusP022Center2559‖
      ≤
      (((1 * 10^40
        + 5482474628496560850617435896499985741293) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP022Factor2559, batchN05119MinusP022Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP022Factor2559 * embedPair2542 batchN05119MinusP022Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP022DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP022Factor2559, batchN05119MinusP022Error2559,
      batchC05119MinusLeftP022NormUpper2559]

noncomputable def batchC05119MinusLeftP023NormUpper2559 : ℝ := (((3 * 10^40
        + 7947996866750967000574183000289719948927) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP023NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP023NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP023Factor2559 * embedPair2542
      batchN05119MinusP023Center2559‖
      ≤
      (((3 * 10^40
        + 7947996866750963571621122772470482784629) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP023Factor2559, batchN05119MinusP023Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP023Factor2559 * embedPair2542 batchN05119MinusP023Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP023DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP023Factor2559, batchN05119MinusP023Error2559,
      batchC05119MinusLeftP023NormUpper2559]

noncomputable def batchC05119MinusLeftP024NormUpper2559 : ℝ := (((4 * 10^40
        + 1481805028283461211079364486540029075409) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP024NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP024NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP024Factor2559 * embedPair2542
      batchN05119MinusP024Center2559‖
      ≤
      (((4 * 10^40
        + 1481805028283457456541489390595834316615) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP024Factor2559, batchN05119MinusP024Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP024Factor2559 * embedPair2542 batchN05119MinusP024Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP024DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP024Factor2559, batchN05119MinusP024Error2559,
      batchC05119MinusLeftP024NormUpper2559]

noncomputable def batchC05119MinusLeftP025NormUpper2559 : ℝ := (((4 * 10^40
        + 6214483774447428247260526233328141970415) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP025NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP025NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP025Factor2559 * embedPair2542
      batchN05119MinusP025Center2559‖
      ≤
      (((4 * 10^40
        + 6214483774447424055405509874281984372201) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP025Factor2559, batchN05119MinusP025Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP025Factor2559 * embedPair2542 batchN05119MinusP025Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP025DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP025Factor2559, batchN05119MinusP025Error2559,
      batchC05119MinusLeftP025NormUpper2559]

noncomputable def batchC05119MinusLeftP026NormUpper2559 : ℝ := (((5 * 10^40
        + 1410134732244417011661360814628148422335) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP026NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP026NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP026Factor2559 * embedPair2542
      batchN05119MinusP026Center2559‖
      ≤
      (((5 * 10^40
        + 1410134732244412338121305944762976442499) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP026Factor2559, batchN05119MinusP026Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP026Factor2559 * embedPair2542 batchN05119MinusP026Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP026DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP026Factor2559, batchN05119MinusP026Error2559,
      batchC05119MinusLeftP026NormUpper2559]

noncomputable def batchC05119MinusLeftP027NormUpper2559 : ℝ := (((5 * 10^40
        + 9573827076686913391019416560179332788395) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP027NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP027NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP027Factor2559 * embedPair2542
      batchN05119MinusP027Center2559‖
      ≤
      (((5 * 10^40
        + 9573827076686907957498966702562978912365) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP027Factor2559, batchN05119MinusP027Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP027Factor2559 * embedPair2542 batchN05119MinusP027Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP027DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP027Factor2559, batchN05119MinusP027Error2559,
      batchC05119MinusLeftP027NormUpper2559]

noncomputable def batchC05119MinusLeftP028NormUpper2559 : ℝ :=
    ((7878878044607954394920220016296441678941
    : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem batchC05119MinusLeftP028NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP028NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP028Factor2559 * embedPair2542
      batchN05119MinusP028Center2559‖
      ≤
      ((984859755575994209420541358304573920861 : ℝ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP028Factor2559, batchN05119MinusP028Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP028Factor2559 * embedPair2542 batchN05119MinusP028Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP028DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP028Factor2559, batchN05119MinusP028Error2559,
      batchC05119MinusLeftP028NormUpper2559]

noncomputable def batchC05119MinusLeftP029NormUpper2559 : ℝ := (((6 * 10^40
        + 8547462118377202954783759829114996078039) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05119MinusLeftP029NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05119MinusPosition2559‖
        ≤
      batchC05119MinusLeftP029NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05119MinusP029Factor2559 * embedPair2542
      batchN05119MinusP029Center2559‖
      ≤
      (((6 * 10^40
        + 8547462118377196681795478063208854016147) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05119MinusP029Factor2559, batchN05119MinusP029Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05119MinusPosition2559)
    (embedPair2542 batchN05119MinusP029Factor2559 * embedPair2542 batchN05119MinusP029Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05119MinusP029DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05119MinusP029Factor2559, batchN05119MinusP029Error2559,
      batchC05119MinusLeftP029NormUpper2559]

noncomputable def batchC05119MinusLeftNormUpper2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05119MinusLeftP000NormUpper2559
  | 1 => batchC05119MinusLeftP001NormUpper2559
  | 2 => batchC05119MinusLeftP002NormUpper2559
  | 3 => batchC05119MinusLeftP003NormUpper2559
  | 4 => batchC05119MinusLeftP004NormUpper2559
  | 5 => batchC05119MinusLeftP005NormUpper2559
  | 6 => batchC05119MinusLeftP006NormUpper2559
  | 7 => batchC05119MinusLeftP007NormUpper2559
  | 8 => batchC05119MinusLeftP008NormUpper2559
  | 9 => batchC05119MinusLeftP009NormUpper2559
  | 10 => batchC05119MinusLeftP010NormUpper2559
  | 11 => batchC05119MinusLeftP011NormUpper2559
  | 12 => batchC05119MinusLeftP012NormUpper2559
  | 13 => batchC05119MinusLeftP013NormUpper2559
  | 14 => batchC05119MinusLeftP014NormUpper2559
  | 15 => batchC05119MinusLeftP015NormUpper2559
  | 16 => batchC05119MinusLeftP016NormUpper2559
  | 17 => batchC05119MinusLeftP017NormUpper2559
  | 18 => batchC05119MinusLeftP018NormUpper2559
  | 19 => batchC05119MinusLeftP019NormUpper2559
  | 20 => batchC05119MinusLeftP020NormUpper2559
  | 21 => batchC05119MinusLeftP021NormUpper2559
  | 22 => batchC05119MinusLeftP022NormUpper2559
  | 23 => batchC05119MinusLeftP023NormUpper2559
  | 24 => batchC05119MinusLeftP024NormUpper2559
  | 25 => batchC05119MinusLeftP025NormUpper2559
  | 26 => batchC05119MinusLeftP026NormUpper2559
  | 27 => batchC05119MinusLeftP027NormUpper2559
  | 28 => batchC05119MinusLeftP028NormUpper2559
  | 29 => batchC05119MinusLeftP029NormUpper2559
  | _ => 0

theorem batchC05119MinusLeftNormBound2559 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 i batchN05119MinusPosition2559‖ ≤
        batchC05119MinusLeftNormUpper2559 i := by
  fin_cases i
  · exact batchC05119MinusLeftP000NormBound2559
  · exact batchC05119MinusLeftP001NormBound2559
  · exact batchC05119MinusLeftP002NormBound2559
  · exact batchC05119MinusLeftP003NormBound2559
  · exact batchC05119MinusLeftP004NormBound2559
  · exact batchC05119MinusLeftP005NormBound2559
  · exact batchC05119MinusLeftP006NormBound2559
  · exact batchC05119MinusLeftP007NormBound2559
  · exact batchC05119MinusLeftP008NormBound2559
  · exact batchC05119MinusLeftP009NormBound2559
  · exact batchC05119MinusLeftP010NormBound2559
  · exact batchC05119MinusLeftP011NormBound2559
  · exact batchC05119MinusLeftP012NormBound2559
  · exact batchC05119MinusLeftP013NormBound2559
  · exact batchC05119MinusLeftP014NormBound2559
  · exact batchC05119MinusLeftP015NormBound2559
  · exact batchC05119MinusLeftP016NormBound2559
  · exact batchC05119MinusLeftP017NormBound2559
  · exact batchC05119MinusLeftP018NormBound2559
  · exact batchC05119MinusLeftP019NormBound2559
  · exact batchC05119MinusLeftP020NormBound2559
  · exact batchC05119MinusLeftP021NormBound2559
  · exact batchC05119MinusLeftP022NormBound2559
  · exact batchC05119MinusLeftP023NormBound2559
  · exact batchC05119MinusLeftP024NormBound2559
  · exact batchC05119MinusLeftP025NormBound2559
  · exact batchC05119MinusLeftP026NormBound2559
  · exact batchC05119MinusLeftP027NormBound2559
  · exact batchC05119MinusLeftP028NormBound2559
  · exact batchC05119MinusLeftP029NormBound2559

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP000NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP001NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP002NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP003NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP004NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP005NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP006NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP007NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP008NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP009NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP010NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP011NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP012NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP013NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP014NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP015NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP016NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP017NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP018NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP019NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP020NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP021NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP022NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP023NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP024NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP025NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP026NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP027NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP028NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusLeftP029NormBound2559
