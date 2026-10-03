import ConnesWeilRH.Dev.C1RouteABatchN05120Minus2559
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def batchC05120MinusLeftP000NormUpper2559 : ℝ :=
    ((526284758248456079249360615864440951069 :
    ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

theorem batchC05120MinusLeftP000NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05120MinusPosition2559‖ ≤
      batchC05120MinusLeftP000NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP000Factor2559 * embedPair2542
      batchN05120MinusP000Center2559‖
      ≤
      ((8420556131975296554415754351237264202501 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP000Factor2559, batchN05120MinusP000Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP000Factor2559 * embedPair2542 batchN05120MinusP000Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP000DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP000Factor2559, batchN05120MinusP000Error2559,
      batchC05120MinusLeftP000NormUpper2559]

noncomputable def batchC05120MinusLeftP001NormUpper2559 : ℝ :=
    ((2089357236962449690116701527176865466317
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05120MinusLeftP001NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05120MinusPosition2559‖ ≤
      batchC05120MinusLeftP001NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP001Factor2559 * embedPair2542
      batchN05120MinusP001Center2559‖
      ≤
      ((65292413655076547282173072953760805953 : ℝ) /
        (1141798 * 10^40
        + 1541647679048466287755595961091061972992)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP001Factor2559, batchN05120MinusP001Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP001Factor2559 * embedPair2542 batchN05120MinusP001Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP001DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP001Factor2559, batchN05120MinusP001Error2559,
      batchC05120MinusLeftP001NormUpper2559]

noncomputable def batchC05120MinusLeftP002NormUpper2559 : ℝ :=
    ((8324759605818580766525653060054592199387
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusLeftP002NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05120MinusPosition2559‖ ≤
      batchC05120MinusLeftP002NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP002Factor2559 * embedPair2542
      batchN05120MinusP002Center2559‖
      ≤
      ((2081189901454645015220305027512775985101 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP002Factor2559, batchN05120MinusP002Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP002Factor2559 * embedPair2542 batchN05120MinusP002Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP002DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP002Factor2559, batchN05120MinusP002Error2559,
      batchC05120MinusLeftP002NormUpper2559]

noncomputable def batchC05120MinusLeftP003NormUpper2559 : ℝ :=
    ((8306494422594220533726182836180070780065
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusLeftP003NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05120MinusPosition2559‖ ≤
      batchC05120MinusLeftP003NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP003Factor2559 * embedPair2542
      batchN05120MinusP003Center2559‖
      ≤
      ((129788975353034684837400965525657429707 : ℝ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP003Factor2559, batchN05120MinusP003Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP003Factor2559 * embedPair2542 batchN05120MinusP003Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP003DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP003Factor2559, batchN05120MinusP003Error2559,
      batchC05120MinusLeftP003NormUpper2559]

noncomputable def batchC05120MinusLeftP004NormUpper2559 : ℝ :=
    ((1036955091544409685656355038743970294123
    : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

theorem batchC05120MinusLeftP004NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05120MinusPosition2559‖ ≤
      batchC05120MinusLeftP004NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP004Factor2559 * embedPair2542
      batchN05120MinusP004Center2559‖
      ≤
      ((518477545772204798876046327766794806137 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP004Factor2559, batchN05120MinusP004Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP004Factor2559 * embedPair2542 batchN05120MinusP004Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP004DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP004Factor2559, batchN05120MinusP004Error2559,
      batchC05120MinusLeftP004NormUpper2559]

noncomputable def batchC05120MinusLeftP005NormUpper2559 : ℝ :=
    ((1528053298479381539174280585986166707 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusLeftP005NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05120MinusPosition2559‖ ≤
      batchC05120MinusLeftP005NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP005Factor2559 * embedPair2542
      batchN05120MinusP005Center2559‖
      ≤
      ((382013324619845353577403791654689015 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP005Factor2559, batchN05120MinusP005Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP005Factor2559 * embedPair2542 batchN05120MinusP005Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP005DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP005Factor2559, batchN05120MinusP005Error2559,
      batchC05120MinusLeftP005NormUpper2559]

noncomputable def batchC05120MinusLeftP006NormUpper2559 : ℝ :=
    ((752189970976684950649426825571052327 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusLeftP006NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05120MinusPosition2559‖ ≤
      batchC05120MinusLeftP006NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP006Factor2559 * embedPair2542
      batchN05120MinusP006Center2559‖
      ≤
      ((188047492744171222296081663618990787 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP006Factor2559, batchN05120MinusP006Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP006Factor2559 * embedPair2542 batchN05120MinusP006Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP006DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP006Factor2559, batchN05120MinusP006Error2559,
      batchC05120MinusLeftP006NormUpper2559]

noncomputable def batchC05120MinusLeftP007NormUpper2559 : ℝ :=
    ((203887069873478714518116722596585433 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusLeftP007NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05120MinusPosition2559‖ ≤
      batchC05120MinusLeftP007NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP007Factor2559 * embedPair2542
      batchN05120MinusP007Center2559‖
      ≤
      ((407774139746957395715025620280876893 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP007Factor2559, batchN05120MinusP007Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP007Factor2559 * embedPair2542 batchN05120MinusP007Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP007DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP007Factor2559, batchN05120MinusP007Error2559,
      batchC05120MinusLeftP007NormUpper2559]

noncomputable def batchC05120MinusLeftP008NormUpper2559 : ℝ :=
    ((423141806495961073059027186302670247753 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusLeftP008NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05120MinusPosition2559‖ ≤
      batchC05120MinusLeftP008NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP008Factor2559 * embedPair2542
      batchN05120MinusP008Center2559‖
      ≤
      ((423141806495961035202299924170000862703 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP008Factor2559, batchN05120MinusP008Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP008Factor2559 * embedPair2542 batchN05120MinusP008Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP008DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP008Factor2559, batchN05120MinusP008Error2559,
      batchC05120MinusLeftP008NormUpper2559]

noncomputable def batchC05120MinusLeftP009NormUpper2559 : ℝ :=
    ((662755986871443343741131595796564248539 :
    ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusLeftP009NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05120MinusPosition2559‖ ≤
      batchC05120MinusLeftP009NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP009Factor2559 * embedPair2542
      batchN05120MinusP009Center2559‖
      ≤
      ((1325511973742886571917481813964612062549 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP009Factor2559, batchN05120MinusP009Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP009Factor2559 * embedPair2542 batchN05120MinusP009Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP009DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP009Factor2559, batchN05120MinusP009Error2559,
      batchC05120MinusLeftP009NormUpper2559]

noncomputable def batchC05120MinusLeftP010NormUpper2559 : ℝ :=
    ((1102551055181160475677549407434233324137
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusLeftP010NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP010NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP010Factor2559 * embedPair2542
      batchN05120MinusP010Center2559‖
      ≤
      ((1102551055181160380443692376074047873555 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP010Factor2559, batchN05120MinusP010Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP010Factor2559 * embedPair2542 batchN05120MinusP010Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP010DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP010Factor2559, batchN05120MinusP010Error2559,
      batchC05120MinusLeftP010NormUpper2559]

noncomputable def batchC05120MinusLeftP011NormUpper2559 : ℝ :=
    ((1484884841627663397939260725405345882251
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusLeftP011NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP011NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP011Factor2559 * embedPair2542
      batchN05120MinusP011Center2559‖
      ≤
      ((1484884841627663270305609575225042944207 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP011Factor2559, batchN05120MinusP011Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP011Factor2559 * embedPair2542 batchN05120MinusP011Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP011DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP011Factor2559, batchN05120MinusP011Error2559,
      batchC05120MinusLeftP011NormUpper2559]

noncomputable def batchC05120MinusLeftP012NormUpper2559 : ℝ :=
    ((1965638578104343949050426997477193294119
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusLeftP012NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP012NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP012Factor2559 * embedPair2542
      batchN05120MinusP012Center2559‖
      ≤
      ((1965638578104343780808205272548656054443 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP012Factor2559, batchN05120MinusP012Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP012Factor2559 * embedPair2542 batchN05120MinusP012Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP012DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP012Factor2559, batchN05120MinusP012Error2559,
      batchC05120MinusLeftP012NormUpper2559]

noncomputable def batchC05120MinusLeftP013NormUpper2559 : ℝ :=
    ((4972010192980343977342239962793157675205
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusLeftP013NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP013NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP013Factor2559 * embedPair2542
      batchN05120MinusP013Center2559‖
      ≤
      ((2486005096490171776590036225336624656957 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP013Factor2559, batchN05120MinusP013Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP013Factor2559 * embedPair2542 batchN05120MinusP013Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP013DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP013Factor2559, batchN05120MinusP013Error2559,
      batchC05120MinusLeftP013NormUpper2559]

noncomputable def batchC05120MinusLeftP014NormUpper2559 : ℝ :=
    ((3680108966330099686651185823142825913981
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusLeftP014NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP014NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP014Factor2559 * embedPair2542
      batchN05120MinusP014Center2559‖
      ≤
      ((1840054483165049687137128637565592517285 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP014Factor2559, batchN05120MinusP014Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP014Factor2559 * embedPair2542 batchN05120MinusP014Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP014DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP014Factor2559, batchN05120MinusP014Error2559,
      batchC05120MinusLeftP014NormUpper2559]

noncomputable def batchC05120MinusLeftP015NormUpper2559 : ℝ :=
    ((296152164867750540151158364101121627529 :
    ℝ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968))

theorem batchC05120MinusLeftP015NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP015NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP015Factor2559 * embedPair2542
      batchN05120MinusP015Center2559‖
      ≤
      ((9476869275768016482777792594102310374567 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP015Factor2559, batchN05120MinusP015Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP015Factor2559 * embedPair2542 batchN05120MinusP015Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP015DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP015Factor2559, batchN05120MinusP015Error2559,
      batchC05120MinusLeftP015NormUpper2559]

noncomputable def batchC05120MinusLeftP016NormUpper2559 : ℝ := (((1 * 10^40
        + 1236896746461363291781814427397629426897) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusLeftP016NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP016NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP016Factor2559 * embedPair2542
      batchN05120MinusP016Center2559‖
      ≤
      ((2809224186615340585632841839188337330709 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP016Factor2559, batchN05120MinusP016Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP016Factor2559 * embedPair2542 batchN05120MinusP016Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP016DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP016Factor2559, batchN05120MinusP016Error2559,
      batchC05120MinusLeftP016NormUpper2559]

noncomputable def batchC05120MinusLeftP017NormUpper2559 : ℝ := (((1 * 10^40
        + 5255235643290231323276409232338195269825) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusLeftP017NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP017NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP017Factor2559 * embedPair2542
      batchN05120MinusP017Center2559‖
      ≤
      (((1 * 10^40
        + 5255235643290230038564699820246749951005) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP017Factor2559, batchN05120MinusP017Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP017Factor2559 * embedPair2542 batchN05120MinusP017Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP017DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP017Factor2559, batchN05120MinusP017Error2559,
      batchC05120MinusLeftP017NormUpper2559]

noncomputable def batchC05120MinusLeftP018NormUpper2559 : ℝ :=
    ((4248630990648346923527393649470703726203
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

theorem batchC05120MinusLeftP018NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP018NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP018Factor2559 * embedPair2542
      batchN05120MinusP018Center2559‖
      ≤
      (((1 * 10^40
        + 6994523962593386264395424304308228597211) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP018Factor2559, batchN05120MinusP018Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP018Factor2559 * embedPair2542 batchN05120MinusP018Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP018DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP018Factor2559, batchN05120MinusP018Error2559,
      batchC05120MinusLeftP018NormUpper2559]

noncomputable def batchC05120MinusLeftP019NormUpper2559 : ℝ := (((1 * 10^40
        + 232550971422358365485765875986526455299) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusLeftP019NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP019NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP019Factor2559 * embedPair2542
      batchN05120MinusP019Center2559‖
      ≤
      (((2 * 10^40
        + 465101942844715012194475818489805426779) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP019Factor2559, batchN05120MinusP019Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP019Factor2559 * embedPair2542 batchN05120MinusP019Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP019DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP019Factor2559, batchN05120MinusP019Error2559,
      batchC05120MinusLeftP019NormUpper2559]

noncomputable def batchC05120MinusLeftP020NormUpper2559 : ℝ :=
    ((193312599350813676566430721055806795647 :
    ℝ) /
        (1141798 * 10^40
        + 1541647679048466287755595961091061972992))

theorem batchC05120MinusLeftP020NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP020NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP020Factor2559 * embedPair2542
      batchN05120MinusP020Center2559‖
      ≤
      (((2 * 10^40
        + 4744012716904148525743810258765383000283) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP020Factor2559, batchN05120MinusP020Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP020Factor2559 * embedPair2542 batchN05120MinusP020Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP020DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP020Factor2559, batchN05120MinusP020Error2559,
      batchC05120MinusLeftP020NormUpper2559]

noncomputable def batchC05120MinusLeftP021NormUpper2559 : ℝ := (((1 * 10^40
        + 4370931320758359016469200512045207946925) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusLeftP021NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP021NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP021Factor2559 * embedPair2542
      batchN05120MinusP021Center2559‖
      ≤
      (((2 * 10^40
        + 8741862641516715625901217329523851368089) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP021Factor2559, batchN05120MinusP021Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP021Factor2559 * embedPair2542 batchN05120MinusP021Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP021DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP021Factor2559, batchN05120MinusP021Error2559,
      batchC05120MinusLeftP021NormUpper2559]

noncomputable def batchC05120MinusLeftP022NormUpper2559 : ℝ := (((1 * 10^40
        + 5472697472864565626187675505682117104447) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusLeftP022NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP022NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP022Factor2559 * embedPair2542
      batchN05120MinusP022Center2559‖
      ≤
      (((3 * 10^40
        + 945394945729128662304405421174629645779) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP022Factor2559, batchN05120MinusP022Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP022Factor2559 * embedPair2542 batchN05120MinusP022Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP022DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP022Factor2559, batchN05120MinusP022Error2559,
      batchC05120MinusLeftP022NormUpper2559]

noncomputable def batchC05120MinusLeftP023NormUpper2559 : ℝ := (((3 * 10^40
        + 7924017579092765769831930163881857920633) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusLeftP023NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP023NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP023Factor2559 * embedPair2542
      batchN05120MinusP023Center2559‖
      ≤
      (((3 * 10^40
        + 7924017579092762600520012188483613096295) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP023Factor2559, batchN05120MinusP023Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP023Factor2559 * embedPair2542 batchN05120MinusP023Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP023DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP023Factor2559, batchN05120MinusP023Error2559,
      batchC05120MinusLeftP023NormUpper2559]

noncomputable def batchC05120MinusLeftP024NormUpper2559 : ℝ := (((4 * 10^40
        + 1455586131209482950384896348946607415573) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusLeftP024NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP024NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP024Factor2559 * embedPair2542
      batchN05120MinusP024Center2559‖
      ≤
      (((2 * 10^40
        + 727793065604739744078353694585867756753) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP024Factor2559, batchN05120MinusP024Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP024Factor2559 * embedPair2542 batchN05120MinusP024Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP024DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP024Factor2559, batchN05120MinusP024Error2559,
      batchC05120MinusLeftP024NormUpper2559]

noncomputable def batchC05120MinusLeftP025NormUpper2559 : ℝ := (((2 * 10^40
        + 3092632594093438302900660667376441393641) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusLeftP025NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP025NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP025Factor2559 * embedPair2542
      batchN05120MinusP025Center2559‖
      ≤
      (((4 * 10^40
        + 6185265188186872751469891150680355187263) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP025Factor2559, batchN05120MinusP025Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP025Factor2559 * embedPair2542 batchN05120MinusP025Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP025DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP025Factor2559, batchN05120MinusP025Error2559,
      batchC05120MinusLeftP025NormUpper2559]

noncomputable def batchC05120MinusLeftP026NormUpper2559 : ℝ :=
    ((1605550709586375162361285922798536343523
    : ℝ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968))

theorem batchC05120MinusLeftP026NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP026NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP026Factor2559 * embedPair2542
      batchN05120MinusP026Center2559‖
      ≤
      (((5 * 10^40
        + 1377622706764000910984651814113871816487) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP026Factor2559, batchN05120MinusP026Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP026Factor2559 * embedPair2542 batchN05120MinusP026Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP026DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP026Factor2559, batchN05120MinusP026Error2559,
      batchC05120MinusLeftP026NormUpper2559]

noncomputable def batchC05120MinusLeftP027NormUpper2559 : ℝ := (((5 * 10^40
        + 9536139688960099389879593947567147164235) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusLeftP027NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP027NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP027Factor2559 * embedPair2542
      batchN05120MinusP027Center2559‖
      ≤
      (((2 * 10^40
        + 9768069844480047214833070985909271116647) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP027Factor2559, batchN05120MinusP027Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP027Factor2559 * embedPair2542 batchN05120MinusP027Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP027DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP027Factor2559, batchN05120MinusP027Error2559,
      batchC05120MinusLeftP027NormUpper2559]

noncomputable def batchC05120MinusLeftP028NormUpper2559 : ℝ := (((6 * 10^40
        + 2991145119147925448981049603955790711895) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

theorem batchC05120MinusLeftP028NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP028NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP028Factor2559 * embedPair2542
      batchN05120MinusP028Center2559‖
      ≤
      (((6 * 10^40
        + 2991145119147920202770407854368920225367) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP028Factor2559, batchN05120MinusP028Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP028Factor2559 * embedPair2542 batchN05120MinusP028Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP028DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP028Factor2559, batchN05120MinusP028Error2559,
      batchC05120MinusLeftP028NormUpper2559]

noncomputable def batchC05120MinusLeftP029NormUpper2559 : ℝ := (((3 * 10^40
        + 4252042653721445095083650002225973605595) : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

theorem batchC05120MinusLeftP029NormBound2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05120MinusPosition2559‖
        ≤
      batchC05120MinusLeftP029NormUpper2559 := by
  have hc : ‖embedPair2542 batchN05120MinusP029Factor2559 * embedPair2542
      batchN05120MinusP029Center2559‖
      ≤
      (((6 * 10^40
        + 8504085307442884487743765974642712000351) : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, batchN05120MinusP029Factor2559, batchN05120MinusP029Center2559,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05120MinusPosition2559)
    (embedPair2542 batchN05120MinusP029Factor2559 * embedPair2542 batchN05120MinusP029Center2559)
        0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add batchN05120MinusP029DerivativeError2559 hc)).trans
  norm_num [pairMagnitude2542, batchN05120MinusP029Factor2559, batchN05120MinusP029Error2559,
      batchC05120MinusLeftP029NormUpper2559]

noncomputable def batchC05120MinusLeftNormUpper2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05120MinusLeftP000NormUpper2559
  | 1 => batchC05120MinusLeftP001NormUpper2559
  | 2 => batchC05120MinusLeftP002NormUpper2559
  | 3 => batchC05120MinusLeftP003NormUpper2559
  | 4 => batchC05120MinusLeftP004NormUpper2559
  | 5 => batchC05120MinusLeftP005NormUpper2559
  | 6 => batchC05120MinusLeftP006NormUpper2559
  | 7 => batchC05120MinusLeftP007NormUpper2559
  | 8 => batchC05120MinusLeftP008NormUpper2559
  | 9 => batchC05120MinusLeftP009NormUpper2559
  | 10 => batchC05120MinusLeftP010NormUpper2559
  | 11 => batchC05120MinusLeftP011NormUpper2559
  | 12 => batchC05120MinusLeftP012NormUpper2559
  | 13 => batchC05120MinusLeftP013NormUpper2559
  | 14 => batchC05120MinusLeftP014NormUpper2559
  | 15 => batchC05120MinusLeftP015NormUpper2559
  | 16 => batchC05120MinusLeftP016NormUpper2559
  | 17 => batchC05120MinusLeftP017NormUpper2559
  | 18 => batchC05120MinusLeftP018NormUpper2559
  | 19 => batchC05120MinusLeftP019NormUpper2559
  | 20 => batchC05120MinusLeftP020NormUpper2559
  | 21 => batchC05120MinusLeftP021NormUpper2559
  | 22 => batchC05120MinusLeftP022NormUpper2559
  | 23 => batchC05120MinusLeftP023NormUpper2559
  | 24 => batchC05120MinusLeftP024NormUpper2559
  | 25 => batchC05120MinusLeftP025NormUpper2559
  | 26 => batchC05120MinusLeftP026NormUpper2559
  | 27 => batchC05120MinusLeftP027NormUpper2559
  | 28 => batchC05120MinusLeftP028NormUpper2559
  | 29 => batchC05120MinusLeftP029NormUpper2559
  | _ => 0

theorem batchC05120MinusLeftNormBound2559 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 i batchN05120MinusPosition2559‖ ≤
        batchC05120MinusLeftNormUpper2559 i := by
  fin_cases i
  · exact batchC05120MinusLeftP000NormBound2559
  · exact batchC05120MinusLeftP001NormBound2559
  · exact batchC05120MinusLeftP002NormBound2559
  · exact batchC05120MinusLeftP003NormBound2559
  · exact batchC05120MinusLeftP004NormBound2559
  · exact batchC05120MinusLeftP005NormBound2559
  · exact batchC05120MinusLeftP006NormBound2559
  · exact batchC05120MinusLeftP007NormBound2559
  · exact batchC05120MinusLeftP008NormBound2559
  · exact batchC05120MinusLeftP009NormBound2559
  · exact batchC05120MinusLeftP010NormBound2559
  · exact batchC05120MinusLeftP011NormBound2559
  · exact batchC05120MinusLeftP012NormBound2559
  · exact batchC05120MinusLeftP013NormBound2559
  · exact batchC05120MinusLeftP014NormBound2559
  · exact batchC05120MinusLeftP015NormBound2559
  · exact batchC05120MinusLeftP016NormBound2559
  · exact batchC05120MinusLeftP017NormBound2559
  · exact batchC05120MinusLeftP018NormBound2559
  · exact batchC05120MinusLeftP019NormBound2559
  · exact batchC05120MinusLeftP020NormBound2559
  · exact batchC05120MinusLeftP021NormBound2559
  · exact batchC05120MinusLeftP022NormBound2559
  · exact batchC05120MinusLeftP023NormBound2559
  · exact batchC05120MinusLeftP024NormBound2559
  · exact batchC05120MinusLeftP025NormBound2559
  · exact batchC05120MinusLeftP026NormBound2559
  · exact batchC05120MinusLeftP027NormBound2559
  · exact batchC05120MinusLeftP028NormBound2559
  · exact batchC05120MinusLeftP029NormBound2559

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP000NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP001NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP002NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP003NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP004NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP005NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP006NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP007NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP008NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP009NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP010NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP011NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP012NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP013NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP014NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP015NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP016NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP017NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP018NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP019NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP020NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP021NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP022NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP023NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP024NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP025NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP026NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP027NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP028NormBound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusLeftP029NormBound2559
