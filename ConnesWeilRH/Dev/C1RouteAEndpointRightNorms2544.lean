import ConnesWeilRH.Dev.C1RouteAEndpointRightThird2544
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def endpointRightP000NormUpper2544 : ℝ := ((4113863521716742794171 : ℝ) /
        1267650600228229401496703205376)

theorem endpointRightP000NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP000NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP000Factor2544 * embedPair2542
      endpointRightP000Center2544‖ ≤
      ((2056931760858370001719 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP000Factor2544, endpointRightP000Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP000Factor2544 * embedPair2542 endpointRightP000Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP000DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP000Factor2544, endpointRightP000Error2544,
      endpointRightP000NormUpper2544]

noncomputable def endpointRightP001NormUpper2544 : ℝ := ((5704827735629101549705 : ℝ) /
        1267650600228229401496703205376)

theorem endpointRightP001NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP001NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP001Factor2544 * embedPair2542
      endpointRightP001Center2544‖ ≤
      ((5704827735629098078455 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP001Factor2544, endpointRightP001Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP001Factor2544 * embedPair2542 endpointRightP001Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP001DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP001Factor2544, endpointRightP001Error2544,
      endpointRightP001NormUpper2544]

noncomputable def endpointRightP002NormUpper2544 : ℝ := ((844231201983803113969 : ℝ) /
        158456325028528675187087900672)

theorem endpointRightP002NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP002NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP002Factor2544 * embedPair2542
      endpointRightP002Center2544‖ ≤
      ((6753849615870421054705 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP002Factor2544, endpointRightP002Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP002Factor2544 * embedPair2542 endpointRightP002Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP002DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP002Factor2544, endpointRightP002Error2544,
      endpointRightP002NormUpper2544]

noncomputable def endpointRightP003NormUpper2544 : ℝ := ((7421321703954867594991 : ℝ) /
        1267650600228229401496703205376)

theorem endpointRightP003NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP003NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP003Factor2544 * embedPair2542
      endpointRightP003Center2544‖ ≤
      ((7421321703954863514283 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP003Factor2544, endpointRightP003Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP003Factor2544 * embedPair2542 endpointRightP003Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP003DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP003Factor2544, endpointRightP003Error2544,
      endpointRightP003NormUpper2544]

noncomputable def endpointRightP004NormUpper2544 : ℝ := ((245263338557798191377 : ℝ) /
        39614081257132168796771975168)

theorem endpointRightP004NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP004NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP004Factor2544 * embedPair2542
      endpointRightP004Center2544‖ ≤
      ((981053354231192238535 : ℝ) /
        158456325028528675187087900672) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP004Factor2544, endpointRightP004Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP004Factor2544 * embedPair2542 endpointRightP004Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP004DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP004Factor2544, endpointRightP004Error2544,
      endpointRightP004NormUpper2544]

noncomputable def endpointRightP005NormUpper2544 : ℝ := ((422564778158438977 : ℝ) /
        158456325028528675187087900672)

theorem endpointRightP005NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP005NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP005Factor2544 * embedPair2542
      endpointRightP005Center2544‖ ≤
      ((3380518225267511447 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP005Factor2544, endpointRightP005Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP005Factor2544 * embedPair2542 endpointRightP005Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP005DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP005Factor2544, endpointRightP005Error2544,
      endpointRightP005NormUpper2544]

noncomputable def endpointRightP006NormUpper2544 : ℝ := ((1101216836433177397 : ℝ) /
        1267650600228229401496703205376)

theorem endpointRightP006NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP006NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP006Factor2544 * embedPair2542
      endpointRightP006Center2544‖ ≤
      ((1101216836433177285 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP006Factor2544, endpointRightP006Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP006Factor2544 * embedPair2542 endpointRightP006Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP006DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP006Factor2544, endpointRightP006Error2544,
      endpointRightP006NormUpper2544]

noncomputable def endpointRightP007NormUpper2544 : ℝ := ((116836102976617633 : ℝ) /
        633825300114114700748351602688)

theorem endpointRightP007NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP007NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP007Factor2544 * embedPair2542
      endpointRightP007Center2544‖ ≤
      ((233672205953235243 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP007Factor2544, endpointRightP007Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP007Factor2544 * embedPair2542 endpointRightP007Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP007DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP007Factor2544, endpointRightP007Error2544,
      endpointRightP007NormUpper2544]

noncomputable def endpointRightP008NormUpper2544 : ℝ := ((34130796214168130613 : ℝ) /
        158456325028528675187087900672)

theorem endpointRightP008NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP008NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP008Factor2544 * embedPair2542
      endpointRightP008Center2544‖ ≤
      ((17065398107084057595 : ℝ) /
        79228162514264337593543950336) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP008Factor2544, endpointRightP008Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP008Factor2544 * embedPair2542 endpointRightP008Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP008DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP008Factor2544, endpointRightP008Error2544,
      endpointRightP008NormUpper2544]

noncomputable def endpointRightP009NormUpper2544 : ℝ := ((840017816946058558515 : ℝ) /
        1267650600228229401496703205376)

theorem endpointRightP009NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP009NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP009Factor2544 * embedPair2542
      endpointRightP009Center2544‖ ≤
      ((840017816946058030915 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP009Factor2544, endpointRightP009Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP009Factor2544 * embedPair2542 endpointRightP009Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP009DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP009Factor2544, endpointRightP009Error2544,
      endpointRightP009NormUpper2544]

noncomputable def endpointRightP010NormUpper2544 : ℝ := ((1390526306986826070301 : ℝ) /
        1267650600228229401496703205376)

theorem endpointRightP010NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP010NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP010Factor2544 * embedPair2542
      endpointRightP010Center2544‖ ≤
      ((1390526306986825227029 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP010Factor2544, endpointRightP010Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP010Factor2544 * embedPair2542 endpointRightP010Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP010DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP010Factor2544, endpointRightP010Error2544,
      endpointRightP010NormUpper2544]

noncomputable def endpointRightP011NormUpper2544 : ℝ := ((1868480975042027865479 : ℝ) /
        1267650600228229401496703205376)

theorem endpointRightP011NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP011NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP011Factor2544 * embedPair2542
      endpointRightP011Center2544‖ ≤
      ((934240487521013426225 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP011Factor2544, endpointRightP011Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP011Factor2544 * embedPair2542 endpointRightP011Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP011DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP011Factor2544, endpointRightP011Error2544,
      endpointRightP011NormUpper2544]

noncomputable def endpointRightP012NormUpper2544 : ℝ := ((1234508165646664695773 : ℝ) /
        633825300114114700748351602688)

theorem endpointRightP012NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP012NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP012Factor2544 * embedPair2542
      endpointRightP012Center2544‖ ≤
      ((154313520705833039503 : ℝ) /
        79228162514264337593543950336) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP012Factor2544, endpointRightP012Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP012Factor2544 * embedPair2542 endpointRightP012Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP012DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP012Factor2544, endpointRightP012Error2544,
      endpointRightP012NormUpper2544]

noncomputable def endpointRightP013NormUpper2544 : ℝ := ((1559336583264426869991 : ℝ) /
        633825300114114700748351602688)

theorem endpointRightP013NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP013NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP013Factor2544 * embedPair2542
      endpointRightP013Center2544‖ ≤
      ((389834145816106517043 : ℝ) /
        158456325028528675187087900672) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP013Factor2544, endpointRightP013Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP013Factor2544 * embedPair2542 endpointRightP013Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP013DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP013Factor2544, endpointRightP013Error2544,
      endpointRightP013NormUpper2544]

noncomputable def endpointRightP014NormUpper2544 : ℝ := ((4608619165064966898087 : ℝ) /
        1267650600228229401496703205376)

theorem endpointRightP014NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP014NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP014Factor2544 * embedPair2542
      endpointRightP014Center2544‖ ≤
      ((4608619165064964233683 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP014Factor2544, endpointRightP014Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP014Factor2544 * embedPair2542 endpointRightP014Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP014DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP014Factor2544, endpointRightP014Error2544,
      endpointRightP014NormUpper2544]

noncomputable def endpointRightP015NormUpper2544 : ℝ := ((5928548520421192642365 : ℝ) /
        1267650600228229401496703205376)

theorem endpointRightP015NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP015NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP015Factor2544 * embedPair2542
      endpointRightP015Center2544‖ ≤
      ((185267141263162137487 : ℝ) /
        39614081257132168796771975168) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP015Factor2544, endpointRightP015Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP015Factor2544 * embedPair2542 endpointRightP015Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP015DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP015Factor2544, endpointRightP015Error2544,
      endpointRightP015NormUpper2544]

noncomputable def endpointRightP016NormUpper2544 : ℝ := ((3512907745564486901053 : ℝ) /
        633825300114114700748351602688)

theorem endpointRightP016NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP016NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP016Factor2544 * embedPair2542
      endpointRightP016Center2544‖ ≤
      ((7025815491128969222487 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP016Factor2544, endpointRightP016Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP016Factor2544 * embedPair2542 endpointRightP016Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP016DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP016Factor2544, endpointRightP016Error2544,
      endpointRightP016NormUpper2544]

noncomputable def endpointRightP017NormUpper2544 : ℝ := ((9530379777238546152695 : ℝ) /
        1267650600228229401496703205376)

theorem endpointRightP017NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP017NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP017Factor2544 * embedPair2542
      endpointRightP017Center2544‖ ≤
      ((4765189888619270206891 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP017Factor2544, endpointRightP017Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP017Factor2544 * embedPair2542 endpointRightP017Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP017DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP017Factor2544, endpointRightP017Error2544,
      endpointRightP017NormUpper2544]

noncomputable def endpointRightP018NormUpper2544 : ℝ := ((5307128363946421900303 : ℝ) /
        633825300114114700748351602688)

theorem endpointRightP018NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP018NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP018Factor2544 * embedPair2542
      endpointRightP018Center2544‖ ≤
      ((5307128363946418300991 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP018Factor2544, endpointRightP018Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP018Factor2544 * embedPair2542 endpointRightP018Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP018DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP018Factor2544, endpointRightP018Error2544,
      endpointRightP018NormUpper2544]

noncomputable def endpointRightP019NormUpper2544 : ℝ := ((6388388086331686826177 : ℝ) /
        633825300114114700748351602688)

theorem endpointRightP019NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP019NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP019Factor2544 * embedPair2542
      endpointRightP019Center2544‖ ≤
      ((3194194043165841720285 : ℝ) /
        316912650057057350374175801344) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP019Factor2544, endpointRightP019Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP019Factor2544 * embedPair2542 endpointRightP019Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP019DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP019Factor2544, endpointRightP019Error2544,
      endpointRightP019NormUpper2544]

noncomputable def endpointRightP020NormUpper2544 : ℝ := ((15442619470098840691881 : ℝ) /
        1267650600228229401496703205376)

theorem endpointRightP020NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP020NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP020Factor2544 * embedPair2542
      endpointRightP020Center2544‖ ≤
      ((15442619470098832184483 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP020Factor2544, endpointRightP020Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP020Factor2544 * embedPair2542 endpointRightP020Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP020DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP020Factor2544, endpointRightP020Error2544,
      endpointRightP020NormUpper2544]

noncomputable def endpointRightP021NormUpper2544 : ℝ := ((4483274163926884120673 : ℝ) /
        316912650057057350374175801344)

theorem endpointRightP021NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP021NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP021Factor2544 * embedPair2542
      endpointRightP021Center2544‖ ≤
      ((4483274163926882393131 : ℝ) /
        316912650057057350374175801344) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP021Factor2544, endpointRightP021Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP021Factor2544 * embedPair2542 endpointRightP021Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP021DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP021Factor2544, endpointRightP021Error2544,
      endpointRightP021NormUpper2544]

noncomputable def endpointRightP022NormUpper2544 : ℝ := ((2413213852317360977895 : ℝ) /
        158456325028528675187087900672)

theorem endpointRightP022NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP022NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP022Factor2544 * embedPair2542
      endpointRightP022Center2544‖ ≤
      ((301651731539670043169 : ℝ) /
        19807040628566084398385987584) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP022Factor2544, endpointRightP022Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP022Factor2544 * embedPair2542 endpointRightP022Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP022DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP022Factor2544, endpointRightP022Error2544,
      endpointRightP022NormUpper2544]

noncomputable def endpointRightP023NormUpper2544 : ℝ := ((2956560878630224590455 : ℝ) /
        158456325028528675187087900672)

theorem endpointRightP023NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP023NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP023Factor2544 * embedPair2542
      endpointRightP023Center2544‖ ≤
      ((5913121757260446049895 : ℝ) /
        316912650057057350374175801344) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP023Factor2544, endpointRightP023Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP023Factor2544 * embedPair2542 endpointRightP023Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP023DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP023Factor2544, endpointRightP023Error2544,
      endpointRightP023NormUpper2544]

noncomputable def endpointRightP024NormUpper2544 : ℝ := ((25852047154786707027311 : ℝ) /
        1267650600228229401496703205376)

theorem endpointRightP024NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP024NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP024Factor2544 * embedPair2542
      endpointRightP024Center2544‖ ≤
      ((12926023577393346247173 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP024Factor2544, endpointRightP024Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP024Factor2544 * embedPair2542 endpointRightP024Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP024DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP024Factor2544, endpointRightP024Error2544,
      endpointRightP024NormUpper2544]

noncomputable def endpointRightP025NormUpper2544 : ℝ := ((28797698633558731510911 : ℝ) /
        1267650600228229401496703205376)

theorem endpointRightP025NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP025NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP025Factor2544 * embedPair2542
      endpointRightP025Center2544‖ ≤
      ((14398849316779357728697 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP025Factor2544, endpointRightP025Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP025Factor2544 * embedPair2542 endpointRightP025Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP025DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP025Factor2544, endpointRightP025Error2544,
      endpointRightP025NormUpper2544]

noncomputable def endpointRightP026NormUpper2544 : ℝ := ((16015683644071129733027 : ℝ) /
        633825300114114700748351602688)

theorem endpointRightP026NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP026NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP026Factor2544 * embedPair2542
      endpointRightP026Center2544‖ ≤
      ((16015683644071118580963 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP026Factor2544, endpointRightP026Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP026Factor2544 * embedPair2542 endpointRightP026Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP026DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP026Factor2544, endpointRightP026Error2544,
      endpointRightP026NormUpper2544]

noncomputable def endpointRightP027NormUpper2544 : ℝ := ((18556021861513245586999 : ℝ) /
        633825300114114700748351602688)

theorem endpointRightP027NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP027NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP027Factor2544 * embedPair2542
      endpointRightP027Center2544‖ ≤
      ((9278010930756618202131 : ℝ) /
        316912650057057350374175801344) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP027Factor2544, endpointRightP027Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP027Factor2544 * embedPair2542 endpointRightP027Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP027DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP027Factor2544, endpointRightP027Error2544,
      endpointRightP027NormUpper2544]

noncomputable def endpointRightP028NormUpper2544 : ℝ := ((4907944576832379542521 : ℝ) /
        158456325028528675187087900672)

theorem endpointRightP028NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP028NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP028Factor2544 * embedPair2542
      endpointRightP028Center2544‖ ≤
      ((19631778307329508489851 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP028Factor2544, endpointRightP028Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP028Factor2544 * embedPair2542 endpointRightP028Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP028DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP028Factor2544, endpointRightP028Error2544,
      endpointRightP028NormUpper2544]

noncomputable def endpointRightP029NormUpper2544 : ℝ := ((42696515139734162924493 : ℝ) /
        1267650600228229401496703205376)

theorem endpointRightP029NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ endpointRightPosition2544‖ ≤
      endpointRightP029NormUpper2544 := by
  have hc : ‖embedPair2542 endpointRightP029Factor2544 * embedPair2542
      endpointRightP029Center2544‖ ≤
      ((21348257569867066511953 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointRightP029Factor2544, endpointRightP029Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ endpointRightPosition2544)
    (embedPair2542 endpointRightP029Factor2544 * embedPair2542 endpointRightP029Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointRightP029DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointRightP029Factor2544, endpointRightP029Error2544,
      endpointRightP029NormUpper2544]

noncomputable def endpointRightNormUpper2544 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => endpointRightP000NormUpper2544
  | 1 => endpointRightP001NormUpper2544
  | 2 => endpointRightP002NormUpper2544
  | 3 => endpointRightP003NormUpper2544
  | 4 => endpointRightP004NormUpper2544
  | 5 => endpointRightP005NormUpper2544
  | 6 => endpointRightP006NormUpper2544
  | 7 => endpointRightP007NormUpper2544
  | 8 => endpointRightP008NormUpper2544
  | 9 => endpointRightP009NormUpper2544
  | 10 => endpointRightP010NormUpper2544
  | 11 => endpointRightP011NormUpper2544
  | 12 => endpointRightP012NormUpper2544
  | 13 => endpointRightP013NormUpper2544
  | 14 => endpointRightP014NormUpper2544
  | 15 => endpointRightP015NormUpper2544
  | 16 => endpointRightP016NormUpper2544
  | 17 => endpointRightP017NormUpper2544
  | 18 => endpointRightP018NormUpper2544
  | 19 => endpointRightP019NormUpper2544
  | 20 => endpointRightP020NormUpper2544
  | 21 => endpointRightP021NormUpper2544
  | 22 => endpointRightP022NormUpper2544
  | 23 => endpointRightP023NormUpper2544
  | 24 => endpointRightP024NormUpper2544
  | 25 => endpointRightP025NormUpper2544
  | 26 => endpointRightP026NormUpper2544
  | 27 => endpointRightP027NormUpper2544
  | 28 => endpointRightP028NormUpper2544
  | 29 => endpointRightP029NormUpper2544
  | _ => 0

theorem endpointRightNormBound2544 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 i endpointRightPosition2544‖ ≤
        endpointRightNormUpper2544 i := by
  fin_cases i
  · exact endpointRightP000NormBound2544
  · exact endpointRightP001NormBound2544
  · exact endpointRightP002NormBound2544
  · exact endpointRightP003NormBound2544
  · exact endpointRightP004NormBound2544
  · exact endpointRightP005NormBound2544
  · exact endpointRightP006NormBound2544
  · exact endpointRightP007NormBound2544
  · exact endpointRightP008NormBound2544
  · exact endpointRightP009NormBound2544
  · exact endpointRightP010NormBound2544
  · exact endpointRightP011NormBound2544
  · exact endpointRightP012NormBound2544
  · exact endpointRightP013NormBound2544
  · exact endpointRightP014NormBound2544
  · exact endpointRightP015NormBound2544
  · exact endpointRightP016NormBound2544
  · exact endpointRightP017NormBound2544
  · exact endpointRightP018NormBound2544
  · exact endpointRightP019NormBound2544
  · exact endpointRightP020NormBound2544
  · exact endpointRightP021NormBound2544
  · exact endpointRightP022NormBound2544
  · exact endpointRightP023NormBound2544
  · exact endpointRightP024NormBound2544
  · exact endpointRightP025NormBound2544
  · exact endpointRightP026NormBound2544
  · exact endpointRightP027NormBound2544
  · exact endpointRightP028NormBound2544
  · exact endpointRightP029NormBound2544

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.endpointRightP000NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP001NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP002NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP003NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP004NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP005NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP006NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP007NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP008NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP009NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP010NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP011NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP012NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP013NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP014NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP015NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP016NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP017NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP018NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP019NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP020NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP021NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP022NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP023NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP024NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP025NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP026NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP027NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP028NormBound2544
#print axioms ConnesWeilRH.Dev.endpointRightP029NormBound2544
