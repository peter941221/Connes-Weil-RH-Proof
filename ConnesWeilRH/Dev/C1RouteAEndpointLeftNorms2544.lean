import ConnesWeilRH.Dev.C1RouteAEndpointLeftThird2544
import ConnesWeilRH.Dev.C1RouteASignedMidpoint2543

namespace ConnesWeilRH.Dev

noncomputable def endpointLeftP000NormUpper2544 : ℝ := ((2065833370434491572249 : ℝ) /
        633825300114114700748351602688)

theorem endpointLeftP000NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP000NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP000Factor2544 * embedPair2542 endpointLeftP000Center2544‖
      ≤
      ((4131666740868980391329 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP000Factor2544, endpointLeftP000Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP000Factor2544 * embedPair2542 endpointLeftP000Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP000DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP000Factor2544, endpointLeftP000Error2544,
      endpointLeftP000NormUpper2544]

noncomputable def endpointLeftP001NormUpper2544 : ℝ := ((5717172292937478988647 : ℝ) /
        1267650600228229401496703205376)

theorem endpointLeftP001NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP001NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP001Factor2544 * embedPair2542 endpointLeftP001Center2544‖
      ≤
      ((5717172292937475571223 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP001Factor2544, endpointLeftP001Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP001Factor2544 * embedPair2542 endpointLeftP001Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP001DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP001Factor2544, endpointLeftP001Error2544,
      endpointLeftP001NormUpper2544]

noncomputable def endpointLeftP002NormUpper2544 : ℝ := ((6761044751798138118163 : ℝ) /
        1267650600228229401496703205376)

theorem endpointLeftP002NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP002NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP002Factor2544 * embedPair2542 endpointLeftP002Center2544‖
      ≤
      ((6761044751798134324729 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP002Factor2544, endpointLeftP002Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP002Factor2544 * embedPair2542 endpointLeftP002Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP002DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP002Factor2544, endpointLeftP002Error2544,
      endpointLeftP002NormUpper2544]

noncomputable def endpointLeftP003NormUpper2544 : ℝ := ((1856179413256026369455 : ℝ) /
        316912650057057350374175801344)

theorem endpointLeftP003NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP003NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP003Factor2544 * embedPair2542 endpointLeftP003Center2544‖
      ≤
      ((1856179413256025366643 : ℝ) /
        316912650057057350374175801344) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP003Factor2544, endpointLeftP003Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP003Factor2544 * embedPair2542 endpointLeftP003Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP003DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP003Factor2544, endpointLeftP003Error2544,
      endpointLeftP003NormUpper2544]

noncomputable def endpointLeftP004NormUpper2544 : ℝ := ((490575079112982560397 : ℝ) /
        79228162514264337593543950336)

theorem endpointLeftP004NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP004NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP004Factor2544 * embedPair2542 endpointLeftP004Center2544‖
      ≤
      ((3924600632903858411809 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP004Factor2544, endpointLeftP004Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP004Factor2544 * embedPair2542 endpointLeftP004Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP004DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP004Factor2544, endpointLeftP004Error2544,
      endpointLeftP004NormUpper2544]

noncomputable def endpointLeftP005NormUpper2544 : ℝ := ((3386899444661166559 : ℝ) /
        1267650600228229401496703205376)

theorem endpointLeftP005NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP005NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP005Factor2544 * embedPair2542 endpointLeftP005Center2544‖
      ≤
      ((3386899444661166189 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP005Factor2544, endpointLeftP005Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP005Factor2544 * embedPair2542 endpointLeftP005Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP005DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP005Factor2544, endpointLeftP005Error2544,
      endpointLeftP005NormUpper2544]

noncomputable def endpointLeftP006NormUpper2544 : ℝ := ((1098020602433943489 : ℝ) /
        1267650600228229401496703205376)

theorem endpointLeftP006NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP006NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP006Factor2544 * embedPair2542 endpointLeftP006Center2544‖
      ≤
      ((549010301216971689 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP006Factor2544, endpointLeftP006Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP006Factor2544 * embedPair2542 endpointLeftP006Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP006DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP006Factor2544, endpointLeftP006Error2544,
      endpointLeftP006NormUpper2544]

noncomputable def endpointLeftP007NormUpper2544 : ℝ := ((115918311926994923 : ℝ) /
        633825300114114700748351602688)

theorem endpointLeftP007NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP007NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP007Factor2544 * embedPair2542 endpointLeftP007Center2544‖
      ≤
      ((231836623853989823 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP007Factor2544, endpointLeftP007Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP007Factor2544 * embedPair2542 endpointLeftP007Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP007DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP007Factor2544, endpointLeftP007Error2544,
      endpointLeftP007NormUpper2544]

noncomputable def endpointLeftP008NormUpper2544 : ℝ := ((273722680239265563769 : ℝ) /
        1267650600228229401496703205376)

theorem endpointLeftP008NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP008NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP008Factor2544 * embedPair2542 endpointLeftP008Center2544‖
      ≤
      ((136861340119632719647 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP008Factor2544, endpointLeftP008Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP008Factor2544 * embedPair2542 endpointLeftP008Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP008DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP008Factor2544, endpointLeftP008Error2544,
      endpointLeftP008NormUpper2544]

noncomputable def endpointLeftP009NormUpper2544 : ℝ := ((842218696465135735413 : ℝ) /
        1267650600228229401496703205376)

theorem endpointLeftP009NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP009NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP009Factor2544 * embedPair2542 endpointLeftP009Center2544‖
      ≤
      ((842218696465135204901 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP009Factor2544, endpointLeftP009Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP009Factor2544 * embedPair2542 endpointLeftP009Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP009DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP009Factor2544, endpointLeftP009Error2544,
      endpointLeftP009NormUpper2544]

noncomputable def endpointLeftP010NormUpper2544 : ℝ := ((348556216761228325847 : ℝ) /
        316912650057057350374175801344)

theorem endpointLeftP010NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP010NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP010Factor2544 * embedPair2542 endpointLeftP010Center2544‖
      ≤
      ((1394224867044912461303 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP010Factor2544, endpointLeftP010Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP010Factor2544 * embedPair2542 endpointLeftP010Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP010DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP010Factor2544, endpointLeftP010Error2544,
      endpointLeftP010NormUpper2544]

noncomputable def endpointLeftP011NormUpper2544 : ℝ := ((468371232693019059305 : ℝ) /
        316912650057057350374175801344)

theorem endpointLeftP011NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP011NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP011Factor2544 * embedPair2542 endpointLeftP011Center2544‖
      ≤
      ((1873484930772075212583 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP011Factor2544, endpointLeftP011Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP011Factor2544 * embedPair2542 endpointLeftP011Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP011DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP011Factor2544, endpointLeftP011Error2544,
      endpointLeftP011NormUpper2544]

noncomputable def endpointLeftP012NormUpper2544 : ℝ := ((618916043340379273307 : ℝ) /
        316912650057057350374175801344)

theorem endpointLeftP012NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP012NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP012Factor2544 * embedPair2542 endpointLeftP012Center2544‖
      ≤
      ((2475664173361516310497 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP012Factor2544, endpointLeftP012Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP012Factor2544 * embedPair2542 endpointLeftP012Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP012DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP012Factor2544, endpointLeftP012Error2544,
      endpointLeftP012NormUpper2544]

noncomputable def endpointLeftP013NormUpper2544 : ℝ := ((3127102301126778275749 : ℝ) /
        1267650600228229401496703205376)

theorem endpointLeftP013NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP013NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP013Factor2544 * embedPair2542 endpointLeftP013Center2544‖
      ≤
      ((3127102301126776696357 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP013Factor2544, endpointLeftP013Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP013Factor2544 * embedPair2542 endpointLeftP013Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP013DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP013Factor2544, endpointLeftP013Error2544,
      endpointLeftP013NormUpper2544]

noncomputable def endpointLeftP014NormUpper2544 : ℝ := ((2310570235804931714725 : ℝ) /
        633825300114114700748351602688)

theorem endpointLeftP014NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP014NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP014Factor2544 * embedPair2542 endpointLeftP014Center2544‖
      ≤
      ((4621140471609860723833 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP014Factor2544, endpointLeftP014Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP014Factor2544 * embedPair2542 endpointLeftP014Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP014DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP014Factor2544, endpointLeftP014Error2544,
      endpointLeftP014NormUpper2544]

noncomputable def endpointLeftP015NormUpper2544 : ℝ := ((2972349966535466347807 : ℝ) /
        633825300114114700748351602688)

theorem endpointLeftP015NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP015NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP015Factor2544 * embedPair2542 endpointLeftP015Center2544‖
      ≤
      ((371543745816933028945 : ℝ) /
        79228162514264337593543950336) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP015Factor2544, endpointLeftP015Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP015Factor2544 * embedPair2542 endpointLeftP015Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP015DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP015Factor2544, endpointLeftP015Error2544,
      endpointLeftP015NormUpper2544]

noncomputable def endpointLeftP016NormUpper2544 : ℝ := ((3522493437983070853899 : ℝ) /
        633825300114114700748351602688)

theorem endpointLeftP016NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP016NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP016Factor2544 * embedPair2542 endpointLeftP016Center2544‖
      ≤
      ((1761246718991534263833 : ℝ) /
        316912650057057350374175801344) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP016Factor2544, endpointLeftP016Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP016Factor2544 * embedPair2542 endpointLeftP016Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP016DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP016Factor2544, endpointLeftP016Error2544,
      endpointLeftP016NormUpper2544]

noncomputable def endpointLeftP017NormUpper2544 : ℝ := ((4778224721675905150063 : ℝ) /
        633825300114114700748351602688)

theorem endpointLeftP017NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP017NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP017Factor2544 * embedPair2542 endpointLeftP017Center2544‖
      ≤
      ((4778224721675902328353 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP017Factor2544, endpointLeftP017Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP017Factor2544 * embedPair2542 endpointLeftP017Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP017DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP017Factor2544, endpointLeftP017Error2544,
      endpointLeftP017NormUpper2544]

noncomputable def endpointLeftP018NormUpper2544 : ℝ := ((5321656636517043017359 : ℝ) /
        633825300114114700748351602688)

theorem endpointLeftP018NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP018NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP018Factor2544 * embedPair2542 endpointLeftP018Center2544‖
      ≤
      ((2660828318258519711517 : ℝ) /
        316912650057057350374175801344) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP018Factor2544, endpointLeftP018Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP018Factor2544 * embedPair2542 endpointLeftP018Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP018DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP018Factor2544, endpointLeftP018Error2544,
      endpointLeftP018NormUpper2544]

noncomputable def endpointLeftP019NormUpper2544 : ℝ := ((6405897046167657553939 : ℝ) /
        633825300114114700748351602688)

theorem endpointLeftP019NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP019NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP019Factor2544 * embedPair2542 endpointLeftP019Center2544‖
      ≤
      ((12811794092335308124583 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP019Factor2544, endpointLeftP019Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP019Factor2544 * embedPair2542 endpointLeftP019Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP019DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP019Factor2544, endpointLeftP019Error2544,
      endpointLeftP019NormUpper2544]

noncomputable def endpointLeftP020NormUpper2544 : ℝ := ((7742494558375209169551 : ℝ) /
        633825300114114700748351602688)

theorem endpointLeftP020NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP020NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP020Factor2544 * embedPair2542 endpointLeftP020Center2544‖
      ≤
      ((15484989116750409762033 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP020Factor2544, endpointLeftP020Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP020Factor2544 * embedPair2542 endpointLeftP020Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP020DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP020Factor2544, endpointLeftP020Error2544,
      endpointLeftP020NormUpper2544]

noncomputable def endpointLeftP021NormUpper2544 : ℝ := ((1123896033507895871133 : ℝ) /
        79228162514264337593543950336)

theorem endpointLeftP021NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP021NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP021Factor2544 * embedPair2542 endpointLeftP021Center2544‖
      ≤
      ((8991168268063163374927 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP021Factor2544, endpointLeftP021Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP021Factor2544 * embedPair2542 endpointLeftP021Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP021DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP021Factor2544, endpointLeftP021Error2544,
      endpointLeftP021NormUpper2544]

noncomputable def endpointLeftP022NormUpper2544 : ℝ := ((4839684473031755515311 : ℝ) /
        316912650057057350374175801344)

theorem endpointLeftP022NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP022NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP022Factor2544 * embedPair2542 endpointLeftP022Center2544‖
      ≤
      ((9679368946063508344205 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP022Factor2544, endpointLeftP022Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP022Factor2544 * embedPair2542 endpointLeftP022Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP022DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP022Factor2544, endpointLeftP022Error2544,
      endpointLeftP022NormUpper2544]

noncomputable def endpointLeftP023NormUpper2544 : ℝ := ((23717509910202823175559 : ℝ) /
        1267650600228229401496703205376)

theorem endpointLeftP023NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP023NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP023Factor2544 * embedPair2542 endpointLeftP023Center2544‖
      ≤
      ((23717509910202810859953 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP023Factor2544, endpointLeftP023Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP023Factor2544 * embedPair2542 endpointLeftP023Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP023DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP023Factor2544, endpointLeftP023Error2544,
      endpointLeftP023NormUpper2544]

noncomputable def endpointLeftP024NormUpper2544 : ℝ := ((25923141382046147180049 : ℝ) /
        1267650600228229401496703205376)

theorem endpointLeftP024NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP024NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP024Factor2544 * embedPair2542 endpointLeftP024Center2544‖
      ≤
      ((12961570691023066275857 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP024Factor2544, endpointLeftP024Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP024Factor2544 * embedPair2542 endpointLeftP024Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP024DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP024Factor2544, endpointLeftP024Error2544,
      endpointLeftP024NormUpper2544]

noncomputable def endpointLeftP025NormUpper2544 : ℝ := ((28876924634721237791815 : ℝ) /
        1267650600228229401496703205376)

theorem endpointLeftP025NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP025NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP025Factor2544 * embedPair2542 endpointLeftP025Center2544‖
      ≤
      ((14438462317360611158667 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP025Factor2544, endpointLeftP025Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP025Factor2544 * embedPair2542 endpointLeftP025Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP025DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP025Factor2544, endpointLeftP025Error2544,
      endpointLeftP025NormUpper2544]

noncomputable def endpointLeftP026NormUpper2544 : ℝ := ((16059760652797232620125 : ℝ) /
        633825300114114700748351602688)

theorem endpointLeftP026NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP026NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP026Factor2544 * embedPair2542 endpointLeftP026Center2544‖
      ≤
      ((32119521305594442988135 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP026Factor2544, endpointLeftP026Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP026Factor2544 * embedPair2542 endpointLeftP026Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP026DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP026Factor2544, endpointLeftP026Error2544,
      endpointLeftP026NormUpper2544]

noncomputable def endpointLeftP027NormUpper2544 : ℝ := ((18607113617011665717449 : ℝ) /
        633825300114114700748351602688)

theorem endpointLeftP027NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP027NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP027Factor2544 * embedPair2542 endpointLeftP027Center2544‖
      ≤
      ((37214227234023312119421 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP027Factor2544, endpointLeftP027Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP027Factor2544 * embedPair2542 endpointLeftP027Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP027DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP027Factor2544, endpointLeftP027Error2544,
      endpointLeftP027NormUpper2544]

noncomputable def endpointLeftP028NormUpper2544 : ℝ := ((19685840901610819784783 : ℝ) /
        633825300114114700748351602688)

theorem endpointLeftP028NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP028NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP028Factor2544 * embedPair2542 endpointLeftP028Center2544‖
      ≤
      ((19685840901610810644289 : ℝ) /
        633825300114114700748351602688) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP028Factor2544, endpointLeftP028Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP028Factor2544 * embedPair2542 endpointLeftP028Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP028DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP028Factor2544, endpointLeftP028Error2544,
      endpointLeftP028NormUpper2544]

noncomputable def endpointLeftP029NormUpper2544 : ℝ := ((2675882595236650876393 : ℝ) /
        79228162514264337593543950336)

theorem endpointLeftP029NormBound2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ endpointLeftPosition2544‖ ≤
      endpointLeftP029NormUpper2544 := by
  have hc : ‖embedPair2542 endpointLeftP029Factor2544 * embedPair2542 endpointLeftP029Center2544‖
      ≤
      ((42814121523786384773999 : ℝ) /
        1267650600228229401496703205376) := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num)
    norm_num [embedPair2542, endpointLeftP029Factor2544, endpointLeftP029Center2544,
        Complex.mul_re, Complex.mul_im]
  have h := midpoint_triangle2543
    (weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ endpointLeftPosition2544)
    (embedPair2542 endpointLeftP029Factor2544 * embedPair2542 endpointLeftP029Center2544) 0
  simp only [sub_zero] at h
  apply (h.trans (add_le_add endpointLeftP029DerivativeError2544 hc)).trans
  norm_num [pairMagnitude2542, endpointLeftP029Factor2544, endpointLeftP029Error2544,
      endpointLeftP029NormUpper2544]

noncomputable def endpointLeftNormUpper2544 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => endpointLeftP000NormUpper2544
  | 1 => endpointLeftP001NormUpper2544
  | 2 => endpointLeftP002NormUpper2544
  | 3 => endpointLeftP003NormUpper2544
  | 4 => endpointLeftP004NormUpper2544
  | 5 => endpointLeftP005NormUpper2544
  | 6 => endpointLeftP006NormUpper2544
  | 7 => endpointLeftP007NormUpper2544
  | 8 => endpointLeftP008NormUpper2544
  | 9 => endpointLeftP009NormUpper2544
  | 10 => endpointLeftP010NormUpper2544
  | 11 => endpointLeftP011NormUpper2544
  | 12 => endpointLeftP012NormUpper2544
  | 13 => endpointLeftP013NormUpper2544
  | 14 => endpointLeftP014NormUpper2544
  | 15 => endpointLeftP015NormUpper2544
  | 16 => endpointLeftP016NormUpper2544
  | 17 => endpointLeftP017NormUpper2544
  | 18 => endpointLeftP018NormUpper2544
  | 19 => endpointLeftP019NormUpper2544
  | 20 => endpointLeftP020NormUpper2544
  | 21 => endpointLeftP021NormUpper2544
  | 22 => endpointLeftP022NormUpper2544
  | 23 => endpointLeftP023NormUpper2544
  | 24 => endpointLeftP024NormUpper2544
  | 25 => endpointLeftP025NormUpper2544
  | 26 => endpointLeftP026NormUpper2544
  | 27 => endpointLeftP027NormUpper2544
  | 28 => endpointLeftP028NormUpper2544
  | 29 => endpointLeftP029NormUpper2544
  | _ => 0

theorem endpointLeftNormBound2544 (i : Fin 30) :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 i endpointLeftPosition2544‖ ≤
        endpointLeftNormUpper2544 i := by
  fin_cases i
  · exact endpointLeftP000NormBound2544
  · exact endpointLeftP001NormBound2544
  · exact endpointLeftP002NormBound2544
  · exact endpointLeftP003NormBound2544
  · exact endpointLeftP004NormBound2544
  · exact endpointLeftP005NormBound2544
  · exact endpointLeftP006NormBound2544
  · exact endpointLeftP007NormBound2544
  · exact endpointLeftP008NormBound2544
  · exact endpointLeftP009NormBound2544
  · exact endpointLeftP010NormBound2544
  · exact endpointLeftP011NormBound2544
  · exact endpointLeftP012NormBound2544
  · exact endpointLeftP013NormBound2544
  · exact endpointLeftP014NormBound2544
  · exact endpointLeftP015NormBound2544
  · exact endpointLeftP016NormBound2544
  · exact endpointLeftP017NormBound2544
  · exact endpointLeftP018NormBound2544
  · exact endpointLeftP019NormBound2544
  · exact endpointLeftP020NormBound2544
  · exact endpointLeftP021NormBound2544
  · exact endpointLeftP022NormBound2544
  · exact endpointLeftP023NormBound2544
  · exact endpointLeftP024NormBound2544
  · exact endpointLeftP025NormBound2544
  · exact endpointLeftP026NormBound2544
  · exact endpointLeftP027NormBound2544
  · exact endpointLeftP028NormBound2544
  · exact endpointLeftP029NormBound2544

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.endpointLeftP000NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP001NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP002NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP003NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP004NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP005NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP006NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP007NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP008NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP009NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP010NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP011NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP012NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP013NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP014NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP015NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP016NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP017NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP018NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP019NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP020NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP021NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP022NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP023NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP024NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP025NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP026NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP027NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP028NormBound2544
#print axioms ConnesWeilRH.Dev.endpointLeftP029NormBound2544
