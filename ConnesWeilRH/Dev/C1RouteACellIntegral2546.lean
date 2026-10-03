import ConnesWeilRH.Dev.C1RouteAFourthEnvelope2545
import ConnesWeilRH.Dev.C1RouteACellRight2546
import ConnesWeilRH.Dev.C1RouteAAdaptiveN05440Plus2542

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def cellP000Charge2546 : ℝ := ((556615799121 : ℝ) /
        500000)

theorem cellP000ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ + baseCoefficientError2540 ⟨0, by omega⟩) *
      thirdCellTerm2544 ⟨0, by omega⟩ ≤ cellP000Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ +
      baseCoefficientError2540 ⟨0, by omega⟩ ≤ ((((93120694313847428463570198751886005510 * 10^40
        + 3774433853198394427148785817215910416785) * 10^40
        + 1645017025942782892863787309175515900791) : ℝ) /
        ((282695530364541492733327 * 10^40
        + 6001188669625323974235000990332994569922) * 10^40
        + 681916416000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨0, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨0, by omega⟩ ≤ ((109672512588375968214943740577103 : ℝ) /
        (3 * 10^40
        + 2451855365842672678315602057625600000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP000Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP000NormUpper2544, endpointRightP000NormUpper2544,
      fourthP000Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ +
      baseCoefficientError2540 ⟨0, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP000Charge2546]

noncomputable def cellP001Charge2546 : ℝ := ((173651956181 : ℝ) /
        1000000)

theorem cellP001ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ + baseCoefficientError2540 ⟨1, by omega⟩) *
      thirdCellTerm2544 ⟨1, by omega⟩ ≤ cellP001Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ +
      baseCoefficientError2540 ⟨1, by omega⟩ ≤ ((((42210570462884611076708942589714590689 * 10^40
        + 47776653908777250556582803978568596720) * 10^40
        + 3912517239119829739516822877906897587539) : ℝ) /
        ((1130782121458165970933310 * 10^40
        + 4004754678501295896940003961331978279688) * 10^40
        + 2727665664000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨1, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨1, by omega⟩ ≤ ((4717663334051440948997159087921 : ℝ) /
        1014120480182583521197362564300800000000) := by
    unfold thirdCellTerm2544
    have h := fourthP001Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP001NormUpper2544, endpointRightP001NormUpper2544,
      fourthP001Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ +
      baseCoefficientError2540 ⟨1, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP001Charge2546]

noncomputable def cellP002Charge2546 : ℝ := ((114297728917 : ℝ) /
        1000000)

theorem cellP002ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ + baseCoefficientError2540 ⟨2, by omega⟩) *
      thirdCellTerm2544 ⟨2, by omega⟩ ≤ cellP002Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ +
      baseCoefficientError2540 ⟨2, by omega⟩ ≤ (((((662936605019 * 10^40
        + 4299824093750125240454546843935103764733) * 10^40
        + 6001283085426859120355468540962325118148) * 10^40
        + 8220449752309338076520350286968797787459) : ℝ) /
        ((318286871302263450979444638813965337664 * 10^40
        + 2919365103025391618969452116220780880213) * 10^40
        + 6034115584000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨2, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨2, by omega⟩ ≤ ((712334287955220754469163742363281 : ℝ) /
        (12 * 10^40
        + 9807421463370690713262408230502400000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP002Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP002NormUpper2544, endpointRightP002NormUpper2544,
      fourthP002Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ +
      baseCoefficientError2540 ⟨2, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP002Charge2546]

noncomputable def cellP003Charge2546 : ℝ := ((2517696689 : ℝ) /
        40000)

theorem cellP003ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ + baseCoefficientError2540 ⟨3, by omega⟩) *
      thirdCellTerm2544 ⟨3, by omega⟩ ≤ cellP003Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ +
      baseCoefficientError2540 ⟨3, by omega⟩ ≤ (((((83220662851 * 10^40
        + 9549881470528616528158903214376403459815) * 10^40
        + 9888503178034579278594048397853876507173) * 10^40
        + 8789008822225157515964380579592846419521) : ℝ) /
        ((79571717825565862744861159703491334416 * 10^40
        + 729841275756347904742363029055195220053) * 10^40
        + 4008528896000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨3, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨3, by omega⟩ ≤ ((78121487444952662436717107204809 : ℝ) /
        (1 * 10^40
        + 2980742146337069071326240823050240000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP003Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP003NormUpper2544, endpointRightP003NormUpper2544,
      fourthP003Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ +
      baseCoefficientError2540 ⟨3, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP003Charge2546]

noncomputable def cellP004Charge2546 : ℝ := ((69520379 : ℝ) /
        1000000)

theorem cellP004ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ + baseCoefficientError2540 ⟨4, by omega⟩) *
      thirdCellTerm2544 ⟨4, by omega⟩ ≤ cellP004Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ +
      baseCoefficientError2540 ⟨4, by omega⟩ ≤ ((((101297694843488858660594296889228238368 * 10^40
        + 1420060250456057416269477821756074395977) * 10^40
        + 6051789131444396771423475617839949228863) : ℝ) /
        ((9263367138985295633885678800 * 10^40
        + 6950326282615987732512451231566067206330) * 10^40
        + 5037119488000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨4, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨4, by omega⟩ ≤ ((825241316216460486567414896873831 : ℝ) /
        (12 * 10^40
        + 9807421463370690713262408230502400000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP004Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP004NormUpper2544, endpointRightP004NormUpper2544,
      fourthP004Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ +
      baseCoefficientError2540 ⟨4, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP004Charge2546]

noncomputable def cellP005Charge2546 : ℝ := ((83769541 : ℝ) /
        1000000)

theorem cellP005ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ + baseCoefficientError2540 ⟨5, by omega⟩) *
      thirdCellTerm2544 ⟨5, by omega⟩ ≤ cellP005Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ +
      baseCoefficientError2540 ⟨5, by omega⟩ ≤ (((((229 * 10^40
        + 2318266924411614035050054971843575098612) * 10^40
        + 784627665898255468940620516187288348904) * 10^40
        + 3511436109703212790585710006348744221529) : ℝ) /
        ((74106937111882365071085430405 * 10^40
        + 5602610260927901860099609852528537650644) * 10^40
        + 296955904000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨5, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨5, by omega⟩ ≤ ((4394197968229583567809025247 : ℝ) /
        1622592768292133633915780102881280000000) := by
    unfold thirdCellTerm2544
    have h := fourthP005Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP005NormUpper2544, endpointRightP005NormUpper2544,
      fourthP005Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ +
      baseCoefficientError2540 ⟨5, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP005Charge2546]

noncomputable def cellP006Charge2546 : ℝ := ((3619463 : ℝ) /
        250000)

theorem cellP006ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ + baseCoefficientError2540 ⟨6, by omega⟩) *
      thirdCellTerm2544 ⟨6, by omega⟩ ≤ cellP006Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ +
      baseCoefficientError2540 ⟨6, by omega⟩ ≤ (((((15 * 10^40
        + 2987108903235620477631102382305130779773) * 10^40
        + 3872939689148799597534198934847620902637) * 10^40
        + 5986555156385211145438210839702742197613) : ℝ) /
        ((9263367138985295633885678800 * 10^40
        + 6950326282615987732512451231566067206330) * 10^40
        + 5037119488000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨6, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨6, by omega⟩ ≤ ((113793560005078415227090754429 : ℝ) /
        (12 * 10^40
        + 9807421463370690713262408230502400000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP006Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP006NormUpper2544, endpointRightP006NormUpper2544,
      fourthP006Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ +
      baseCoefficientError2540 ⟨6, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP006Charge2546]

noncomputable def cellP007Charge2546 : ℝ := ((10899 : ℝ) /
        25000)

theorem cellP007ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ + baseCoefficientError2540 ⟨7, by omega⟩) *
      thirdCellTerm2544 ⟨7, by omega⟩ ≤ cellP007Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ +
      baseCoefficientError2540 ⟨7, by omega⟩ ≤ (((((17 * 10^40
        + 3118839107681074729673407826917298493845) * 10^40
        + 290607725344131940531030266963631276807) * 10^40
        + 9978831739756088590643955665223255940279) : ℝ) /
        ((74106937111882365071085430405 * 10^40
        + 5602610260927901860099609852528537650644) * 10^40
        + 296955904000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨7, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨7, by omega⟩ ≤ ((12112395917772306034516273869 : ℝ) /
        (6 * 10^40
        + 4903710731685345356631204115251200000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP007Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP007NormUpper2544, endpointRightP007NormUpper2544,
      fourthP007Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ +
      baseCoefficientError2540 ⟨7, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP007Charge2546]

noncomputable def cellP008Charge2546 : ℝ := ((469177003 : ℝ) /
        200000)

theorem cellP008ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ + baseCoefficientError2540 ⟨8, by omega⟩) *
      thirdCellTerm2544 ⟨8, by omega⟩ ≤ cellP008Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ +
      baseCoefficientError2540 ⟨8, by omega⟩ ≤ ((((6033313744676513990559329937335715893 * 10^40
        + 2878496704160725703236536637626175406599) * 10^40
        + 5929471070091245581432356627475787660957) : ℝ) /
        ((565391060729082985466655 * 10^40
        + 2002377339250647948470001980665989139844) * 10^40
        + 1363832832000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨8, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨8, by omega⟩ ≤ ((5707281152593904807535375514267 : ℝ) /
        (2 * 10^40
        + 5961484292674138142652481646100480000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP008Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP008NormUpper2544, endpointRightP008NormUpper2544,
      fourthP008Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ +
      baseCoefficientError2540 ⟨8, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP008Charge2546]

noncomputable def cellP009Charge2546 : ℝ := ((1629072399 : ℝ) /
        250000)

theorem cellP009ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ + baseCoefficientError2540 ⟨9, by omega⟩) *
      thirdCellTerm2544 ⟨9, by omega⟩ ≤ cellP009Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ +
      baseCoefficientError2540 ⟨9, by omega⟩ ≤ ((((173656070251177298745402462270792114336 * 10^40
        + 9773250537970820037169366879510749866476) * 10^40
        + 118636438400633812185202175508164134999) : ℝ) /
        ((18092513943330655534932966 * 10^40
        + 4076074856020734351040063381311652475012) * 10^40
        + 3642650624000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨9, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨9, by omega⟩ ≤ ((88126971750513893027385044218513 : ℝ) /
        (12 * 10^40
        + 9807421463370690713262408230502400000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP009Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP009NormUpper2544, endpointRightP009NormUpper2544,
      fourthP009Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ +
      baseCoefficientError2540 ⟨9, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP009Charge2546]

noncomputable def cellP010Charge2546 : ℝ := ((6866684691 : ℝ) /
        1000000)

theorem cellP010ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ + baseCoefficientError2540 ⟨10, by omega⟩) *
      thirdCellTerm2544 ⟨10, by omega⟩ ≤ cellP010Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ +
      baseCoefficientError2540 ⟨10, by omega⟩ ≤ ((((13786472946242502856102012349420430300 * 10^40
        + 7092420457096453354230173553376503255444) * 10^40
        + 7261240818800079225708243019149976815703) : ℝ) /
        ((2261564242916331941866620 * 10^40
        + 8009509357002591793880007922663956559376) * 10^40
        + 5455331328000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨10, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨10, by omega⟩ ≤ ((146218520338878985871290358678363 : ℝ) /
        (12 * 10^40
        + 9807421463370690713262408230502400000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP010Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP010NormUpper2544, endpointRightP010NormUpper2544,
      fourthP010Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ +
      baseCoefficientError2540 ⟨10, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP010Charge2546]

noncomputable def cellP011Charge2546 : ℝ := ((7276376151 : ℝ) /
        1000000)

theorem cellP011ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ + baseCoefficientError2540 ⟨11, by omega⟩) *
      thirdCellTerm2544 ⟨11, by omega⟩ ≤ cellP011Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ +
      baseCoefficientError2540 ⟨11, by omega⟩ ≤ ((((86840701653153754533362659927014676727 * 10^40
        + 696019347461324107149580610560740842626) * 10^40
        + 6098900435921021076153789097200058666249) : ℝ) /
        ((18092513943330655534932966 * 10^40
        + 4076074856020734351040063381311652475012) * 10^40
        + 3642650624000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨11, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨11, by omega⟩ ≤ ((196784214224479981284950030728991 : ℝ) /
        (12 * 10^40
        + 9807421463370690713262408230502400000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP011Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP011NormUpper2544, endpointRightP011NormUpper2544,
      fourthP011Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ +
      baseCoefficientError2540 ⟨11, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP011Charge2546]

noncomputable def cellP012Charge2546 : ℝ := ((1869146939 : ℝ) /
        125000)

theorem cellP012ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ + baseCoefficientError2540 ⟨12, by omega⟩) *
      thirdCellTerm2544 ⟨12, by omega⟩ ≤ cellP012Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ +
      baseCoefficientError2540 ⟨12, by omega⟩ ≤ ((((33708382168297497162066443870484007724 * 10^40
        + 4140504327805415050743500621155579032957) * 10^40
        + 5150871504291635525704317821594631365781) : ℝ) /
        ((4523128485832663883733241 * 10^40
        + 6019018714005183587760015845327913118753) * 10^40
        + 910662656000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨12, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨12, by omega⟩ ≤ ((13022788093500271457341540897663 : ℝ) /
        6490371073168534535663120411525120000000) := by
    unfold thirdCellTerm2544
    have h := fourthP012Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP012NormUpper2544, endpointRightP012NormUpper2544,
      fourthP012Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ +
      baseCoefficientError2540 ⟨12, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP012Charge2546]

noncomputable def cellP013Charge2546 : ℝ := ((963302823 : ℝ) /
        125000)

theorem cellP013ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ + baseCoefficientError2540 ⟨13, by omega⟩) *
      thirdCellTerm2544 ⟨13, by omega⟩ ≤ cellP013Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ +
      baseCoefficientError2540 ⟨13, by omega⟩ ≤ ((((6866445712464570894733638406345779434 * 10^40
        + 9963826102670440327794987083811570750676) * 10^40
        + 1232046326062786844704743988083082284453) : ℝ) /
        ((2261564242916331941866620 * 10^40
        + 8009509357002591793880007922663956559376) * 10^40
        + 5455331328000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨13, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨13, by omega⟩ ≤ ((10296255308207369794742954885579 : ℝ) /
        4056481920730334084789450257203200000000) := by
    unfold thirdCellTerm2544
    have h := fourthP013Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP013NormUpper2544, endpointRightP013NormUpper2544,
      fourthP013Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ +
      baseCoefficientError2540 ⟨13, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP013Charge2546]

noncomputable def cellP014Charge2546 : ℝ := ((254169879079 : ℝ) /
        500000)

theorem cellP014ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ + baseCoefficientError2540 ⟨14, by omega⟩) *
      thirdCellTerm2544 ⟨14, by omega⟩ ≤ cellP014Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ +
      baseCoefficientError2540 ⟨14, by omega⟩ ≤ ((((76412118001440715843926048769235947003 * 10^40
        + 3597125816945912312150085254979261020269) * 10^40
        + 4532251577905988424121513159763385317207) : ℝ) /
        ((565391060729082985466655 * 10^40
        + 2002377339250647948470001980665989139844) * 10^40
        + 1363832832000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨14, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨14, by omega⟩ ≤ ((244123903334649033537206481281703 : ℝ) /
        (6 * 10^40
        + 4903710731685345356631204115251200000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP014Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP014NormUpper2544, endpointRightP014NormUpper2544,
      fourthP014Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ +
      baseCoefficientError2540 ⟨14, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP014Charge2546]

noncomputable def cellP015Charge2546 : ℝ := ((163833957373 : ℝ) /
        250000)

theorem cellP015ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ + baseCoefficientError2540 ⟨15, by omega⟩) *
      thirdCellTerm2544 ⟨15, by omega⟩ ≤ cellP015Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ +
      baseCoefficientError2540 ⟨15, by omega⟩ ≤ ((((4776434766896607741971735708499914342 * 10^40
        + 5804499173415983998733395483083072414016) * 10^40
        + 5260231684707342355514359610260251255177) : ℝ) /
        ((35336941295567686591665 * 10^40
        + 9500148583703165496779375123791624321240) * 10^40
        + 2585239552000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨15, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨15, by omega⟩ ≤ ((125868928713510041494296788697073 : ℝ) /
        (2 * 10^40
        + 5961484292674138142652481646100480000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP015Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP015NormUpper2544, endpointRightP015NormUpper2544,
      fourthP015Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ +
      baseCoefficientError2540 ⟨15, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP015Charge2546]

noncomputable def cellP016Charge2546 : ℝ := ((13596318079 : ℝ) /
        1000000)

theorem cellP016ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ + baseCoefficientError2540 ⟨16, by omega⟩) *
      thirdCellTerm2544 ⟨16, by omega⟩ ≤ cellP016Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ +
      baseCoefficientError2540 ⟨16, by omega⟩ ≤ ((((21375800380463757112343186828057132156 * 10^40
        + 3005469446433911836010239975470296495886) * 10^40
        + 4624465867200316905626939800446342809687) : ℝ) /
        ((9046256971665327767466483 * 10^40
        + 2038037428010367175520031690655826237506) * 10^40
        + 1821325312000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨16, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨16, by omega⟩ ≤ ((149381690550892632204256313771941 : ℝ) /
        (2 * 10^40
        + 5961484292674138142652481646100480000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP016Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP016NormUpper2544, endpointRightP016NormUpper2544,
      fourthP016Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ +
      baseCoefficientError2540 ⟨16, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP016Charge2546]

noncomputable def cellP017Charge2546 : ℝ := ((2325716039 : ℝ) /
        40000)

theorem cellP017ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ + baseCoefficientError2540 ⟨17, by omega⟩) *
      thirdCellTerm2544 ⟨17, by omega⟩ ≤ cellP017Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ +
      baseCoefficientError2540 ⟨17, by omega⟩ ≤ ((((268792886079646552552979327563921939802 *
          10^40
        + 3390485050186981133521379617616209249623) * 10^40
        + 8600462187071352855771430599948213035623) : ℝ) /
        ((36185027886661311069865932 * 10^40
        + 8152149712041468702080126762623304950024) * 10^40
        + 7285301248000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨17, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨17, by omega⟩ ≤ ((1016031940546640069370153767302429 : ℝ) /
        (12 * 10^40
        + 9807421463370690713262408230502400000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP017Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP017NormUpper2544, endpointRightP017NormUpper2544,
      fourthP017Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ +
      baseCoefficientError2540 ⟨17, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP017Charge2546]

noncomputable def cellP018Charge2546 : ℝ := ((11271341061 : ℝ) /
        500000)

theorem cellP018ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ + baseCoefficientError2540 ⟨18, by omega⟩) *
      thirdCellTerm2544 ⟨18, by omega⟩ ≤ cellP018Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ +
      baseCoefficientError2540 ⟨18, by omega⟩ ≤ ((((11684044070411210977294048472138772015 * 10^40
        + 9881322302082569906245942212542786123641) * 10^40
        + 7043219078507850128517442478271877459531) : ℝ) /
        ((4523128485832663883733241 * 10^40
        + 6019018714005183587760015845327913118753) * 10^40
        + 910662656000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨18, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨18, by omega⟩ ≤ ((226558752143356382063748360620499 : ℝ) /
        (2 * 10^40
        + 5961484292674138142652481646100480000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP018Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP018NormUpper2544, endpointRightP018NormUpper2544,
      fourthP018Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ +
      baseCoefficientError2540 ⟨18, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP018Charge2546]

noncomputable def cellP019Charge2546 : ℝ := ((71021063743 : ℝ) /
        1000000)

theorem cellP019ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ + baseCoefficientError2540 ⟨19, by omega⟩) *
      thirdCellTerm2544 ⟨19, by omega⟩ ≤ cellP019Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ +
      baseCoefficientError2540 ⟨19, by omega⟩ ≤ ((((244170988641889405075722699840862323176 *
          10^40
        + 2509178028472484570859962733394027234830) * 10^40
        + 739927852801267642065533268710420066873) : ℝ) /
        ((36185027886661311069865932 * 10^40
        + 8152149712041468702080126762623304950024) * 10^40
        + 7285301248000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨19, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨19, by omega⟩ ≤ ((1366222853925625381055386670175817 : ℝ) /
        (12 * 10^40
        + 9807421463370690713262408230502400000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP019Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP019NormUpper2544, endpointRightP019NormUpper2544,
      fourthP019Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ +
      baseCoefficientError2540 ⟨19, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP019Charge2546]

noncomputable def cellP020Charge2546 : ℝ := ((10203209327 : ℝ) /
        125000)

theorem cellP020ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ + baseCoefficientError2540 ⟨20, by omega⟩) *
      thirdCellTerm2544 ⟨20, by omega⟩ ≤ cellP020Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ +
      baseCoefficientError2540 ⟨20, by omega⟩ ≤ ((((115848821104137059659375175579084463999 *
          10^40
        + 643099990344399537759063972216884072841) * 10^40
        + 2655996216542088952150021129975937572499) : ℝ) /
        ((18092513943330655534932966 * 10^40
        + 4076074856020734351040063381311652475012) * 10^40
        + 3642650624000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨20, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨20, by omega⟩ ≤ ((1654754626380234428066217090121897 : ℝ) /
        (12 * 10^40
        + 9807421463370690713262408230502400000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP020Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP020NormUpper2544, endpointRightP020NormUpper2544,
      fourthP020Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ +
      baseCoefficientError2540 ⟨20, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP020Charge2546]

noncomputable def cellP021Charge2546 : ℝ := ((2730549673 : ℝ) /
        100000)

theorem cellP021ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ + baseCoefficientError2540 ⟨21, by omega⟩) *
      thirdCellTerm2544 ⟨21, by omega⟩ ≤ cellP021Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ +
      baseCoefficientError2540 ⟨21, by omega⟩ ≤ ((((66626865540037362994812621614054875466 * 10^40
        + 9061143156193079004997324607780457707950) * 10^40
        + 2747275152063253344505675900241181785623) : ℝ) /
        ((36185027886661311069865932 * 10^40
        + 8152149712041468702080126762623304950024) * 10^40
        + 7285301248000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨21, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨21, by omega⟩ ≤ ((962496453859441781129233804208953 : ℝ) /
        (6 * 10^40
        + 4903710731685345356631204115251200000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP021Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP021NormUpper2544, endpointRightP021NormUpper2544,
      fourthP021Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ +
      baseCoefficientError2540 ⟨21, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP021Charge2546]

noncomputable def cellP022Charge2546 : ℝ := ((5584163797 : ℝ) /
        50000)

theorem cellP022ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ + baseCoefficientError2540 ⟨22, by omega⟩) *
      thirdCellTerm2544 ⟨22, by omega⟩ ≤ cellP022Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ +
      baseCoefficientError2540 ⟨22, by omega⟩ ≤ ((((126455421095091873372421969168167923511 *
          10^40
        + 5277208600918642429678153969848856401050) * 10^40
        + 6951391694373326013099227482209824291249) : ℝ) /
        ((18092513943330655534932966 * 10^40
        + 4076074856020734351040063381311652475012) * 10^40
        + 3642650624000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨22, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨22, by omega⟩ ≤ ((2074192842479632130180362627091407 : ℝ) /
        (12 * 10^40
        + 9807421463370690713262408230502400000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP022Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP022NormUpper2544, endpointRightP022NormUpper2544,
      fourthP022Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ +
      baseCoefficientError2540 ⟨22, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP022Charge2546]

noncomputable def cellP023Charge2546 : ℝ := ((13866271171 : ℝ) /
        100000)

theorem cellP023ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ + baseCoefficientError2540 ⟨23, by omega⟩) *
      thirdCellTerm2544 ⟨23, by omega⟩ ≤ cellP023Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ +
      baseCoefficientError2540 ⟨23, by omega⟩ ≤ ((((511276298416454353097039678983764027661 *
          10^40
        + 7527899143713626692335723795609804328247) * 10^40
        + 1086049602521165547899203038733095993121) : ℝ) /
        ((72370055773322622139731865 * 10^40
        + 6304299424082937404160253525246609900049) * 10^40
        + 4570602496000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨23, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨23, by omega⟩ ≤ ((2547783138800426126387717536472321 : ℝ) /
        (12 * 10^40
        + 9807421463370690713262408230502400000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP023Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP023NormUpper2544, endpointRightP023NormUpper2544,
      fourthP023Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ +
      baseCoefficientError2540 ⟨23, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP023Charge2546]

noncomputable def cellP024Charge2546 : ℝ := ((15861849811 : ℝ) /
        500000)

theorem cellP024ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ + baseCoefficientError2540 ⟨24, by omega⟩) *
      thirdCellTerm2544 ⟨24, by omega⟩ ≤ cellP024Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ +
      baseCoefficientError2540 ⟨24, by omega⟩ ≤ ((((53446135505553485010917072818380911004 * 10^40
        + 2232014645606102581116249049030033049719) * 10^40
        + 6181268009306289579257019627352998191873) : ℝ) /
        ((36185027886661311069865932 * 10^40
        + 8152149712041468702080126762623304950024) * 10^40
        + 7285301248000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨24, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨24, by omega⟩ ≤ ((2788020452304006268372831939779987 : ℝ) /
        (12 * 10^40
        + 9807421463370690713262408230502400000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP024Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP024NormUpper2544, endpointRightP024NormUpper2544,
      fourthP024Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ +
      baseCoefficientError2540 ⟨24, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP024Charge2546]

noncomputable def cellP025Charge2546 : ℝ := ((165361016343 : ℝ) /
        1000000)

theorem cellP025ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ + baseCoefficientError2540 ⟨25, by omega⟩) *
      thirdCellTerm2544 ⟨25, by omega⟩ ≤ cellP025Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ +
      baseCoefficientError2540 ⟨25, by omega⟩ ≤ ((((62430528835003779256303601813041241998 * 10^40
        + 7244716490202004615063470177394605437486) * 10^40
        + 7490506855045784078190015819733452184687) : ℝ) /
        ((9046256971665327767466483 * 10^40
        + 2038037428010367175520031690655826237506) * 10^40
        + 1821325312000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨25, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨25, by omega⟩ ≤ ((155515817204728073307129438382301 : ℝ) /
        6490371073168534535663120411525120000000) := by
    unfold thirdCellTerm2544
    have h := fourthP025Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP025NormUpper2544, endpointRightP025NormUpper2544,
      fourthP025Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ +
      baseCoefficientError2540 ⟨25, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP025Charge2546]

noncomputable def cellP026Charge2546 : ℝ := ((113957473033 : ℝ) /
        1000000)

theorem cellP026ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ + baseCoefficientError2540 ⟨26, by omega⟩) *
      thirdCellTerm2544 ⟨26, by omega⟩ ≤ cellP026Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ +
      baseCoefficientError2540 ⟨26, by omega⟩ ≤ ((((77243077954253104144433158925516046152 * 10^40
        + 2142437133562224996504443947604249748491) * 10^40
        + 8710478732253464533250604206452988353749) : ℝ) /
        ((18092513943330655534932966 * 10^40
        + 4076074856020734351040063381311652475012) * 10^40
        + 3642650624000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨26, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨26, by omega⟩ ≤ ((3464827983700922825349569512368401 : ℝ) /
        (12 * 10^40
        + 9807421463370690713262408230502400000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP026Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP026NormUpper2544, endpointRightP026NormUpper2544,
      fourthP026Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ +
      baseCoefficientError2540 ⟨26, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP026Charge2546]

noncomputable def cellP027Charge2546 : ℝ := ((97266781801 : ℝ) /
        200000)

theorem cellP027ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ + baseCoefficientError2540 ⟨27, by omega⟩) *
      thirdCellTerm2544 ⟨27, by omega⟩ ≤ cellP027Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ +
      baseCoefficientError2540 ⟨27, by omega⟩ ≤ ((((1108974111919111548099277736891035049 * 10^40
        + 5224709099718969740803316411378711125064) * 10^40
        + 6593813365636201947000706467987543525979) : ℝ) /
        ((70673882591135373183331 * 10^40
        + 9000297167406330993558750247583248642480) * 10^40
        + 5170479104000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨27, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨27, by omega⟩ ≤ ((4023199947494551999132299192522057 : ℝ) /
        (12 * 10^40
        + 9807421463370690713262408230502400000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP027Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP027NormUpper2544, endpointRightP027NormUpper2544,
      fourthP027Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ +
      baseCoefficientError2540 ⟨27, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP027Charge2546]

noncomputable def cellP028Charge2546 : ℝ := ((216949280919 : ℝ) /
        500000)

theorem cellP028ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ + baseCoefficientError2540 ⟨28, by omega⟩) *
      thirdCellTerm2544 ⟨28, by omega⟩ ≤ cellP028Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ +
      baseCoefficientError2540 ⟨28, by omega⟩ ≤ ((((59800428709388611431100465369520699479 * 10^40
        + 1074095473532884734655837300850657686619) * 10^40
        + 3167775069923583462194495929809963397031) : ℝ) /
        ((4523128485832663883733241 * 10^40
        + 6019018714005183587760015845327913118753) * 10^40
        + 910662656000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨28, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨28, by omega⟩ ≤ ((852025036503278983349577391570131 : ℝ) /
        (2 * 10^40
        + 5961484292674138142652481646100480000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP028Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP028NormUpper2544, endpointRightP028NormUpper2544,
      fourthP028Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ +
      baseCoefficientError2540 ⟨28, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP028Charge2546]

noncomputable def cellP029Charge2546 : ℝ := ((65267761737 : ℝ) /
        125000)

theorem cellP029ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ + baseCoefficientError2540 ⟨29, by omega⟩) *
      thirdCellTerm2544 ⟨29, by omega⟩ ≤ cellP029Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ +
      baseCoefficientError2540 ⟨29, by omega⟩ ≤ ((((33044562702864613694961276831163920415 * 10^40
        + 8865212964294645574062897984442766730727) * 10^40
        + 2429414593206452607322928077743726815703) : ℝ) /
        ((2261564242916331941866620 * 10^40
        + 8009509357002591793880007922663956559376) * 10^40
        + 5455331328000000000000000000000000000000)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨29, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨29, by omega⟩ ≤ ((579838652654863222737381870954829 : ℝ) /
        (1 * 10^40
        + 6225927682921336339157801028812800000000)) := by
    unfold thirdCellTerm2544
    have h := fourthP029Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP029NormUpper2544, endpointRightP029NormUpper2544,
      fourthP029Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ +
      baseCoefficientError2540 ⟨29, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [cellP029Charge2546]

noncomputable def cellCharge2546 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => cellP000Charge2546
  | 1 => cellP001Charge2546
  | 2 => cellP002Charge2546
  | 3 => cellP003Charge2546
  | 4 => cellP004Charge2546
  | 5 => cellP005Charge2546
  | 6 => cellP006Charge2546
  | 7 => cellP007Charge2546
  | 8 => cellP008Charge2546
  | 9 => cellP009Charge2546
  | 10 => cellP010Charge2546
  | 11 => cellP011Charge2546
  | 12 => cellP012Charge2546
  | 13 => cellP013Charge2546
  | 14 => cellP014Charge2546
  | 15 => cellP015Charge2546
  | 16 => cellP016Charge2546
  | 17 => cellP017Charge2546
  | 18 => cellP018Charge2546
  | 19 => cellP019Charge2546
  | 20 => cellP020Charge2546
  | 21 => cellP021Charge2546
  | 22 => cellP022Charge2546
  | 23 => cellP023Charge2546
  | 24 => cellP024Charge2546
  | 25 => cellP025Charge2546
  | 26 => cellP026Charge2546
  | 27 => cellP027Charge2546
  | 28 => cellP028Charge2546
  | 29 => cellP029Charge2546
  | _ => 0

theorem cellChargeBound2546 (i : Fin 30) :
    (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      thirdCellTerm2544 i ≤ cellCharge2546 i := by
  fin_cases i
  · exact cellP000ChargeBound2546
  · exact cellP001ChargeBound2546
  · exact cellP002ChargeBound2546
  · exact cellP003ChargeBound2546
  · exact cellP004ChargeBound2546
  · exact cellP005ChargeBound2546
  · exact cellP006ChargeBound2546
  · exact cellP007ChargeBound2546
  · exact cellP008ChargeBound2546
  · exact cellP009ChargeBound2546
  · exact cellP010ChargeBound2546
  · exact cellP011ChargeBound2546
  · exact cellP012ChargeBound2546
  · exact cellP013ChargeBound2546
  · exact cellP014ChargeBound2546
  · exact cellP015ChargeBound2546
  · exact cellP016ChargeBound2546
  · exact cellP017ChargeBound2546
  · exact cellP018ChargeBound2546
  · exact cellP019ChargeBound2546
  · exact cellP020ChargeBound2546
  · exact cellP021ChargeBound2546
  · exact cellP022ChargeBound2546
  · exact cellP023ChargeBound2546
  · exact cellP024ChargeBound2546
  · exact cellP025ChargeBound2546
  · exact cellP026ChargeBound2546
  · exact cellP027ChargeBound2546
  · exact cellP028ChargeBound2546
  · exact cellP029ChargeBound2546

noncomputable def cellThirdUpper2546 : ℝ := ((1237907300787 : ℝ) /
        250000)

noncomputable def cellCurvatureUpper2546 : ℝ := ((5663644581 : ℝ) /
        1000000)

noncomputable def cellIntegralUpper2546 : ℝ := ((379207837 : ℝ) /
        500000000000)

theorem cellThirdBound2546 : thirdAggregateUpper2544 ≤ cellThirdUpper2546 := by
  have h : thirdAggregateUpper2544 ≤ ∑ i : Fin 30, cellCharge2546 i :=
    Finset.sum_le_sum (fun i _ => cellChargeBound2546 i)
  apply h.trans
  rw [sum30_chain2541]
  norm_num [cellCharge2546, cellThirdUpper2546, cellP000Charge2546, cellP001Charge2546,
      cellP002Charge2546, cellP003Charge2546, cellP004Charge2546, cellP005Charge2546,
      cellP006Charge2546, cellP007Charge2546, cellP008Charge2546, cellP009Charge2546,
      cellP010Charge2546, cellP011Charge2546, cellP012Charge2546, cellP013Charge2546,
      cellP014Charge2546, cellP015Charge2546, cellP016Charge2546, cellP017Charge2546,
      cellP018Charge2546, cellP019Charge2546, cellP020Charge2546, cellP021Charge2546,
      cellP022Charge2546, cellP023Charge2546, cellP024Charge2546, cellP025Charge2546,
      cellP026Charge2546, cellP027Charge2546, cellP028Charge2546, cellP029Charge2546]

theorem cellCurvatureBound2546 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 endpointLeftPosition2544 endpointRightPosition2544 ≤
        cellCurvatureUpper2546 := by
  have h := curvature_after_endpoints2544
  have ht := cellThirdBound2546
  norm_num [signedMidpointUpper2543, cellThirdUpper2546, cellCurvatureUpper2546,
    endpointLeftPosition2544, endpointRightPosition2544] at *
  linarith

theorem cellIntegralBound2546 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤ baseCoefficientError2540 i) :
    (∫ x in endpointLeftPosition2544..endpointRightPosition2544,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤
        cellIntegralUpper2546 := by
  have h := weightedPhysical2539_norm_integral_le_signed_cell (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541 hcoeff
    (a := endpointLeftPosition2544) (b := endpointRightPosition2544)
    (by norm_num [endpointLeftPosition2544, endpointRightPosition2544])
  have hl := adaptiveN05440PlusSigned_le2542
  have hr := adaptiveN05441PlusSigned_le2542
  have hc := cellCurvatureBound2546
  have hleft : adaptiveN05440PlusPosition2542 = endpointLeftPosition2544 := by
    norm_num [adaptiveN05440PlusPosition2542, endpointLeftPosition2544]
  have hright : adaptiveN05441PlusPosition2542 = endpointRightPosition2544 := by
    norm_num [adaptiveN05441PlusPosition2542, endpointRightPosition2544]
  rw [hleft] at hl
  rw [hright] at hr
  norm_num [endpointLeftPosition2544, endpointRightPosition2544, adaptiveN05440PlusUpper2542,
    adaptiveN05441PlusUpper2542, cellCurvatureUpper2546, cellIntegralUpper2546] at *
  linarith

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.cellChargeBound2546
#print axioms ConnesWeilRH.Dev.cellThirdBound2546
#print axioms ConnesWeilRH.Dev.cellCurvatureBound2546
#print axioms ConnesWeilRH.Dev.cellIntegralBound2546
