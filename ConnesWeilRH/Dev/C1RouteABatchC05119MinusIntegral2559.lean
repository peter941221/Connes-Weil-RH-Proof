import ConnesWeilRH.Dev.C1RouteABatchC05119MinusAssembly2559
import ConnesWeilRH.Dev.C1RouteABatchValueN05120Minus2559
import ConnesWeilRH.Dev.C1RouteABatchValueN05119Minus2559

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def batchC05119MinusCellP000Charge2559 : ℝ := ((1947669566259 : ℝ) /
        1000000)

theorem batchC05119MinusCellP000ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ + baseCoefficientError2540 ⟨0, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨0, by omega⟩ ≤ batchC05119MinusCellP000Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨0, by omega⟩ ≤ (((88488590528 * 10^40
        + 2161260874684443202365995898430532303539) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP000NormUpper2559, batchC05119MinusRightP000NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP000Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ +
      baseCoefficientError2540 ⟨0, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP000Charge2559]

noncomputable def batchC05119MinusCellP001Charge2559 : ℝ := ((27377284241 : ℝ) /
        125000)

theorem batchC05119MinusCellP001ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ + baseCoefficientError2540 ⟨1, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨1, by omega⟩ ≤ batchC05119MinusCellP001Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨1, by omega⟩ ≤ (((87808655345 * 10^40
        + 1406819854922359114343240230818458298549) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP001NormUpper2559, batchC05119MinusRightP001NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP001Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ +
      baseCoefficientError2540 ⟨1, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP001Charge2559]

noncomputable def batchC05119MinusCellP002Charge2559 : ℝ := ((121716002293 : ℝ) /
        1000000)

theorem batchC05119MinusCellP002ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ + baseCoefficientError2540 ⟨2, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨2, by omega⟩ ≤ batchC05119MinusCellP002Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨2, by omega⟩ ≤ (((10932102145 * 10^40
        + 3632009956196694879125110975541528519759) : ℝ) /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP002NormUpper2559, batchC05119MinusRightP002NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP002Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ +
      baseCoefficientError2540 ⟨2, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP002Charge2559]

noncomputable def batchC05119MinusCellP003Charge2559 : ℝ := ((30490109079 : ℝ) /
        500000)

theorem batchC05119MinusCellP003ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ + baseCoefficientError2540 ⟨3, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨3, by omega⟩ ≤ batchC05119MinusCellP003Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨3, by omega⟩ ≤ (((21815029697 * 10^40
        + 1461290390830746110017837553243900898279) : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP003NormUpper2559, batchC05119MinusRightP003NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP003Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ +
      baseCoefficientError2540 ⟨3, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP003Charge2559]

noncomputable def batchC05119MinusCellP004Charge2559 : ℝ := ((63674439 : ℝ) /
        1000000)

theorem batchC05119MinusCellP004ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ + baseCoefficientError2540 ⟨4, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨4, by omega⟩ ≤ batchC05119MinusCellP004Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨4, by omega⟩ ≤ (((85100819 * 10^40
        + 3480975091278270551529880582556057407561) : ℝ) /
        (14615016373309029 * 10^40
        + 1820368483271628301965593254297600000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP004NormUpper2559, batchC05119MinusRightP004NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP004Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ +
      baseCoefficientError2540 ⟨4, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP004Charge2559]

noncomputable def batchC05119MinusCellP005Charge2559 : ℝ := ((32657423 : ℝ) /
        1000000)

theorem batchC05119MinusCellP005ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ + baseCoefficientError2540 ⟨5, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨5, by omega⟩ ≤ batchC05119MinusCellP005Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨5, by omega⟩ ≤ (((7900146 * 10^40
        + 908622505524847251470503961784046322191) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP005NormUpper2559, batchC05119MinusRightP005NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP005Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ +
      baseCoefficientError2540 ⟨5, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP005Charge2559]

noncomputable def batchC05119MinusCellP006Charge2559 : ℝ := ((8544609 : ℝ) /
        1000000)

theorem batchC05119MinusCellP006ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ + baseCoefficientError2540 ⟨6, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨6, by omega⟩ ≤ batchC05119MinusCellP006Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨6, by omega⟩ ≤ (((1935733 * 10^40
        + 2132028338826533264715218528719676500303) : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP006NormUpper2559, batchC05119MinusRightP006NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP006Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ +
      baseCoefficientError2540 ⟨6, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP006Charge2559]

noncomputable def batchC05119MinusCellP007Charge2559 : ℝ := ((653917 : ℝ) /
        1000000)

theorem batchC05119MinusCellP007ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ + baseCoefficientError2540 ⟨7, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨7, by omega⟩ ≤ batchC05119MinusCellP007Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨7, by omega⟩ ≤ (((130914 * 10^40
        + 584131862909226827565916000150479263053) : ℝ) /
        (467680523945888933 * 10^40
        + 8251791464692105662898984137523200000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP007NormUpper2559, batchC05119MinusRightP007NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP007Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ +
      baseCoefficientError2540 ⟨7, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP007Charge2559]

noncomputable def batchC05119MinusCellP008Charge2559 : ℝ := ((312186981 : ℝ) /
        100000)

theorem batchC05119MinusCellP008ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ + baseCoefficientError2540 ⟨8, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨8, by omega⟩ ≤ batchC05119MinusCellP008Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨8, by omega⟩ ≤ (((1094578937 * 10^40
        + 3615749736338861273183531361169120238399) : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP008NormUpper2559, batchC05119MinusRightP008NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP008Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ +
      baseCoefficientError2540 ⟨8, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP008Charge2559]

noncomputable def batchC05119MinusCellP009Charge2559 : ℝ := ((1766538319 : ℝ) /
        200000)

theorem batchC05119MinusCellP009ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ + baseCoefficientError2540 ⟨9, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨9, by omega⟩ ≤ batchC05119MinusCellP009Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨9, by omega⟩ ≤ (((6886067586 * 10^40
        + 5210044499655612326590735391411578672963) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP009NormUpper2559, batchC05119MinusRightP009NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP009Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ +
      baseCoefficientError2540 ⟨9, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP009Charge2559]

noncomputable def batchC05119MinusCellP010Charge2559 : ℝ := ((9355127269 : ℝ) /
        1000000)

theorem batchC05119MinusCellP010ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ + baseCoefficientError2540 ⟨10, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨10, by omega⟩ ≤ batchC05119MinusCellP010Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨10, by omega⟩ ≤ (((11483511862 * 10^40
        + 5905757783573768867313930997514143640241) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP010NormUpper2559, batchC05119MinusRightP010NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP010Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ +
      baseCoefficientError2540 ⟨10, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP010Charge2559]

noncomputable def batchC05119MinusCellP011Charge2559 : ℝ := ((9936491747 : ℝ) /
        1000000)

theorem batchC05119MinusCellP011ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ + baseCoefficientError2540 ⟨11, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨11, by omega⟩ ≤ batchC05119MinusCellP011Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨11, by omega⟩ ≤ (((30981891679 * 10^40
        + 4449987756158009726995561275172964025993) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP011NormUpper2559, batchC05119MinusRightP011NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP011Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ +
      baseCoefficientError2540 ⟨11, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP011Charge2559]

noncomputable def batchC05119MinusCellP012Charge2559 : ℝ := ((20457605871 : ℝ) /
        1000000)

theorem batchC05119MinusCellP012ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ + baseCoefficientError2540 ⟨12, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨12, by omega⟩ ≤ batchC05119MinusCellP012Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨12, by omega⟩ ≤ (((5135291475 * 10^40
        + 1679666280356380996560277291884990711707) : ℝ) /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP012NormUpper2559, batchC05119MinusRightP012NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP012Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ +
      baseCoefficientError2540 ⟨12, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP012Charge2559]

noncomputable def batchC05119MinusCellP013Charge2559 : ℝ := ((10557209539 : ℝ) /
        1000000)

theorem batchC05119MinusCellP013ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ + baseCoefficientError2540 ⟨13, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨13, by omega⟩ ≤ batchC05119MinusCellP013Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨13, by omega⟩ ≤ (((52038568652 * 10^40
        + 4307837102998603673405218707081971123297) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP013NormUpper2559, batchC05119MinusRightP013NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP013Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ +
      baseCoefficientError2540 ⟨13, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP013Charge2559]

noncomputable def batchC05119MinusCellP014Charge2559 : ℝ := ((174415136661 : ℝ) /
        250000)

theorem batchC05119MinusCellP014ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ + baseCoefficientError2540 ⟨14, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨14, by omega⟩ ≤ batchC05119MinusCellP014Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨14, by omega⟩ ≤ (((38627813963 * 10^40
        + 3683798759009039299387641077592690956201) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP014NormUpper2559, batchC05119MinusRightP014NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP014Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ +
      baseCoefficientError2540 ⟨14, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP014Charge2559]

noncomputable def batchC05119MinusCellP015Charge2559 : ℝ := ((900270416261 : ℝ) /
        1000000)

theorem batchC05119MinusCellP015ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ + baseCoefficientError2540 ⟨15, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨15, by omega⟩ ≤ batchC05119MinusCellP015Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨15, by omega⟩ ≤ (((99677548001 * 10^40
        + 9531439287716662673479570068249557149141) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP015NormUpper2559, batchC05119MinusRightP015NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP015Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ +
      baseCoefficientError2540 ⟨15, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP015Charge2559]

noncomputable def batchC05119MinusCellP016Charge2559 : ℝ := ((18688661671 : ℝ) /
        1000000)

theorem batchC05119MinusCellP016ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ + baseCoefficientError2540 ⟨16, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨16, by omega⟩ ≤ batchC05119MinusCellP016Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨16, by omega⟩ ≤ (((59182595050 * 10^40
        + 8801991785052588232992450270746044255089) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP016NormUpper2559, batchC05119MinusRightP016NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP016Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ +
      baseCoefficientError2540 ⟨16, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP016Charge2559]

noncomputable def batchC05119MinusCellP017Charge2559 : ℝ := ((15998097639 : ℝ) /
        200000)

theorem batchC05119MinusCellP017ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ + baseCoefficientError2540 ⟨17, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨17, by omega⟩ ≤ batchC05119MinusCellP017Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨17, by omega⟩ ≤ (((161156843125 * 10^40
        + 8433802974386617399696585212955457329803) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP017NormUpper2559, batchC05119MinusRightP017NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP017Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ +
      baseCoefficientError2540 ⟨17, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP017Charge2559]

noncomputable def batchC05119MinusCellP018Charge2559 : ℝ := ((31021789117 : ℝ) /
        1000000)

theorem batchC05119MinusCellP018ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ + baseCoefficientError2540 ⟨18, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨18, by omega⟩ ≤ batchC05119MinusCellP018Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨18, by omega⟩ ≤ (((1404112393 * 10^40
        + 5770991697407368179047595843030976000903) : ℝ) /
        (116920130986472233 * 10^40
        + 4562947866173026415724746034380800000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP018NormUpper2559, batchC05119MinusRightP018NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP018Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ +
      baseCoefficientError2540 ⟨18, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP018Charge2559]

noncomputable def batchC05119MinusCellP019Charge2559 : ℝ := ((24444253401 : ℝ) /
        250000)

theorem batchC05119MinusCellP019ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ + baseCoefficientError2540 ⟨19, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨19, by omega⟩ ≤ batchC05119MinusCellP019Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨19, by omega⟩ ≤ (((216855719688 * 10^40
        + 2005291329201358511347269344397662092751) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP019NormUpper2559, batchC05119MinusRightP019NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP019Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ +
      baseCoefficientError2540 ⟨19, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP019Charge2559]

noncomputable def batchC05119MinusCellP020Charge2559 : ℝ := ((22484237157 : ℝ) /
        200000)

theorem batchC05119MinusCellP020ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ + baseCoefficientError2540 ⟨20, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨20, by omega⟩ ≤ batchC05119MinusCellP020Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨20, by omega⟩ ≤ (((52551451698 * 10^40
        + 7911268737923481841333875817328015925499) : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP020NormUpper2559, batchC05119MinusRightP020NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP020Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ +
      baseCoefficientError2540 ⟨20, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP020Charge2559]

noncomputable def batchC05119MinusCellP021Charge2559 : ℝ := ((9404459261 : ℝ) /
        250000)

theorem batchC05119MinusCellP021ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ + baseCoefficientError2540 ⟨21, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨21, by omega⟩ ≤ batchC05119MinusCellP021Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨21, by omega⟩ ≤ (((61150865557 * 10^40
        + 9108580562416397831947116173421313199867) : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP021NormUpper2559, batchC05119MinusRightP021NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP021Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ +
      baseCoefficientError2540 ⟨21, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP021Charge2559]

noncomputable def batchC05119MinusCellP022Charge2559 : ℝ := ((153882180581 : ℝ) /
        1000000)

theorem batchC05119MinusCellP022ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ + baseCoefficientError2540 ⟨22, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨22, by omega⟩ ≤ batchC05119MinusCellP022Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨22, by omega⟩ ≤ (((20593448401 * 10^40
        + 8504989784743433860170107712051702762343) : ℝ) /
        (935361047891777867 * 10^40
        + 6503582929384211325797968275046400000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP022NormUpper2559, batchC05119MinusRightP022NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP022Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ +
      baseCoefficientError2540 ⟨22, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP022Charge2559]

noncomputable def batchC05119MinusCellP023Charge2559 : ℝ := ((191118680517 : ℝ) /
        1000000)

theorem batchC05119MinusCellP023ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ + baseCoefficientError2540 ⟨23, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨23, by omega⟩ ≤ batchC05119MinusCellP023Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨23, by omega⟩ ≤ (((25303795300 * 10^40
        + 4107990433975965859867590568690191204343) : ℝ) /
        (935361047891777867 * 10^40
        + 6503582929384211325797968275046400000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP023NormUpper2559, batchC05119MinusRightP023NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP023Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ +
      baseCoefficientError2540 ⟨23, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP023Charge2559]

noncomputable def batchC05119MinusCellP024Charge2559 : ℝ := ((43730538947 : ℝ) /
        1000000)

theorem batchC05119MinusCellP024ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ + baseCoefficientError2540 ⟨24, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨24, by omega⟩ ≤ batchC05119MinusCellP024Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨24, by omega⟩ ≤ (((443094843360 * 10^40
        + 1642245804745254927960021894028971630441) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP024NormUpper2559, batchC05119MinusRightP024NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP024Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ +
      baseCoefficientError2540 ⟨24, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP024Charge2559]

noncomputable def batchC05119MinusCellP025Charge2559 : ℝ := ((911927023 : ℝ) /
        4000)

theorem batchC05119MinusCellP025ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ + baseCoefficientError2540 ⟨25, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨25, by omega⟩ ≤ batchC05119MinusCellP025Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨25, by omega⟩ ≤ (((15449743909 * 10^40
        + 6969753670983620259504231238570059166981) : ℝ) /
        (467680523945888933 * 10^40
        + 8251791464692105662898984137523200000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP025NormUpper2559, batchC05119MinusRightP025NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP025Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ +
      baseCoefficientError2540 ⟨25, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP025Charge2559]

noncomputable def batchC05119MinusCellP026Charge2559 : ℝ := ((19641784593 : ℝ) /
        125000)

theorem batchC05119MinusCellP026ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ + baseCoefficientError2540 ⟨26, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨26, by omega⟩ ≤ batchC05119MinusCellP026Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨26, by omega⟩ ≤ (((4406558354 * 10^40
        + 6059259865533368129950169295034727541723) : ℝ) /
        (119726214130147567 * 10^40
        + 592458614961179049702139939205939200000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP026NormUpper2559, batchC05119MinusRightP026NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP026Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ +
      baseCoefficientError2540 ⟨26, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP026Charge2559]

noncomputable def batchC05119MinusCellP027Charge2559 : ℝ := ((670720226263 : ℝ) /
        1000000)

theorem batchC05119MinusCellP027ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ + baseCoefficientError2540 ⟨27, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨27, by omega⟩ ≤ batchC05119MinusCellP027Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨27, by omega⟩ ≤ (((127940547341 * 10^40
        + 8289084400335869708686554467907612759019) : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP027NormUpper2559, batchC05119MinusRightP027NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP027Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ +
      baseCoefficientError2540 ⟨27, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP027Charge2559]

noncomputable def batchC05119MinusCellP028Charge2559 : ℝ := ((74805499663 : ℝ) /
        125000)

theorem batchC05119MinusCellP028ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ + baseCoefficientError2540 ⟨28, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨28, by omega⟩ ≤ batchC05119MinusCellP028Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨28, by omega⟩ ≤ (((677419049630 * 10^40
        + 1313430205894039018134945273931902047131) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP028NormUpper2559, batchC05119MinusRightP028NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP028Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ +
      baseCoefficientError2540 ⟨28, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP028Charge2559]

noncomputable def batchC05119MinusCellP029Charge2559 : ℝ := ((720219232169 : ℝ) /
        1000000)

theorem batchC05119MinusCellP029ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ + baseCoefficientError2540 ⟨29, by omega⟩) *
      batchC05119MinusThirdCell2559 ⟨29, by omega⟩ ≤ batchC05119MinusCellP029Charge2559 := by
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
  have ht : batchC05119MinusThirdCell2559 ⟨29, by omega⟩ ≤ (((73768830288 * 10^40
        + 5116632116847683841671779821827300148513) : ℝ) /
        (1496577676626844588 * 10^40
        + 2405732687014738121276749240074240000000)) := by
    unfold batchC05119MinusThirdCell2559
    norm_num [batchC05119MinusLeftNormUpper2559, batchC05119MinusRightNormUpper2559,
      batchC05119MinusLeftP029NormUpper2559, batchC05119MinusRightP029NormUpper2559,
      batchC05119MinusFourthUpper2559, batchC05119MinusFourthP029Upper2559,
      batchN05119MinusPosition2559, batchN05120MinusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ +
      baseCoefficientError2540 ⟨29, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119MinusCellP029Charge2559]

noncomputable def batchC05119MinusCellCharge2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05119MinusCellP000Charge2559
  | 1 => batchC05119MinusCellP001Charge2559
  | 2 => batchC05119MinusCellP002Charge2559
  | 3 => batchC05119MinusCellP003Charge2559
  | 4 => batchC05119MinusCellP004Charge2559
  | 5 => batchC05119MinusCellP005Charge2559
  | 6 => batchC05119MinusCellP006Charge2559
  | 7 => batchC05119MinusCellP007Charge2559
  | 8 => batchC05119MinusCellP008Charge2559
  | 9 => batchC05119MinusCellP009Charge2559
  | 10 => batchC05119MinusCellP010Charge2559
  | 11 => batchC05119MinusCellP011Charge2559
  | 12 => batchC05119MinusCellP012Charge2559
  | 13 => batchC05119MinusCellP013Charge2559
  | 14 => batchC05119MinusCellP014Charge2559
  | 15 => batchC05119MinusCellP015Charge2559
  | 16 => batchC05119MinusCellP016Charge2559
  | 17 => batchC05119MinusCellP017Charge2559
  | 18 => batchC05119MinusCellP018Charge2559
  | 19 => batchC05119MinusCellP019Charge2559
  | 20 => batchC05119MinusCellP020Charge2559
  | 21 => batchC05119MinusCellP021Charge2559
  | 22 => batchC05119MinusCellP022Charge2559
  | 23 => batchC05119MinusCellP023Charge2559
  | 24 => batchC05119MinusCellP024Charge2559
  | 25 => batchC05119MinusCellP025Charge2559
  | 26 => batchC05119MinusCellP026Charge2559
  | 27 => batchC05119MinusCellP027Charge2559
  | 28 => batchC05119MinusCellP028Charge2559
  | 29 => batchC05119MinusCellP029Charge2559
  | _ => 0

theorem batchC05119MinusCellChargeBound2559 (i : Fin 30) :
    (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC05119MinusThirdCell2559 i ≤ batchC05119MinusCellCharge2559 i := by
  fin_cases i
  · exact batchC05119MinusCellP000ChargeBound2559
  · exact batchC05119MinusCellP001ChargeBound2559
  · exact batchC05119MinusCellP002ChargeBound2559
  · exact batchC05119MinusCellP003ChargeBound2559
  · exact batchC05119MinusCellP004ChargeBound2559
  · exact batchC05119MinusCellP005ChargeBound2559
  · exact batchC05119MinusCellP006ChargeBound2559
  · exact batchC05119MinusCellP007ChargeBound2559
  · exact batchC05119MinusCellP008ChargeBound2559
  · exact batchC05119MinusCellP009ChargeBound2559
  · exact batchC05119MinusCellP010ChargeBound2559
  · exact batchC05119MinusCellP011ChargeBound2559
  · exact batchC05119MinusCellP012ChargeBound2559
  · exact batchC05119MinusCellP013ChargeBound2559
  · exact batchC05119MinusCellP014ChargeBound2559
  · exact batchC05119MinusCellP015ChargeBound2559
  · exact batchC05119MinusCellP016ChargeBound2559
  · exact batchC05119MinusCellP017ChargeBound2559
  · exact batchC05119MinusCellP018ChargeBound2559
  · exact batchC05119MinusCellP019ChargeBound2559
  · exact batchC05119MinusCellP020ChargeBound2559
  · exact batchC05119MinusCellP021ChargeBound2559
  · exact batchC05119MinusCellP022ChargeBound2559
  · exact batchC05119MinusCellP023ChargeBound2559
  · exact batchC05119MinusCellP024ChargeBound2559
  · exact batchC05119MinusCellP025ChargeBound2559
  · exact batchC05119MinusCellP026ChargeBound2559
  · exact batchC05119MinusCellP027ChargeBound2559
  · exact batchC05119MinusCellP028ChargeBound2559
  · exact batchC05119MinusCellP029ChargeBound2559

noncomputable def batchC05119MinusCellThirdUpper2559 : ℝ := ((7150429413453 : ℝ) /
        1000000)

noncomputable def batchC05119MinusCellCurvatureUpper2559 : ℝ := ((7188870623 : ℝ) /
        200000)

noncomputable def batchC05119MinusCellIntegralUpper2559 : ℝ := ((2208147857 : ℝ) /
        125000000000)

theorem batchC05119MinusCellThirdBound2559 : batchC05119MinusThirdAggregate2559 ≤
    batchC05119MinusCellThirdUpper2559 := by
  have h : batchC05119MinusThirdAggregate2559 ≤ ∑ i : Fin 30, batchC05119MinusCellCharge2559 i :=
    Finset.sum_le_sum (fun i _ => batchC05119MinusCellChargeBound2559 i)
  apply h.trans
  rw [sum30_chain2541]
  norm_num [batchC05119MinusCellCharge2559, batchC05119MinusCellThirdUpper2559,
      batchC05119MinusCellP000Charge2559, batchC05119MinusCellP001Charge2559,
      batchC05119MinusCellP002Charge2559, batchC05119MinusCellP003Charge2559,
          batchC05119MinusCellP004Charge2559, batchC05119MinusCellP005Charge2559,
      batchC05119MinusCellP006Charge2559, batchC05119MinusCellP007Charge2559,
          batchC05119MinusCellP008Charge2559, batchC05119MinusCellP009Charge2559,
      batchC05119MinusCellP010Charge2559, batchC05119MinusCellP011Charge2559,
          batchC05119MinusCellP012Charge2559, batchC05119MinusCellP013Charge2559,
      batchC05119MinusCellP014Charge2559, batchC05119MinusCellP015Charge2559,
          batchC05119MinusCellP016Charge2559, batchC05119MinusCellP017Charge2559,
      batchC05119MinusCellP018Charge2559, batchC05119MinusCellP019Charge2559,
          batchC05119MinusCellP020Charge2559, batchC05119MinusCellP021Charge2559,
      batchC05119MinusCellP022Charge2559, batchC05119MinusCellP023Charge2559,
          batchC05119MinusCellP024Charge2559, batchC05119MinusCellP025Charge2559,
      batchC05119MinusCellP026Charge2559, batchC05119MinusCellP027Charge2559,
          batchC05119MinusCellP028Charge2559, batchC05119MinusCellP029Charge2559]

theorem batchC05119MinusCellCurvatureBound2559 :
    signedCurvatureUpper2539 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN05119MinusPosition2559 batchN05120MinusPosition2559 ≤
        batchC05119MinusCellCurvatureUpper2559 := by
  have h := batchC05119MinusCurvature_bound2559
  have ht := batchC05119MinusCellThirdBound2559
  norm_num [batchC05119MinusSignedMidpointUpper2559, batchC05119MinusCellThirdUpper2559,
      batchC05119MinusCellCurvatureUpper2559,
    batchN05119MinusPosition2559, batchN05120MinusPosition2559] at *
  linarith

theorem batchC05119MinusCellIntegralBound2559 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤ baseCoefficientError2540 i) :
    (∫ x in batchN05119MinusPosition2559..batchN05120MinusPosition2559,
      ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖) ≤
        batchC05119MinusCellIntegralUpper2559 := by
  have h := weightedPhysical2539_norm_integral_le_signed_cell (-1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541 hcoeff
    (a := batchN05119MinusPosition2559) (b := batchN05120MinusPosition2559)
    (by norm_num [batchN05119MinusPosition2559, batchN05120MinusPosition2559])
  have hl := batchValueN05119MinusSigned_le2559
  have hr := batchValueN05120MinusSigned_le2559
  have hc := batchC05119MinusCellCurvatureBound2559
  have hleft : batchValueN05119MinusPosition2559 = batchN05119MinusPosition2559 := by
    norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559]
  have hright : batchValueN05120MinusPosition2559 = batchN05120MinusPosition2559 := by
    norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559]
  rw [hleft] at hl
  rw [hright] at hr
  norm_num [batchN05119MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05119MinusUpper2559,
    batchValueN05120MinusUpper2559, batchC05119MinusCellCurvatureUpper2559,
        batchC05119MinusCellIntegralUpper2559] at *
  linarith

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05119MinusCellChargeBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusCellThirdBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusCellCurvatureBound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusCellIntegralBound2559
