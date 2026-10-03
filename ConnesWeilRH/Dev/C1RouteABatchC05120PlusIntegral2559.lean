import ConnesWeilRH.Dev.C1RouteABatchC05120PlusAssembly2559
import ConnesWeilRH.Dev.C1RouteABatchValueN05121Plus2559
import ConnesWeilRH.Dev.C1RouteABatchValueN05120Plus2559

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def batchC05120PlusCellP000Charge2559 : ℝ := ((1947669566259 : ℝ) /
        1000000)

theorem batchC05120PlusCellP000ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ + baseCoefficientError2540 ⟨0, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨0, by omega⟩ ≤ batchC05120PlusCellP000Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨0, by omega⟩ ≤ (((88488590528 * 10^40
        + 2161260874684443202365996215051332303539) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP000NormUpper2559, batchC05120PlusRightP000NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP000Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ +
      baseCoefficientError2540 ⟨0, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP000Charge2559]

noncomputable def batchC05120PlusCellP001Charge2559 : ℝ := ((27377284241 : ℝ) /
        125000)

theorem batchC05120PlusCellP001ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ + baseCoefficientError2540 ⟨1, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨1, by omega⟩ ≤ batchC05120PlusCellP001Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨1, by omega⟩ ≤ (((87808655345 * 10^40
        + 1406819854922359114343240545084058298549) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP001NormUpper2559, batchC05120PlusRightP001NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP001Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ +
      baseCoefficientError2540 ⟨1, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP001Charge2559]

noncomputable def batchC05120PlusCellP002Charge2559 : ℝ := ((121716002293 : ℝ) /
        1000000)

theorem batchC05120PlusCellP002ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ + baseCoefficientError2540 ⟨2, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨2, by omega⟩ ≤ batchC05120PlusCellP002Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨2, by omega⟩ ≤ (((10932102145 * 10^40
        + 3632009956196694879125110936411928519759) : ℝ) /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP002NormUpper2559, batchC05120PlusRightP002NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP002Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ +
      baseCoefficientError2540 ⟨2, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP002Charge2559]

noncomputable def batchC05120PlusCellP003Charge2559 : ℝ := ((30490109079 : ℝ) /
        500000)

theorem batchC05120PlusCellP003ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ + baseCoefficientError2540 ⟨3, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨3, by omega⟩ ≤ batchC05120PlusCellP003Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨3, by omega⟩ ≤ (((21815029697 * 10^40
        + 1461290390830746110017837475138300898279) : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP003NormUpper2559, batchC05120PlusRightP003NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP003Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ +
      baseCoefficientError2540 ⟨3, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP003Charge2559]

noncomputable def batchC05120PlusCellP004Charge2559 : ℝ := ((63674439 : ℝ) /
        1000000)

theorem batchC05120PlusCellP004ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ + baseCoefficientError2540 ⟨4, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨4, by omega⟩ ≤ batchC05120PlusCellP004Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨4, by omega⟩ ≤ (((85100819 * 10^40
        + 3480975091278270551529880582860657407561) : ℝ) /
        (14615016373309029 * 10^40
        + 1820368483271628301965593254297600000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP004NormUpper2559, batchC05120PlusRightP004NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP004Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ +
      baseCoefficientError2540 ⟨4, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP004Charge2559]

noncomputable def batchC05120PlusCellP005Charge2559 : ℝ := ((32657423 : ℝ) /
        1000000)

theorem batchC05120PlusCellP005ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ + baseCoefficientError2540 ⟨5, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨5, by omega⟩ ≤ batchC05120PlusCellP005Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨5, by omega⟩ ≤ (((7900146 * 10^40
        + 908622505524847251470503961784046322191) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP005NormUpper2559, batchC05120PlusRightP005NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP005Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ +
      baseCoefficientError2540 ⟨5, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP005Charge2559]

noncomputable def batchC05120PlusCellP006Charge2559 : ℝ := ((8544609 : ℝ) /
        1000000)

theorem batchC05120PlusCellP006ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ + baseCoefficientError2540 ⟨6, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨6, by omega⟩ ≤ batchC05120PlusCellP006Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨6, by omega⟩ ≤ (((1935733 * 10^40
        + 2132028338826533264715218528719676500303) : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP006NormUpper2559, batchC05120PlusRightP006NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP006Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ +
      baseCoefficientError2540 ⟨6, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP006Charge2559]

noncomputable def batchC05120PlusCellP007Charge2559 : ℝ := ((653917 : ℝ) /
        1000000)

theorem batchC05120PlusCellP007ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ + baseCoefficientError2540 ⟨7, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨7, by omega⟩ ≤ batchC05120PlusCellP007Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨7, by omega⟩ ≤ (((130914 * 10^40
        + 584131862909226827565916000150479263053) : ℝ) /
        (467680523945888933 * 10^40
        + 8251791464692105662898984137523200000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP007NormUpper2559, batchC05120PlusRightP007NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP007Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ +
      baseCoefficientError2540 ⟨7, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP007Charge2559]

noncomputable def batchC05120PlusCellP008Charge2559 : ℝ := ((312186981 : ℝ) /
        100000)

theorem batchC05120PlusCellP008ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ + baseCoefficientError2540 ⟨8, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨8, by omega⟩ ≤ batchC05120PlusCellP008Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨8, by omega⟩ ≤ (((1094578937 * 10^40
        + 3615749736338861273183531362602720238399) : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP008NormUpper2559, batchC05120PlusRightP008NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP008Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ +
      baseCoefficientError2540 ⟨8, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP008Charge2559]

noncomputable def batchC05120PlusCellP009Charge2559 : ℝ := ((1766538319 : ℝ) /
        200000)

theorem batchC05120PlusCellP009ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ + baseCoefficientError2540 ⟨9, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨9, by omega⟩ ≤ batchC05120PlusCellP009Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨9, by omega⟩ ≤ (((6886067586 * 10^40
        + 5210044499655612326590735404774778672963) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP009NormUpper2559, batchC05120PlusRightP009NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP009Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ +
      baseCoefficientError2540 ⟨9, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP009Charge2559]

noncomputable def batchC05120PlusCellP010Charge2559 : ℝ := ((9355127269 : ℝ) /
        1000000)

theorem batchC05120PlusCellP010ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ + baseCoefficientError2540 ⟨10, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨10, by omega⟩ ≤ batchC05120PlusCellP010Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨10, by omega⟩ ≤ (((11483511862 * 10^40
        + 5905757783573768867313931023933343640241) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP010NormUpper2559, batchC05120PlusRightP010NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP010Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ +
      baseCoefficientError2540 ⟨10, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP010Charge2559]

noncomputable def batchC05120PlusCellP011Charge2559 : ℝ := ((9936491747 : ℝ) /
        1000000)

theorem batchC05120PlusCellP011ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ + baseCoefficientError2540 ⟨11, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨11, by omega⟩ ≤ batchC05120PlusCellP011Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨11, by omega⟩ ≤ (((30981891679 * 10^40
        + 4449987756158009726995561353918564025993) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP011NormUpper2559, batchC05120PlusRightP011NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP011Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ +
      baseCoefficientError2540 ⟨11, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP011Charge2559]

noncomputable def batchC05120PlusCellP012Charge2559 : ℝ := ((20457605871 : ℝ) /
        1000000)

theorem batchC05120PlusCellP012ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ + baseCoefficientError2540 ⟨12, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨12, by omega⟩ ≤ batchC05120PlusCellP012Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨12, by omega⟩ ≤ (((5135291475 * 10^40
        + 1679666280356380996560277306208190711707) : ℝ) /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP012NormUpper2559, batchC05120PlusRightP012NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP012Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ +
      baseCoefficientError2540 ⟨12, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP012Charge2559]

noncomputable def batchC05120PlusCellP013Charge2559 : ℝ := ((10557209539 : ℝ) /
        1000000)

theorem batchC05120PlusCellP013ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ + baseCoefficientError2540 ⟨13, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨13, by omega⟩ ≤ batchC05120PlusCellP013Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨13, by omega⟩ ≤ (((52038568652 * 10^40
        + 4307837102998603673405218863958771123297) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP013NormUpper2559, batchC05120PlusRightP013NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP013Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ +
      baseCoefficientError2540 ⟨13, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP013Charge2559]

noncomputable def batchC05120PlusCellP014Charge2559 : ℝ := ((174415136661 : ℝ) /
        250000)

theorem batchC05120PlusCellP014ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ + baseCoefficientError2540 ⟨14, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨14, by omega⟩ ≤ batchC05120PlusCellP014Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨14, by omega⟩ ≤ (((38627813963 * 10^40
        + 3683798759009039299387641210098290956201) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP014NormUpper2559, batchC05120PlusRightP014NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP014Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ +
      baseCoefficientError2540 ⟨14, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP014Charge2559]

noncomputable def batchC05120PlusCellP015Charge2559 : ℝ := ((900270416261 : ℝ) /
        1000000)

theorem batchC05120PlusCellP015ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ + baseCoefficientError2540 ⟨15, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨15, by omega⟩ ≤ batchC05120PlusCellP015Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨15, by omega⟩ ≤ (((99677548001 * 10^40
        + 9531439287716662673479570439654357149141) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP015NormUpper2559, batchC05120PlusRightP015NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP015Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ +
      baseCoefficientError2540 ⟨15, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP015Charge2559]

noncomputable def batchC05120PlusCellP016Charge2559 : ℝ := ((18688661671 : ℝ) /
        1000000)

theorem batchC05120PlusCellP016ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ + baseCoefficientError2540 ⟨16, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨16, by omega⟩ ≤ batchC05120PlusCellP016Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨16, by omega⟩ ≤ (((59182595050 * 10^40
        + 8801991785052588232992450503962044255089) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP016NormUpper2559, batchC05120PlusRightP016NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP016Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ +
      baseCoefficientError2540 ⟨16, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP016Charge2559]

noncomputable def batchC05120PlusCellP017Charge2559 : ℝ := ((15998097639 : ℝ) /
        200000)

theorem batchC05120PlusCellP017ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ + baseCoefficientError2540 ⟨17, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨17, by omega⟩ ≤ batchC05120PlusCellP017Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨17, by omega⟩ ≤ (((161156843125 * 10^40
        + 8433802974386617399696585914395457329803) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP017NormUpper2559, batchC05120PlusRightP017NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP017Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ +
      baseCoefficientError2540 ⟨17, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP017Charge2559]

noncomputable def batchC05120PlusCellP018Charge2559 : ℝ := ((31021789117 : ℝ) /
        1000000)

theorem batchC05120PlusCellP018ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ + baseCoefficientError2540 ⟨18, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨18, by omega⟩ ≤ batchC05120PlusCellP018Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨18, by omega⟩ ≤ (((1404112393 * 10^40
        + 5770991697407368179047595849360576000903) : ℝ) /
        (116920130986472233 * 10^40
        + 4562947866173026415724746034380800000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP018NormUpper2559, batchC05120PlusRightP018NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP018Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ +
      baseCoefficientError2540 ⟨18, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP018Charge2559]

noncomputable def batchC05120PlusCellP019Charge2559 : ℝ := ((24444253401 : ℝ) /
        250000)

theorem batchC05120PlusCellP019ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ + baseCoefficientError2540 ⟨19, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨19, by omega⟩ ≤ batchC05120PlusCellP019Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨19, by omega⟩ ≤ (((216855719688 * 10^40
        + 2005291329201358511347270382528862092751) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP019NormUpper2559, batchC05120PlusRightP019NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP019Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ +
      baseCoefficientError2540 ⟨19, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP019Charge2559]

noncomputable def batchC05120PlusCellP020Charge2559 : ℝ := ((22484237157 : ℝ) /
        200000)

theorem batchC05120PlusCellP020ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ + baseCoefficientError2540 ⟨20, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨20, by omega⟩ ≤ batchC05120PlusCellP020Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨20, by omega⟩ ≤ (((52551451698 * 10^40
        + 7911268737923481841333876084796815925499) : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP020NormUpper2559, batchC05120PlusRightP020NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP020Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ +
      baseCoefficientError2540 ⟨20, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP020Charge2559]

noncomputable def batchC05120PlusCellP021Charge2559 : ℝ := ((9404459261 : ℝ) /
        250000)

theorem batchC05120PlusCellP021ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ + baseCoefficientError2540 ⟨21, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨21, by omega⟩ ≤ batchC05120PlusCellP021Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨21, by omega⟩ ≤ (((61150865557 * 10^40
        + 9108580562416397831947116500056833199867) : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP021NormUpper2559, batchC05120PlusRightP021NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP021Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ +
      baseCoefficientError2540 ⟨21, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP021Charge2559]

noncomputable def batchC05120PlusCellP022Charge2559 : ℝ := ((153882180581 : ℝ) /
        1000000)

theorem batchC05120PlusCellP022ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ + baseCoefficientError2540 ⟨22, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨22, by omega⟩ ≤ batchC05120PlusCellP022Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨22, by omega⟩ ≤ (((20593448401 * 10^40
        + 8504989784743433860170107824698102762343) : ℝ) /
        (935361047891777867 * 10^40
        + 6503582929384211325797968275046400000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP022NormUpper2559, batchC05120PlusRightP022NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP022Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ +
      baseCoefficientError2540 ⟨22, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP022Charge2559]

noncomputable def batchC05120PlusCellP023Charge2559 : ℝ := ((191118680517 : ℝ) /
        1000000)

theorem batchC05120PlusCellP023ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ + baseCoefficientError2540 ⟨23, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨23, by omega⟩ ≤ batchC05120PlusCellP023Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨23, by omega⟩ ≤ (((25303795300 * 10^40
        + 4107990433975965859867590716434191204343) : ℝ) /
        (935361047891777867 * 10^40
        + 6503582929384211325797968275046400000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP023NormUpper2559, batchC05120PlusRightP023NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP023Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ +
      baseCoefficientError2540 ⟨23, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP023Charge2559]

noncomputable def batchC05120PlusCellP024Charge2559 : ℝ := ((43730538947 : ℝ) /
        1000000)

theorem batchC05120PlusCellP024ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ + baseCoefficientError2540 ⟨24, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨24, by omega⟩ ≤ batchC05120PlusCellP024Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨24, by omega⟩ ≤ (((443094843360 * 10^40
        + 1642245804745254927960024555916971630441) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP024NormUpper2559, batchC05120PlusRightP024NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP024Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ +
      baseCoefficientError2540 ⟨24, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP024Charge2559]

noncomputable def batchC05120PlusCellP025Charge2559 : ℝ := ((911927023 : ℝ) /
        4000)

theorem batchC05120PlusCellP025ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ + baseCoefficientError2540 ⟨25, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨25, by omega⟩ ≤ batchC05120PlusCellP025Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨25, by omega⟩ ≤ (((15449743909 * 10^40
        + 6969753670983620259504231334643659166981) : ℝ) /
        (467680523945888933 * 10^40
        + 8251791464692105662898984137523200000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP025NormUpper2559, batchC05120PlusRightP025NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP025Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ +
      baseCoefficientError2540 ⟨25, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP025Charge2559]

noncomputable def batchC05120PlusCellP026Charge2559 : ℝ := ((19641784593 : ℝ) /
        125000)

theorem batchC05120PlusCellP026ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ + baseCoefficientError2540 ⟨26, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨26, by omega⟩ ≤ batchC05120PlusCellP026Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨26, by omega⟩ ≤ (((4406558354 * 10^40
        + 6059259865533368129950169323383143541723) : ℝ) /
        (119726214130147567 * 10^40
        + 592458614961179049702139939205939200000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP026NormUpper2559, batchC05120PlusRightP026NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP026Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ +
      baseCoefficientError2540 ⟨26, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP026Charge2559]

noncomputable def batchC05120PlusCellP027Charge2559 : ℝ := ((670720226263 : ℝ) /
        1000000)

theorem batchC05120PlusCellP027ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ + baseCoefficientError2540 ⟨27, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨27, by omega⟩ ≤ batchC05120PlusCellP027Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨27, by omega⟩ ≤ (((127940547341 * 10^40
        + 8289084400335869708686555330484252759019) : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP027NormUpper2559, batchC05120PlusRightP027NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP027Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ +
      baseCoefficientError2540 ⟨27, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP027Charge2559]

noncomputable def batchC05120PlusCellP028Charge2559 : ℝ := ((74805499663 : ℝ) /
        125000)

theorem batchC05120PlusCellP028ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ + baseCoefficientError2540 ⟨28, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨28, by omega⟩ ≤ batchC05120PlusCellP028Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨28, by omega⟩ ≤ (((677419049630 * 10^40
        + 1313430205894039018134949923608702047131) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP028NormUpper2559, batchC05120PlusRightP028NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP028Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ +
      baseCoefficientError2540 ⟨28, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP028Charge2559]

noncomputable def batchC05120PlusCellP029Charge2559 : ℝ := ((720219232169 : ℝ) /
        1000000)

theorem batchC05120PlusCellP029ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ + baseCoefficientError2540 ⟨29, by omega⟩) *
      batchC05120PlusThirdCell2559 ⟨29, by omega⟩ ≤ batchC05120PlusCellP029Charge2559 := by
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
  have ht : batchC05120PlusThirdCell2559 ⟨29, by omega⟩ ≤ (((73768830288 * 10^40
        + 5116632116847683841671780341814500148513) : ℝ) /
        (1496577676626844588 * 10^40
        + 2405732687014738121276749240074240000000)) := by
    unfold batchC05120PlusThirdCell2559
    norm_num [batchC05120PlusLeftNormUpper2559, batchC05120PlusRightNormUpper2559,
      batchC05120PlusLeftP029NormUpper2559, batchC05120PlusRightP029NormUpper2559,
      batchC05120PlusFourthUpper2559, batchC05120PlusFourthP029Upper2559,
      batchN05120PlusPosition2559, batchN05121PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ +
      baseCoefficientError2540 ⟨29, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05120PlusCellP029Charge2559]

noncomputable def batchC05120PlusCellCharge2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05120PlusCellP000Charge2559
  | 1 => batchC05120PlusCellP001Charge2559
  | 2 => batchC05120PlusCellP002Charge2559
  | 3 => batchC05120PlusCellP003Charge2559
  | 4 => batchC05120PlusCellP004Charge2559
  | 5 => batchC05120PlusCellP005Charge2559
  | 6 => batchC05120PlusCellP006Charge2559
  | 7 => batchC05120PlusCellP007Charge2559
  | 8 => batchC05120PlusCellP008Charge2559
  | 9 => batchC05120PlusCellP009Charge2559
  | 10 => batchC05120PlusCellP010Charge2559
  | 11 => batchC05120PlusCellP011Charge2559
  | 12 => batchC05120PlusCellP012Charge2559
  | 13 => batchC05120PlusCellP013Charge2559
  | 14 => batchC05120PlusCellP014Charge2559
  | 15 => batchC05120PlusCellP015Charge2559
  | 16 => batchC05120PlusCellP016Charge2559
  | 17 => batchC05120PlusCellP017Charge2559
  | 18 => batchC05120PlusCellP018Charge2559
  | 19 => batchC05120PlusCellP019Charge2559
  | 20 => batchC05120PlusCellP020Charge2559
  | 21 => batchC05120PlusCellP021Charge2559
  | 22 => batchC05120PlusCellP022Charge2559
  | 23 => batchC05120PlusCellP023Charge2559
  | 24 => batchC05120PlusCellP024Charge2559
  | 25 => batchC05120PlusCellP025Charge2559
  | 26 => batchC05120PlusCellP026Charge2559
  | 27 => batchC05120PlusCellP027Charge2559
  | 28 => batchC05120PlusCellP028Charge2559
  | 29 => batchC05120PlusCellP029Charge2559
  | _ => 0

theorem batchC05120PlusCellChargeBound2559 (i : Fin 30) :
    (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC05120PlusThirdCell2559 i ≤ batchC05120PlusCellCharge2559 i := by
  fin_cases i
  · exact batchC05120PlusCellP000ChargeBound2559
  · exact batchC05120PlusCellP001ChargeBound2559
  · exact batchC05120PlusCellP002ChargeBound2559
  · exact batchC05120PlusCellP003ChargeBound2559
  · exact batchC05120PlusCellP004ChargeBound2559
  · exact batchC05120PlusCellP005ChargeBound2559
  · exact batchC05120PlusCellP006ChargeBound2559
  · exact batchC05120PlusCellP007ChargeBound2559
  · exact batchC05120PlusCellP008ChargeBound2559
  · exact batchC05120PlusCellP009ChargeBound2559
  · exact batchC05120PlusCellP010ChargeBound2559
  · exact batchC05120PlusCellP011ChargeBound2559
  · exact batchC05120PlusCellP012ChargeBound2559
  · exact batchC05120PlusCellP013ChargeBound2559
  · exact batchC05120PlusCellP014ChargeBound2559
  · exact batchC05120PlusCellP015ChargeBound2559
  · exact batchC05120PlusCellP016ChargeBound2559
  · exact batchC05120PlusCellP017ChargeBound2559
  · exact batchC05120PlusCellP018ChargeBound2559
  · exact batchC05120PlusCellP019ChargeBound2559
  · exact batchC05120PlusCellP020ChargeBound2559
  · exact batchC05120PlusCellP021ChargeBound2559
  · exact batchC05120PlusCellP022ChargeBound2559
  · exact batchC05120PlusCellP023ChargeBound2559
  · exact batchC05120PlusCellP024ChargeBound2559
  · exact batchC05120PlusCellP025ChargeBound2559
  · exact batchC05120PlusCellP026ChargeBound2559
  · exact batchC05120PlusCellP027ChargeBound2559
  · exact batchC05120PlusCellP028ChargeBound2559
  · exact batchC05120PlusCellP029ChargeBound2559

noncomputable def batchC05120PlusCellThirdUpper2559 : ℝ := ((7150429413453 : ℝ) /
        1000000)

noncomputable def batchC05120PlusCellCurvatureUpper2559 : ℝ := ((28746319 : ℝ) /
        800)

noncomputable def batchC05120PlusCellIntegralUpper2559 : ℝ := ((8830540631 : ℝ) /
        500000000000)

theorem batchC05120PlusCellThirdBound2559 : batchC05120PlusThirdAggregate2559 ≤
    batchC05120PlusCellThirdUpper2559 := by
  have h : batchC05120PlusThirdAggregate2559 ≤ ∑ i : Fin 30, batchC05120PlusCellCharge2559 i :=
    Finset.sum_le_sum (fun i _ => batchC05120PlusCellChargeBound2559 i)
  apply h.trans
  rw [sum30_chain2541]
  norm_num [batchC05120PlusCellCharge2559, batchC05120PlusCellThirdUpper2559,
      batchC05120PlusCellP000Charge2559, batchC05120PlusCellP001Charge2559,
      batchC05120PlusCellP002Charge2559, batchC05120PlusCellP003Charge2559,
          batchC05120PlusCellP004Charge2559, batchC05120PlusCellP005Charge2559,
      batchC05120PlusCellP006Charge2559, batchC05120PlusCellP007Charge2559,
          batchC05120PlusCellP008Charge2559, batchC05120PlusCellP009Charge2559,
      batchC05120PlusCellP010Charge2559, batchC05120PlusCellP011Charge2559,
          batchC05120PlusCellP012Charge2559, batchC05120PlusCellP013Charge2559,
      batchC05120PlusCellP014Charge2559, batchC05120PlusCellP015Charge2559,
          batchC05120PlusCellP016Charge2559, batchC05120PlusCellP017Charge2559,
      batchC05120PlusCellP018Charge2559, batchC05120PlusCellP019Charge2559,
          batchC05120PlusCellP020Charge2559, batchC05120PlusCellP021Charge2559,
      batchC05120PlusCellP022Charge2559, batchC05120PlusCellP023Charge2559,
          batchC05120PlusCellP024Charge2559, batchC05120PlusCellP025Charge2559,
      batchC05120PlusCellP026Charge2559, batchC05120PlusCellP027Charge2559,
          batchC05120PlusCellP028Charge2559, batchC05120PlusCellP029Charge2559]

theorem batchC05120PlusCellCurvatureBound2559 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN05120PlusPosition2559 batchN05121PlusPosition2559 ≤
        batchC05120PlusCellCurvatureUpper2559 := by
  have h := batchC05120PlusCurvature_bound2559
  have ht := batchC05120PlusCellThirdBound2559
  norm_num [batchC05120PlusSignedMidpointUpper2559, batchC05120PlusCellThirdUpper2559,
      batchC05120PlusCellCurvatureUpper2559,
    batchN05120PlusPosition2559, batchN05121PlusPosition2559] at *
  linarith

theorem batchC05120PlusCellIntegralBound2559 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤ baseCoefficientError2540 i) :
    (∫ x in batchN05120PlusPosition2559..batchN05121PlusPosition2559,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤
        batchC05120PlusCellIntegralUpper2559 := by
  have h := weightedPhysical2539_norm_integral_le_signed_cell (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541 hcoeff
    (a := batchN05120PlusPosition2559) (b := batchN05121PlusPosition2559)
    (by norm_num [batchN05120PlusPosition2559, batchN05121PlusPosition2559])
  have hl := batchValueN05120PlusSigned_le2559
  have hr := batchValueN05121PlusSigned_le2559
  have hc := batchC05120PlusCellCurvatureBound2559
  have hleft : batchValueN05120PlusPosition2559 = batchN05120PlusPosition2559 := by
    norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559]
  have hright : batchValueN05121PlusPosition2559 = batchN05121PlusPosition2559 := by
    norm_num [batchValueN05121PlusPosition2559, batchN05121PlusPosition2559]
  rw [hleft] at hl
  rw [hright] at hr
  norm_num [batchN05120PlusPosition2559, batchN05121PlusPosition2559,
      batchValueN05120PlusUpper2559,
    batchValueN05121PlusUpper2559, batchC05120PlusCellCurvatureUpper2559,
        batchC05120PlusCellIntegralUpper2559] at *
  linarith

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05120PlusCellChargeBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusCellThirdBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusCellCurvatureBound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusCellIntegralBound2559
