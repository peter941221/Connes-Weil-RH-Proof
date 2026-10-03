import ConnesWeilRH.Dev.C1RouteABatchC05119PlusAssembly2559
import ConnesWeilRH.Dev.C1RouteABatchValueN05120Plus2559
import ConnesWeilRH.Dev.C1RouteABatchValueN05119Plus2559

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def batchC05119PlusCellP000Charge2559 : ℝ := ((389291654203 : ℝ) /
        200000)

theorem batchC05119PlusCellP000ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ + baseCoefficientError2540 ⟨0, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨0, by omega⟩ ≤ batchC05119PlusCellP000Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨0, by omega⟩ ≤ (((44216778838 * 10^40
        + 6452368291154697680068824017072711525127) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP000NormUpper2559, batchC05119PlusRightP000NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP000Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ +
      baseCoefficientError2540 ⟨0, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP000Charge2559]

noncomputable def batchC05119PlusCellP001Charge2559 : ℝ := ((54720103697 : ℝ) /
        250000)

theorem batchC05119PlusCellP001ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ + baseCoefficientError2540 ⟨1, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨1, by omega⟩ ≤ batchC05119PlusCellP001Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨1, by omega⟩ ≤ (((87753384953 * 10^40
        + 9267765681712627335058868757667833254891) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP001NormUpper2559, batchC05119PlusRightP001NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP001Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ +
      baseCoefficientError2540 ⟨1, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP001Charge2559]

noncomputable def batchC05119PlusCellP002Charge2559 : ℝ := ((121638905987 : ℝ) /
        1000000)

theorem batchC05119PlusCellP002ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ + baseCoefficientError2540 ⟨2, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨2, by omega⟩ ≤ batchC05119PlusCellP002Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨2, by omega⟩ ≤ (((17480284203 * 10^40
        + 2244724214363918736064982973591113438109) : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP002NormUpper2559, batchC05119PlusRightP002NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP002Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ +
      baseCoefficientError2540 ⟨2, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP002Charge2559]

noncomputable def batchC05119PlusCellP003Charge2559 : ℝ := ((15235363947 : ℝ) /
        250000)

theorem batchC05119PlusCellP003ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ + baseCoefficientError2540 ⟨3, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨3, by omega⟩ ≤ batchC05119PlusCellP003Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨3, by omega⟩ ≤ (((87204651472 * 10^40
        + 4102163368781180553165534774462529035563) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP003NormUpper2559, batchC05119PlusRightP003NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP003Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ +
      baseCoefficientError2540 ⟨3, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP003Charge2559]

noncomputable def batchC05119PlusCellP004Charge2559 : ℝ := ((31816939 : ℝ) /
        500000)

theorem batchC05119PlusCellP004ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ + baseCoefficientError2540 ⟨4, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨4, by omega⟩ ≤ batchC05119PlusCellP004Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨4, by omega⟩ ≤ (((87087729109 * 10^40
        + 2359762910065289989706093716562022033871) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP004NormUpper2559, batchC05119PlusRightP004NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP004Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ +
      baseCoefficientError2540 ⟨4, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP004Charge2559]

noncomputable def batchC05119PlusCellP005Charge2559 : ℝ := ((33203211 : ℝ) /
        1000000)

theorem batchC05119PlusCellP005ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ + baseCoefficientError2540 ⟨5, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨5, by omega⟩ ≤ batchC05119PlusCellP005Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨5, by omega⟩ ≤ (((2008044 * 10^40
        + 3645630448099263475951359303012867619461) : ℝ) /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP005NormUpper2559, batchC05119PlusRightP005NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP005Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ +
      baseCoefficientError2540 ⟨5, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP005Charge2559]

noncomputable def batchC05119PlusCellP006Charge2559 : ℝ := ((2152837 : ℝ) /
        250000)

theorem batchC05119PlusCellP006ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ + baseCoefficientError2540 ⟨6, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨6, by omega⟩ ≤ batchC05119PlusCellP006Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨6, by omega⟩ ≤ (((7803410 * 10^40
        + 1909556926316514872218786148211072192157) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP006NormUpper2559, batchC05119PlusRightP006NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP006Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ +
      baseCoefficientError2540 ⟨6, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP006Charge2559]

noncomputable def batchC05119PlusCellP007Charge2559 : ℝ := ((32821 : ℝ) /
        50000)

theorem batchC05119PlusCellP007ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ + baseCoefficientError2540 ⟨7, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨7, by omega⟩ ≤ batchC05119PlusCellP007Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨7, by omega⟩ ≤ (((2102641 * 10^40
        + 797498377239006774288389092900634504963) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP007NormUpper2559, batchC05119PlusRightP007NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP007Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ +
      baseCoefficientError2540 ⟨7, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP007Charge2559]

noncomputable def batchC05119PlusCellP008Charge2559 : ℝ := ((624008253 : ℝ) /
        200000)

theorem batchC05119PlusCellP008ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ + baseCoefficientError2540 ⟨8, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨8, by omega⟩ ≤ batchC05119PlusCellP008Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨8, by omega⟩ ≤ (((4375751277 * 10^40
        + 8120739075740116929128560311377092868509) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP008NormUpper2559, batchC05119PlusRightP008NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP008Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ +
      baseCoefficientError2540 ⟨8, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP008Charge2559]

noncomputable def batchC05119PlusCellP009Charge2559 : ℝ := ((2206825003 : ℝ) /
        250000)

theorem batchC05119PlusCellP009ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ + baseCoefficientError2540 ⟨9, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨9, by omega⟩ ≤ batchC05119PlusCellP009Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨9, by omega⟩ ≤ (((1376372849 * 10^40
        + 3753442559128694276095888939304716198619) : ℝ) /
        (1496577676626844588 * 10^40
        + 2405732687014738121276749240074240000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP009NormUpper2559, batchC05119PlusRightP009NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP009Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ +
      baseCoefficientError2540 ⟨9, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP009Charge2559]

noncomputable def batchC05119PlusCellP010Charge2559 : ℝ := ((9349353473 : ℝ) /
        1000000)

theorem batchC05119PlusCellP010ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ + baseCoefficientError2540 ⟨10, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨10, by omega⟩ ≤ batchC05119PlusCellP010Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨10, by omega⟩ ≤ (((22952848940 * 10^40
        + 7753358768220873169848630008024159601841) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP010NormUpper2559, batchC05119PlusRightP010NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP010Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ +
      baseCoefficientError2540 ⟨10, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP010Charge2559]

noncomputable def batchC05119PlusCellP011Charge2559 : ℝ := ((1986065689 : ℝ) /
        200000)

theorem batchC05119PlusCellP011ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ + baseCoefficientError2540 ⟨11, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨11, by omega⟩ ≤ batchC05119PlusCellP011Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨11, by omega⟩ ≤ (((1238506982 * 10^40
        + 4404766087142273789733548254936250132619) : ℝ) /
        (598631070650737835 * 10^40
        + 2962293074805895248510699696029696000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP011NormUpper2559, batchC05119PlusRightP011NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP011Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ +
      baseCoefficientError2540 ⟨11, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP011Charge2559]

noncomputable def batchC05119PlusCellP012Charge2559 : ℝ := ((20444866887 : ℝ) /
        1000000)

theorem batchC05119PlusCellP012ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ + baseCoefficientError2540 ⟨12, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨12, by omega⟩ ≤ batchC05119PlusCellP012Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨12, by omega⟩ ≤ (((10264187441 * 10^40
        + 9109408108191561636262893598347271386677) : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP012NormUpper2559, batchC05119PlusRightP012NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP012Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ +
      baseCoefficientError2540 ⟨12, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP012Charge2559]

noncomputable def batchC05119PlusCellP013Charge2559 : ℝ := ((2110123453 : ℝ) /
        200000)

theorem batchC05119PlusCellP013ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ + baseCoefficientError2540 ⟨13, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨13, by omega⟩ ≤ batchC05119PlusCellP013Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨13, by omega⟩ ≤ (((52006074033 * 10^40
        + 5751678594211918224342083239171195243867) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP013NormUpper2559, batchC05119PlusRightP013NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP013Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ +
      baseCoefficientError2540 ⟨13, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP013Charge2559]

noncomputable def batchC05119PlusCellP014Charge2559 : ℝ := ((174305811791 : ℝ) /
        250000)

theorem batchC05119PlusCellP014ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ + baseCoefficientError2540 ⟨14, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨14, by omega⟩ ≤ batchC05119PlusCellP014Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨14, by omega⟩ ≤ (((4825450215 * 10^40
        + 7152306046897881649972517983897373838063) : ℝ) /
        (935361047891777867 * 10^40
        + 6503582929384211325797968275046400000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP014NormUpper2559, batchC05119PlusRightP014NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP014Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ +
      baseCoefficientError2540 ⟨14, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP014Charge2559]

noncomputable def batchC05119PlusCellP015Charge2559 : ℝ := ((89970499943 : ℝ) /
        100000)

theorem batchC05119PlusCellP015ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ + baseCoefficientError2540 ⟨15, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨15, by omega⟩ ≤ batchC05119PlusCellP015Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨15, by omega⟩ ≤ (((49807472648 * 10^40
        + 4789601556975117799114900100629675590179) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP015NormUpper2559, batchC05119PlusRightP015NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP015Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ +
      baseCoefficientError2540 ⟨15, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP015Charge2559]

noncomputable def batchC05119PlusCellP016Charge2559 : ℝ := ((1167306909 : ℝ) /
        62500)

theorem batchC05119PlusCellP016ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ + baseCoefficientError2540 ⟨16, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨16, by omega⟩ ≤ batchC05119PlusCellP016Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨16, by omega⟩ ≤ (((11829076399 * 10^40
        + 1231511153513479312747059931461112466409) : ℝ) /
        (1496577676626844588 * 10^40
        + 2405732687014738121276749240074240000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP016NormUpper2559, batchC05119PlusRightP016NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP016Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ +
      baseCoefficientError2540 ⟨16, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP016Charge2559]

noncomputable def batchC05119PlusCellP017Charge2559 : ℝ := ((79940101239 : ℝ) /
        1000000)

theorem batchC05119PlusCellP017ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ + baseCoefficientError2540 ⟨17, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨17, by omega⟩ ≤ batchC05119PlusCellP017Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨17, by omega⟩ ≤ (((32211065704 * 10^40
        + 3995747697671134119867481752995639996709) : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP017NormUpper2559, batchC05119PlusRightP017NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP017Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ +
      baseCoefficientError2540 ⟨17, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP017Charge2559]

noncomputable def batchC05119PlusCellP018Charge2559 : ℝ := ((31002237319 : ℝ) /
        1000000)

theorem batchC05119PlusCellP018ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ + baseCoefficientError2540 ⟨18, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨18, by omega⟩ ≤ batchC05119PlusCellP018Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨18, by omega⟩ ≤ (((44903277998 * 10^40
        + 4324595953093792890531750627603144712131) : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP018NormUpper2559, batchC05119PlusRightP018NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP018Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ +
      baseCoefficientError2540 ⟨18, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP018Charge2559]

noncomputable def batchC05119PlusCellP019Charge2559 : ℝ := ((97715335279 : ℝ) /
        1000000)

theorem batchC05119PlusCellP019ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ + baseCoefficientError2540 ⟨19, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨19, by omega⟩ ≤ batchC05119PlusCellP019Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨19, by omega⟩ ≤ (((108359462901 * 10^40
        + 3026752455819041543504483113526077229627) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP019NormUpper2559, batchC05119PlusRightP019NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP019Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ +
      baseCoefficientError2540 ⟨19, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP019Charge2559]

noncomputable def batchC05119PlusCellP020Charge2559 : ℝ := ((56175107123 : ℝ) /
        500000)

theorem batchC05119PlusCellP020ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ + baseCoefficientError2540 ⟨20, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨20, by omega⟩ ≤ batchC05119PlusCellP020Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨20, by omega⟩ ≤ (((262591379731 * 10^40
        + 2543019934528126154587011904532594432331) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP020NormUpper2559, batchC05119PlusRightP020NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP020Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ +
      baseCoefficientError2540 ⟨20, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP020Charge2559]

noncomputable def batchC05119PlusCellP021Charge2559 : ℝ := ((2349629733 : ℝ) /
        62500)

theorem batchC05119PlusCellP021ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ + baseCoefficientError2540 ⟨21, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨21, by omega⟩ ≤ batchC05119PlusCellP021Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨21, by omega⟩ ≤ (((152780599000 * 10^40
        + 227797535620115661937330069098347546413) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP021NormUpper2559, batchC05119PlusRightP021NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP021Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ +
      baseCoefficientError2540 ⟨21, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP021Charge2559]

noncomputable def batchC05119PlusCellP022Charge2559 : ℝ := ((3075699123 : ℝ) /
        20000)

theorem batchC05119PlusCellP022ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ + baseCoefficientError2540 ⟨22, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨22, by omega⟩ ≤ batchC05119PlusCellP022Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨22, by omega⟩ ≤ (((329286995803 * 10^40
        + 8233858230601155619437402384257799498493) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP022NormUpper2559, batchC05119PlusRightP022NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP022Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ +
      baseCoefficientError2540 ⟨22, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP022Charge2559]

noncomputable def batchC05119PlusCellP023Charge2559 : ℝ := ((190997852221 : ℝ) /
        1000000)

theorem batchC05119PlusCellP023ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ + baseCoefficientError2540 ⟨23, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨23, by omega⟩ ≤ batchC05119PlusCellP023Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨23, by omega⟩ ≤ (((202302382680 * 10^40
        + 6158802267156202043537129961558201835491) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP023NormUpper2559, batchC05119PlusRightP023NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP023Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ +
      baseCoefficientError2540 ⟨23, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP023Charge2559]

noncomputable def batchC05119PlusCellP024Charge2559 : ℝ := ((4370288473 : ℝ) /
        100000)

theorem batchC05119PlusCellP024ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ + baseCoefficientError2540 ⟨24, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨24, by omega⟩ ≤ batchC05119PlusCellP024Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨24, by omega⟩ ≤ (((221407320031 * 10^40
        + 5019716641005206248531644331317575978939) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP024NormUpper2559, batchC05119PlusRightP024NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP024Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ +
      baseCoefficientError2540 ⟨24, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP024Charge2559]

noncomputable def batchC05119PlusCellP025Charge2559 : ℝ := ((113918771569 : ℝ) /
        500000)

theorem batchC05119PlusCellP025ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ + baseCoefficientError2540 ⟨25, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨25, by omega⟩ ≤ batchC05119PlusCellP025Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨25, by omega⟩ ≤ (((61759883950 * 10^40
        + 5128479407468440706217528183021183843583) : ℝ) /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP025NormUpper2559, batchC05119PlusRightP025NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP025Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ +
      baseCoefficientError2540 ⟨25, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP025Charge2559]

noncomputable def batchC05119PlusCellP026Charge2559 : ℝ := ((31406970569 : ℝ) /
        200000)

theorem batchC05119PlusCellP026ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ + baseCoefficientError2540 ⟨26, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨26, by omega⟩ ≤ batchC05119PlusCellP026Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨26, by omega⟩ ≤ (((110094254593 * 10^40
        + 4316311457577738883855948653525181741079) : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP026NormUpper2559, batchC05119PlusRightP026NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP026Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ +
      baseCoefficientError2540 ⟨26, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP026Charge2559]

noncomputable def batchC05119PlusCellP027Charge2559 : ℝ := ((134059138853 : ℝ) /
        200000)

theorem batchC05119PlusCellP027ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ + baseCoefficientError2540 ⟨27, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨27, by omega⟩ ≤ batchC05119PlusCellP027Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨27, by omega⟩ ≤ (((639297837214 * 10^40
        + 6222845944519691918399431512359885840043) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP027NormUpper2559, batchC05119PlusRightP027NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP027Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ +
      baseCoefficientError2540 ⟨27, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP027Charge2559]

noncomputable def batchC05119PlusCellP028Charge2559 : ℝ := ((598065165771 : ℝ) /
        1000000)

theorem batchC05119PlusCellP028ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ + baseCoefficientError2540 ⟨28, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨28, by omega⟩ ≤ batchC05119PlusCellP028Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨28, by omega⟩ ≤ (((2644493065 * 10^40
        + 2869442331598999784107857156161230848947) : ℝ) /
        (58460065493236116 * 10^40
        + 7281473933086513207862373017190400000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP028NormUpper2559, batchC05119PlusRightP028NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP028Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ +
      baseCoefficientError2540 ⟨28, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP028Charge2559]

noncomputable def batchC05119PlusCellP029Charge2559 : ℝ := ((179940808357 : ℝ) /
        250000)

theorem batchC05119PlusCellP029ChargeBound2559 :
    (‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ + baseCoefficientError2540 ⟨29, by omega⟩) *
      batchC05119PlusThirdCell2559 ⟨29, by omega⟩ ≤ batchC05119PlusCellP029Charge2559 := by
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
  have ht : batchC05119PlusThirdCell2559 ⟨29, by omega⟩ ≤ (((73722124379 * 10^40
        + 7247699952771374831477388745500902357163) : ℝ) /
        (1496577676626844588 * 10^40
        + 2405732687014738121276749240074240000000)) := by
    unfold batchC05119PlusThirdCell2559
    norm_num [batchC05119PlusLeftNormUpper2559, batchC05119PlusRightNormUpper2559,
      batchC05119PlusLeftP029NormUpper2559, batchC05119PlusRightP029NormUpper2559,
      batchC05119PlusFourthUpper2559, batchC05119PlusFourthP029Upper2559,
      batchN05119PlusPosition2559, batchN05120PlusPosition2559]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ +
      baseCoefficientError2540 ⟨29, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC05119PlusCellP029Charge2559]

noncomputable def batchC05119PlusCellCharge2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05119PlusCellP000Charge2559
  | 1 => batchC05119PlusCellP001Charge2559
  | 2 => batchC05119PlusCellP002Charge2559
  | 3 => batchC05119PlusCellP003Charge2559
  | 4 => batchC05119PlusCellP004Charge2559
  | 5 => batchC05119PlusCellP005Charge2559
  | 6 => batchC05119PlusCellP006Charge2559
  | 7 => batchC05119PlusCellP007Charge2559
  | 8 => batchC05119PlusCellP008Charge2559
  | 9 => batchC05119PlusCellP009Charge2559
  | 10 => batchC05119PlusCellP010Charge2559
  | 11 => batchC05119PlusCellP011Charge2559
  | 12 => batchC05119PlusCellP012Charge2559
  | 13 => batchC05119PlusCellP013Charge2559
  | 14 => batchC05119PlusCellP014Charge2559
  | 15 => batchC05119PlusCellP015Charge2559
  | 16 => batchC05119PlusCellP016Charge2559
  | 17 => batchC05119PlusCellP017Charge2559
  | 18 => batchC05119PlusCellP018Charge2559
  | 19 => batchC05119PlusCellP019Charge2559
  | 20 => batchC05119PlusCellP020Charge2559
  | 21 => batchC05119PlusCellP021Charge2559
  | 22 => batchC05119PlusCellP022Charge2559
  | 23 => batchC05119PlusCellP023Charge2559
  | 24 => batchC05119PlusCellP024Charge2559
  | 25 => batchC05119PlusCellP025Charge2559
  | 26 => batchC05119PlusCellP026Charge2559
  | 27 => batchC05119PlusCellP027Charge2559
  | 28 => batchC05119PlusCellP028Charge2559
  | 29 => batchC05119PlusCellP029Charge2559
  | _ => 0

theorem batchC05119PlusCellChargeBound2559 (i : Fin 30) :
    (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC05119PlusThirdCell2559 i ≤ batchC05119PlusCellCharge2559 i := by
  fin_cases i
  · exact batchC05119PlusCellP000ChargeBound2559
  · exact batchC05119PlusCellP001ChargeBound2559
  · exact batchC05119PlusCellP002ChargeBound2559
  · exact batchC05119PlusCellP003ChargeBound2559
  · exact batchC05119PlusCellP004ChargeBound2559
  · exact batchC05119PlusCellP005ChargeBound2559
  · exact batchC05119PlusCellP006ChargeBound2559
  · exact batchC05119PlusCellP007ChargeBound2559
  · exact batchC05119PlusCellP008ChargeBound2559
  · exact batchC05119PlusCellP009ChargeBound2559
  · exact batchC05119PlusCellP010ChargeBound2559
  · exact batchC05119PlusCellP011ChargeBound2559
  · exact batchC05119PlusCellP012ChargeBound2559
  · exact batchC05119PlusCellP013ChargeBound2559
  · exact batchC05119PlusCellP014ChargeBound2559
  · exact batchC05119PlusCellP015ChargeBound2559
  · exact batchC05119PlusCellP016ChargeBound2559
  · exact batchC05119PlusCellP017ChargeBound2559
  · exact batchC05119PlusCellP018ChargeBound2559
  · exact batchC05119PlusCellP019ChargeBound2559
  · exact batchC05119PlusCellP020ChargeBound2559
  · exact batchC05119PlusCellP021ChargeBound2559
  · exact batchC05119PlusCellP022ChargeBound2559
  · exact batchC05119PlusCellP023ChargeBound2559
  · exact batchC05119PlusCellP024ChargeBound2559
  · exact batchC05119PlusCellP025ChargeBound2559
  · exact batchC05119PlusCellP026ChargeBound2559
  · exact batchC05119PlusCellP027ChargeBound2559
  · exact batchC05119PlusCellP028ChargeBound2559
  · exact batchC05119PlusCellP029ChargeBound2559

noncomputable def batchC05119PlusCellThirdUpper2559 : ℝ := ((7145936963279 : ℝ) /
        1000000)

noncomputable def batchC05119PlusCellCurvatureUpper2559 : ℝ := ((35914650663 : ℝ) /
        1000000)

noncomputable def batchC05119PlusCellIntegralUpper2559 : ℝ := ((17653882879 : ℝ) /
        1000000000000)

theorem batchC05119PlusCellThirdBound2559 : batchC05119PlusThirdAggregate2559 ≤
    batchC05119PlusCellThirdUpper2559 := by
  have h : batchC05119PlusThirdAggregate2559 ≤ ∑ i : Fin 30, batchC05119PlusCellCharge2559 i :=
    Finset.sum_le_sum (fun i _ => batchC05119PlusCellChargeBound2559 i)
  apply h.trans
  rw [sum30_chain2541]
  norm_num [batchC05119PlusCellCharge2559, batchC05119PlusCellThirdUpper2559,
      batchC05119PlusCellP000Charge2559, batchC05119PlusCellP001Charge2559,
      batchC05119PlusCellP002Charge2559, batchC05119PlusCellP003Charge2559,
          batchC05119PlusCellP004Charge2559, batchC05119PlusCellP005Charge2559,
      batchC05119PlusCellP006Charge2559, batchC05119PlusCellP007Charge2559,
          batchC05119PlusCellP008Charge2559, batchC05119PlusCellP009Charge2559,
      batchC05119PlusCellP010Charge2559, batchC05119PlusCellP011Charge2559,
          batchC05119PlusCellP012Charge2559, batchC05119PlusCellP013Charge2559,
      batchC05119PlusCellP014Charge2559, batchC05119PlusCellP015Charge2559,
          batchC05119PlusCellP016Charge2559, batchC05119PlusCellP017Charge2559,
      batchC05119PlusCellP018Charge2559, batchC05119PlusCellP019Charge2559,
          batchC05119PlusCellP020Charge2559, batchC05119PlusCellP021Charge2559,
      batchC05119PlusCellP022Charge2559, batchC05119PlusCellP023Charge2559,
          batchC05119PlusCellP024Charge2559, batchC05119PlusCellP025Charge2559,
      batchC05119PlusCellP026Charge2559, batchC05119PlusCellP027Charge2559,
          batchC05119PlusCellP028Charge2559, batchC05119PlusCellP029Charge2559]

theorem batchC05119PlusCellCurvatureBound2559 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN05119PlusPosition2559 batchN05120PlusPosition2559 ≤
        batchC05119PlusCellCurvatureUpper2559 := by
  have h := batchC05119PlusCurvature_bound2559
  have ht := batchC05119PlusCellThirdBound2559
  norm_num [batchC05119PlusSignedMidpointUpper2559, batchC05119PlusCellThirdUpper2559,
      batchC05119PlusCellCurvatureUpper2559,
    batchN05119PlusPosition2559, batchN05120PlusPosition2559] at *
  linarith

theorem batchC05119PlusCellIntegralBound2559 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤ baseCoefficientError2540 i) :
    (∫ x in batchN05119PlusPosition2559..batchN05120PlusPosition2559,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤
        batchC05119PlusCellIntegralUpper2559 := by
  have h := weightedPhysical2539_norm_integral_le_signed_cell (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541 hcoeff
    (a := batchN05119PlusPosition2559) (b := batchN05120PlusPosition2559)
    (by norm_num [batchN05119PlusPosition2559, batchN05120PlusPosition2559])
  have hl := batchValueN05119PlusSigned_le2559
  have hr := batchValueN05120PlusSigned_le2559
  have hc := batchC05119PlusCellCurvatureBound2559
  have hleft : batchValueN05119PlusPosition2559 = batchN05119PlusPosition2559 := by
    norm_num [batchValueN05119PlusPosition2559, batchN05119PlusPosition2559]
  have hright : batchValueN05120PlusPosition2559 = batchN05120PlusPosition2559 := by
    norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559]
  rw [hleft] at hl
  rw [hright] at hr
  norm_num [batchN05119PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05119PlusUpper2559,
    batchValueN05120PlusUpper2559, batchC05119PlusCellCurvatureUpper2559,
        batchC05119PlusCellIntegralUpper2559] at *
  linarith

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05119PlusCellChargeBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusCellThirdBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusCellCurvatureBound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusCellIntegralBound2559
