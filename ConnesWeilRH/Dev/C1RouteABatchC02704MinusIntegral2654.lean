import ConnesWeilRH.Dev.C1RouteABatchC02704MinusAssembly2654
import ConnesWeilRH.Dev.C1RouteABatchValueN02705Minus2654
import ConnesWeilRH.Dev.C1RouteABatchValueN02704Minus2654

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def batchC02704MinusCellP000Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP000ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ + baseCoefficientError2540 ⟨0, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨0, by omega⟩ ≤ batchC02704MinusCellP000Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨0, by omega⟩ ≤ ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP000NormUpper2654, batchC02704MinusRightP000NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP000Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ +
      baseCoefficientError2540 ⟨0, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP000Charge2654]

noncomputable def batchC02704MinusCellP001Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP001ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ + baseCoefficientError2540 ⟨1, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨1, by omega⟩ ≤ batchC02704MinusCellP001Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨1, by omega⟩ ≤ ((11353010984725169411 : ℝ) /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP001NormUpper2654, batchC02704MinusRightP001NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP001Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ +
      baseCoefficientError2540 ⟨1, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP001Charge2654]

noncomputable def batchC02704MinusCellP002Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP002ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ + baseCoefficientError2540 ⟨2, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨2, by omega⟩ ≤ batchC02704MinusCellP002Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨2, by omega⟩ ≤
      ((355474022106548965881460008469517581949 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP002NormUpper2654, batchC02704MinusRightP002NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP002Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ +
      baseCoefficientError2540 ⟨2, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP002Charge2654]

noncomputable def batchC02704MinusCellP003Charge2654 : ℝ := ((5583 : ℝ) /
        40000)

theorem batchC02704MinusCellP003ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ + baseCoefficientError2540 ⟨3, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨3, by omega⟩ ≤ batchC02704MinusCellP003Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨3, by omega⟩ ≤ (((199725 * 10^40
        + 1775592191050723819584130419366785802961) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP003NormUpper2654, batchC02704MinusRightP003NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP003Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ +
      baseCoefficientError2540 ⟨3, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP003Charge2654]

noncomputable def batchC02704MinusCellP004Charge2654 : ℝ := ((2393 : ℝ) /
        40000)

theorem batchC02704MinusCellP004ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ + baseCoefficientError2540 ⟨4, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨4, by omega⟩ ≤ batchC02704MinusCellP004Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨4, by omega⟩ ≤ (((81874746 * 10^40
        + 5129087385644078564551099997510740819263) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP004NormUpper2654, batchC02704MinusRightP004NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP004Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ +
      baseCoefficientError2540 ⟨4, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP004Charge2654]

noncomputable def batchC02704MinusCellP005Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP005ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ + baseCoefficientError2540 ⟨5, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨5, by omega⟩ ≤ batchC02704MinusCellP005Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨5, by omega⟩ ≤ ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP005NormUpper2654, batchC02704MinusRightP005NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP005Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ +
      baseCoefficientError2540 ⟨5, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP005Charge2654]

noncomputable def batchC02704MinusCellP006Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP006ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ + baseCoefficientError2540 ⟨6, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨6, by omega⟩ ≤ batchC02704MinusCellP006Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨6, by omega⟩ ≤ ((540460733125594277341303032720561 : ℝ)
      /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP006NormUpper2654, batchC02704MinusRightP006NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP006Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ +
      baseCoefficientError2540 ⟨6, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP006Charge2654]

noncomputable def batchC02704MinusCellP007Charge2654 : ℝ := ((829 : ℝ) /
        1000000)

theorem batchC02704MinusCellP007ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ + baseCoefficientError2540 ⟨7, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨7, by omega⟩ ≤ batchC02704MinusCellP007Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨7, by omega⟩ ≤ (((5309 * 10^40
        + 1557473972289208196685788955799702991433) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP007NormUpper2654, batchC02704MinusRightP007NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP007Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ +
      baseCoefficientError2540 ⟨7, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP007Charge2654]

noncomputable def batchC02704MinusCellP008Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP008ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ + baseCoefficientError2540 ⟨8, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨8, by omega⟩ ≤ batchC02704MinusCellP008Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨8, by omega⟩ ≤ ((7962465568105285294135244531769 : ℝ) /
        (467680523945888933 * 10^40
        + 8251791464692105662898984137523200000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP008NormUpper2654, batchC02704MinusRightP008NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP008Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ +
      baseCoefficientError2540 ⟨8, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP008Charge2654]

noncomputable def batchC02704MinusCellP009Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP009ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ + baseCoefficientError2540 ⟨9, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨9, by omega⟩ ≤ batchC02704MinusCellP009Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨9, by omega⟩ ≤ ((254804677757947137521223654734761 : ℝ)
      /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP009NormUpper2654, batchC02704MinusRightP009NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP009Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ +
      baseCoefficientError2540 ⟨9, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP009Charge2654]

noncomputable def batchC02704MinusCellP010Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP010ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ + baseCoefficientError2540 ⟨10, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨10, by omega⟩ ≤ batchC02704MinusCellP010Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨10, by omega⟩ ≤ ((127404012840851666314518478077203 :
      ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP010NormUpper2654, batchC02704MinusRightP010NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP010Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ +
      baseCoefficientError2540 ⟨10, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP010Charge2654]

noncomputable def batchC02704MinusCellP011Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP011ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ + baseCoefficientError2540 ⟨11, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨11, by omega⟩ ≤ batchC02704MinusCellP011Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨11, by omega⟩ ≤ ((63702564497087350286489325873381 : ℝ)
      /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP011NormUpper2654, batchC02704MinusRightP011NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP011Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ +
      baseCoefficientError2540 ⟨11, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP011Charge2654]

noncomputable def batchC02704MinusCellP012Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP012ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ + baseCoefficientError2540 ⟨12, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨12, by omega⟩ ≤ batchC02704MinusCellP012Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨12, by omega⟩ ≤ ((254812570201410883553416944386707 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP012NormUpper2654, batchC02704MinusRightP012NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP012Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ +
      baseCoefficientError2540 ⟨12, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP012Charge2654]

noncomputable def batchC02704MinusCellP013Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP013ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ + baseCoefficientError2540 ⟨13, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨13, by omega⟩ ≤ batchC02704MinusCellP013Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨13, by omega⟩ ≤ ((127407338675740356323877025653557 :
      ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP013NormUpper2654, batchC02704MinusRightP013NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP013Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ +
      baseCoefficientError2540 ⟨13, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP013Charge2654]

noncomputable def batchC02704MinusCellP014Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP014ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ + baseCoefficientError2540 ⟨14, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨14, by omega⟩ ≤ batchC02704MinusCellP014Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨14, by omega⟩ ≤ ((63704645453031984370836105017663 : ℝ)
      /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP014NormUpper2654, batchC02704MinusRightP014NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP014Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ +
      baseCoefficientError2540 ⟨14, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP014Charge2654]

noncomputable def batchC02704MinusCellP015Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP015ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ + baseCoefficientError2540 ⟨15, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨15, by omega⟩ ≤ batchC02704MinusCellP015Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨15, by omega⟩ ≤ ((63705344863565463112636075135807 : ℝ)
      /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP015NormUpper2654, batchC02704MinusRightP015NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP015Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ +
      baseCoefficientError2540 ⟨15, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP015Charge2654]

noncomputable def batchC02704MinusCellP016Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP016ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ + baseCoefficientError2540 ⟨16, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨16, by omega⟩ ≤ batchC02704MinusCellP016Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨16, by omega⟩ ≤ ((254823401285116674661212902081839 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP016NormUpper2654, batchC02704MinusRightP016NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP016Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ +
      baseCoefficientError2540 ⟨16, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP016Charge2654]

noncomputable def batchC02704MinusCellP017Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP017ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ + baseCoefficientError2540 ⟨17, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨17, by omega⟩ ≤ batchC02704MinusCellP017Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨17, by omega⟩ ≤ ((15926708040036319534253594821689 : ℝ)
      /
        (935361047891777867 * 10^40
        + 6503582929384211325797968275046400000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP017NormUpper2654, batchC02704MinusRightP017NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP017Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ +
      baseCoefficientError2540 ⟨17, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP017Charge2654]

noncomputable def batchC02704MinusCellP018Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP018ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ + baseCoefficientError2540 ⟨18, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨18, by omega⟩ ≤ batchC02704MinusCellP018Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨18, by omega⟩ ≤ ((254828813513562529360874779087779 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP018NormUpper2654, batchC02704MinusRightP018NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP018Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ +
      baseCoefficientError2540 ⟨18, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP018Charge2654]

noncomputable def batchC02704MinusCellP019Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP019ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ + baseCoefficientError2540 ⟨19, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨19, by omega⟩ ≤ batchC02704MinusCellP019Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨19, by omega⟩ ≤ ((127415748556437395796905467144163 :
      ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP019NormUpper2654, batchC02704MinusRightP019NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP019Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ +
      baseCoefficientError2540 ⟨19, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP019Charge2654]

noncomputable def batchC02704MinusCellP020Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP020ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ + baseCoefficientError2540 ⟨20, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨20, by omega⟩ ≤ batchC02704MinusCellP020Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨20, by omega⟩ ≤ ((254834415353127397144245762119077 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP020NormUpper2654, batchC02704MinusRightP020NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP020Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ +
      baseCoefficientError2540 ⟨20, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP020Charge2654]

noncomputable def batchC02704MinusCellP021Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP021ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ + baseCoefficientError2540 ⟨21, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨21, by omega⟩ ≤ batchC02704MinusCellP021Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨21, by omega⟩ ≤ ((50967370153789052028484649092871 : ℝ)
      /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP021NormUpper2654, batchC02704MinusRightP021NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP021Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ +
      baseCoefficientError2540 ⟨21, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP021Charge2654]

noncomputable def batchC02704MinusCellP022Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP022ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ + baseCoefficientError2540 ⟨22, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨22, by omega⟩ ≤ batchC02704MinusCellP022Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨22, by omega⟩ ≤ ((50967619462944883208921438335641 : ℝ)
      /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP022NormUpper2654, batchC02704MinusRightP022NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP022Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ +
      baseCoefficientError2540 ⟨22, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP022Charge2654]

noncomputable def batchC02704MinusCellP023Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP023ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ + baseCoefficientError2540 ⟨23, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨23, by omega⟩ ≤ batchC02704MinusCellP023Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨23, by omega⟩ ≤ ((254841691374636915823698772201067 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP023NormUpper2654, batchC02704MinusRightP023NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP023Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ +
      baseCoefficientError2540 ⟨23, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP023Charge2654]

noncomputable def batchC02704MinusCellP024Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP024ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ + baseCoefficientError2540 ⟨24, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨24, by omega⟩ ≤ batchC02704MinusCellP024Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨24, by omega⟩ ≤ ((31855417884590279325016327309591 : ℝ)
      /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP024NormUpper2654, batchC02704MinusRightP024NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP024Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ +
      baseCoefficientError2540 ⟨24, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP024Charge2654]

noncomputable def batchC02704MinusCellP025Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP025ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ + baseCoefficientError2540 ⟨25, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨25, by omega⟩ ≤ batchC02704MinusCellP025Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨25, by omega⟩ ≤ ((12742270701162981555443181469353 : ℝ)
      /
        (748288838313422294 * 10^40
        + 1202866343507369060638374620037120000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP025NormUpper2654, batchC02704MinusRightP025NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP025Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ +
      baseCoefficientError2540 ⟨25, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP025Charge2654]

noncomputable def batchC02704MinusCellP026Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP026ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ + baseCoefficientError2540 ⟨26, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨26, by omega⟩ ≤ batchC02704MinusCellP026Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨26, by omega⟩ ≤ ((254847530463531542883592640947371 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP026NormUpper2654, batchC02704MinusRightP026NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP026Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ +
      baseCoefficientError2540 ⟨26, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP026Charge2654]

noncomputable def batchC02704MinusCellP027Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP027ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ + baseCoefficientError2540 ⟨27, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨27, by omega⟩ ≤ batchC02704MinusCellP027Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨27, by omega⟩ ≤ ((127425292292717772800374275447871 :
      ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP027NormUpper2654, batchC02704MinusRightP027NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP027Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ +
      baseCoefficientError2540 ⟨27, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP027Charge2654]

noncomputable def batchC02704MinusCellP028Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP028ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ + baseCoefficientError2540 ⟨28, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨28, by omega⟩ ≤ batchC02704MinusCellP028Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨28, by omega⟩ ≤ ((31856474220472579085075920387923 : ℝ)
      /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP028NormUpper2654, batchC02704MinusRightP028NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP028Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ +
      baseCoefficientError2540 ⟨28, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP028Charge2654]

noncomputable def batchC02704MinusCellP029Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704MinusCellP029ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ + baseCoefficientError2540 ⟨29, by omega⟩) *
      batchC02704MinusThirdCell2654 ⟨29, by omega⟩ ≤ batchC02704MinusCellP029Charge2654 := by
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
  have ht : batchC02704MinusThirdCell2654 ⟨29, by omega⟩ ≤ ((25485363467030341013751996945443 : ℝ)
      /
        (1496577676626844588 * 10^40
        + 2405732687014738121276749240074240000000)) := by
    unfold batchC02704MinusThirdCell2654
    norm_num [batchC02704MinusLeftNormUpper2654, batchC02704MinusRightNormUpper2654,
      batchC02704MinusLeftP029NormUpper2654, batchC02704MinusRightP029NormUpper2654,
      batchC02704MinusFourthUpper2654, batchC02704MinusFourthP029Upper2654,
      batchN02704MinusPosition2654, batchN02705MinusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ +
      baseCoefficientError2540 ⟨29, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704MinusCellP029Charge2654]

noncomputable def batchC02704MinusCellCharge2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02704MinusCellP000Charge2654
  | 1 => batchC02704MinusCellP001Charge2654
  | 2 => batchC02704MinusCellP002Charge2654
  | 3 => batchC02704MinusCellP003Charge2654
  | 4 => batchC02704MinusCellP004Charge2654
  | 5 => batchC02704MinusCellP005Charge2654
  | 6 => batchC02704MinusCellP006Charge2654
  | 7 => batchC02704MinusCellP007Charge2654
  | 8 => batchC02704MinusCellP008Charge2654
  | 9 => batchC02704MinusCellP009Charge2654
  | 10 => batchC02704MinusCellP010Charge2654
  | 11 => batchC02704MinusCellP011Charge2654
  | 12 => batchC02704MinusCellP012Charge2654
  | 13 => batchC02704MinusCellP013Charge2654
  | 14 => batchC02704MinusCellP014Charge2654
  | 15 => batchC02704MinusCellP015Charge2654
  | 16 => batchC02704MinusCellP016Charge2654
  | 17 => batchC02704MinusCellP017Charge2654
  | 18 => batchC02704MinusCellP018Charge2654
  | 19 => batchC02704MinusCellP019Charge2654
  | 20 => batchC02704MinusCellP020Charge2654
  | 21 => batchC02704MinusCellP021Charge2654
  | 22 => batchC02704MinusCellP022Charge2654
  | 23 => batchC02704MinusCellP023Charge2654
  | 24 => batchC02704MinusCellP024Charge2654
  | 25 => batchC02704MinusCellP025Charge2654
  | 26 => batchC02704MinusCellP026Charge2654
  | 27 => batchC02704MinusCellP027Charge2654
  | 28 => batchC02704MinusCellP028Charge2654
  | 29 => batchC02704MinusCellP029Charge2654
  | _ => 0

theorem batchC02704MinusCellChargeBound2654 (i : Fin 30) :
    (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC02704MinusThirdCell2654 i ≤ batchC02704MinusCellCharge2654 i := by
  fin_cases i
  · exact batchC02704MinusCellP000ChargeBound2654
  · exact batchC02704MinusCellP001ChargeBound2654
  · exact batchC02704MinusCellP002ChargeBound2654
  · exact batchC02704MinusCellP003ChargeBound2654
  · exact batchC02704MinusCellP004ChargeBound2654
  · exact batchC02704MinusCellP005ChargeBound2654
  · exact batchC02704MinusCellP006ChargeBound2654
  · exact batchC02704MinusCellP007ChargeBound2654
  · exact batchC02704MinusCellP008ChargeBound2654
  · exact batchC02704MinusCellP009ChargeBound2654
  · exact batchC02704MinusCellP010ChargeBound2654
  · exact batchC02704MinusCellP011ChargeBound2654
  · exact batchC02704MinusCellP012ChargeBound2654
  · exact batchC02704MinusCellP013ChargeBound2654
  · exact batchC02704MinusCellP014ChargeBound2654
  · exact batchC02704MinusCellP015ChargeBound2654
  · exact batchC02704MinusCellP016ChargeBound2654
  · exact batchC02704MinusCellP017ChargeBound2654
  · exact batchC02704MinusCellP018ChargeBound2654
  · exact batchC02704MinusCellP019ChargeBound2654
  · exact batchC02704MinusCellP020ChargeBound2654
  · exact batchC02704MinusCellP021ChargeBound2654
  · exact batchC02704MinusCellP022ChargeBound2654
  · exact batchC02704MinusCellP023ChargeBound2654
  · exact batchC02704MinusCellP024ChargeBound2654
  · exact batchC02704MinusCellP025ChargeBound2654
  · exact batchC02704MinusCellP026ChargeBound2654
  · exact batchC02704MinusCellP027ChargeBound2654
  · exact batchC02704MinusCellP028ChargeBound2654
  · exact batchC02704MinusCellP029ChargeBound2654

noncomputable def batchC02704MinusCellThirdUpper2654 : ℝ := ((3129 : ℝ) /
        15625)

noncomputable def batchC02704MinusCellCurvatureUpper2654 : ℝ := ((3771 : ℝ) /
        1000000)

noncomputable def batchC02704MinusCellIntegralUpper2654 : ℝ := ((2203 : ℝ) /
        1000000000000)

theorem batchC02704MinusCellThirdBound2654 : batchC02704MinusThirdAggregate2654 ≤
    batchC02704MinusCellThirdUpper2654 := by
  have h : batchC02704MinusThirdAggregate2654 ≤ ∑ i : Fin 30, batchC02704MinusCellCharge2654 i :=
    Finset.sum_le_sum (fun i _ => batchC02704MinusCellChargeBound2654 i)
  apply h.trans
  rw [sum30_chain2541]
  norm_num [batchC02704MinusCellCharge2654, batchC02704MinusCellThirdUpper2654,
      batchC02704MinusCellP000Charge2654, batchC02704MinusCellP001Charge2654,
      batchC02704MinusCellP002Charge2654, batchC02704MinusCellP003Charge2654,
          batchC02704MinusCellP004Charge2654, batchC02704MinusCellP005Charge2654,
      batchC02704MinusCellP006Charge2654, batchC02704MinusCellP007Charge2654,
          batchC02704MinusCellP008Charge2654, batchC02704MinusCellP009Charge2654,
      batchC02704MinusCellP010Charge2654, batchC02704MinusCellP011Charge2654,
          batchC02704MinusCellP012Charge2654, batchC02704MinusCellP013Charge2654,
      batchC02704MinusCellP014Charge2654, batchC02704MinusCellP015Charge2654,
          batchC02704MinusCellP016Charge2654, batchC02704MinusCellP017Charge2654,
      batchC02704MinusCellP018Charge2654, batchC02704MinusCellP019Charge2654,
          batchC02704MinusCellP020Charge2654, batchC02704MinusCellP021Charge2654,
      batchC02704MinusCellP022Charge2654, batchC02704MinusCellP023Charge2654,
          batchC02704MinusCellP024Charge2654, batchC02704MinusCellP025Charge2654,
      batchC02704MinusCellP026Charge2654, batchC02704MinusCellP027Charge2654,
          batchC02704MinusCellP028Charge2654, batchC02704MinusCellP029Charge2654]

theorem batchC02704MinusCellCurvatureBound2654 :
    signedCurvatureUpper2539 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN02704MinusPosition2654 batchN02705MinusPosition2654 ≤
        batchC02704MinusCellCurvatureUpper2654 := by
  have h := batchC02704MinusCurvature_bound2654
  have ht := batchC02704MinusCellThirdBound2654
  norm_num [batchC02704MinusSignedMidpointUpper2654, batchC02704MinusCellThirdUpper2654,
      batchC02704MinusCellCurvatureUpper2654,
    batchN02704MinusPosition2654, batchN02705MinusPosition2654] at *
  linarith

theorem batchC02704MinusCellIntegralBound2654 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤ baseCoefficientError2540 i) :
    (∫ x in batchN02704MinusPosition2654..batchN02705MinusPosition2654,
      ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖) ≤
        batchC02704MinusCellIntegralUpper2654 := by
  have h := weightedPhysical2539_norm_integral_le_signed_cell (-1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541 hcoeff
    (a := batchN02704MinusPosition2654) (b := batchN02705MinusPosition2654)
    (by norm_num [batchN02704MinusPosition2654, batchN02705MinusPosition2654])
  have hl := batchValueN02704MinusSigned_le2654
  have hr := batchValueN02705MinusSigned_le2654
  have hc := batchC02704MinusCellCurvatureBound2654
  have hleft : batchValueN02704MinusPosition2654 = batchN02704MinusPosition2654 := by
    norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654]
  have hright : batchValueN02705MinusPosition2654 = batchN02705MinusPosition2654 := by
    norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654]
  rw [hleft] at hl
  rw [hright] at hr
  norm_num [batchN02704MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02704MinusUpper2654,
    batchValueN02705MinusUpper2654, batchC02704MinusCellCurvatureUpper2654,
        batchC02704MinusCellIntegralUpper2654] at *
  linarith

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02704MinusCellChargeBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusCellThirdBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusCellCurvatureBound2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusCellIntegralBound2654
