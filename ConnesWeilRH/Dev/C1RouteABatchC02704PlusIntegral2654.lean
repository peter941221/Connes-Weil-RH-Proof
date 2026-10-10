import ConnesWeilRH.Dev.C1RouteABatchC02704PlusAssembly2654
import ConnesWeilRH.Dev.C1RouteABatchValueN02705Plus2654
import ConnesWeilRH.Dev.C1RouteABatchValueN02704Plus2654

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def batchC02704PlusCellP000Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP000ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ + baseCoefficientError2540 ⟨0, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨0, by omega⟩ ≤ batchC02704PlusCellP000Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨0, by omega⟩ ≤ ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP000NormUpper2654, batchC02704PlusRightP000NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP000Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ +
      baseCoefficientError2540 ⟨0, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP000Charge2654]

noncomputable def batchC02704PlusCellP001Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP001ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ + baseCoefficientError2540 ⟨1, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨1, by omega⟩ ≤ batchC02704PlusCellP001Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨1, by omega⟩ ≤ ((11396094338325169411 : ℝ) /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP001NormUpper2654, batchC02704PlusRightP001NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP001Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ +
      baseCoefficientError2540 ⟨1, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP001Charge2654]

noncomputable def batchC02704PlusCellP002Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP002ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ + baseCoefficientError2540 ⟨2, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨2, by omega⟩ ≤ batchC02704PlusCellP002Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨2, by omega⟩ ≤ ((13341253279585639305518643025356319 :
      ℝ) /
        (11972621413014756 * 10^40
        + 7059245861496117904970213993920593920000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP002NormUpper2654, batchC02704PlusRightP002NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP002Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ +
      baseCoefficientError2540 ⟨2, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP002Charge2654]

noncomputable def batchC02704PlusCellP003Charge2654 : ℝ := ((1297 : ℝ) /
        200000)

theorem batchC02704PlusCellP003ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ + baseCoefficientError2540 ⟨3, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨3, by omega⟩ ≤ batchC02704PlusCellP003Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨3, by omega⟩ ≤ (((9278 * 10^40
        + 3855182682296684018303873064851931384257) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP003NormUpper2654, batchC02704PlusRightP003NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP003Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ +
      baseCoefficientError2540 ⟨3, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP003Charge2654]

noncomputable def batchC02704PlusCellP004Charge2654 : ℝ := ((1377 : ℝ) /
        500000)

theorem batchC02704PlusCellP004ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ + baseCoefficientError2540 ⟨4, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨4, by omega⟩ ≤ batchC02704PlusCellP004Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨4, by omega⟩ ≤ (((188409 * 10^40
        + 1103606607586129821457787680252182633419) : ℝ) /
        (748288838313422294 * 10^40
        + 1202866343507369060638374620037120000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP004NormUpper2654, batchC02704PlusRightP004NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP004Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ +
      baseCoefficientError2540 ⟨4, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP004Charge2654]

noncomputable def batchC02704PlusCellP005Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP005ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ + baseCoefficientError2540 ⟨5, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨5, by omega⟩ ≤ batchC02704PlusCellP005Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨5, by omega⟩ ≤ ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP005NormUpper2654, batchC02704PlusRightP005NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP005Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ +
      baseCoefficientError2540 ⟨5, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP005Charge2654]

noncomputable def batchC02704PlusCellP006Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP006ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ + baseCoefficientError2540 ⟨6, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨6, by omega⟩ ≤ batchC02704PlusCellP006Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨6, by omega⟩ ≤ ((51251060176906798821894626745889 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP006NormUpper2654, batchC02704PlusRightP006NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP006Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ +
      baseCoefficientError2540 ⟨6, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP006Charge2654]

noncomputable def batchC02704PlusCellP007Charge2654 : ℝ := ((3 : ℝ) /
        62500)

theorem batchC02704PlusCellP007ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ + baseCoefficientError2540 ⟨7, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨7, by omega⟩ ≤ batchC02704PlusCellP007Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨7, by omega⟩ ≤ (((306 * 10^40
        + 9680823585962664747270516090486010594481) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP007NormUpper2654, batchC02704PlusRightP007NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP007Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ +
      baseCoefficientError2540 ⟨7, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP007Charge2654]

noncomputable def batchC02704PlusCellP008Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP008ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ + baseCoefficientError2540 ⟨8, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨8, by omega⟩ ≤ batchC02704PlusCellP008Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨8, by omega⟩ ≤ ((7962465628414155999050444531769 : ℝ) /
        (467680523945888933 * 10^40
        + 8251791464692105662898984137523200000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP008NormUpper2654, batchC02704PlusRightP008NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP008Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ +
      baseCoefficientError2540 ⟨8, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP008Charge2654]

noncomputable def batchC02704PlusCellP009Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP009ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ + baseCoefficientError2540 ⟨9, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨9, by omega⟩ ≤ batchC02704PlusCellP009Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨9, by omega⟩ ≤ ((254804679687846000766945254734761 : ℝ)
      /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP009NormUpper2654, batchC02704PlusRightP009NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP009Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ +
      baseCoefficientError2540 ⟨9, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP009Charge2654]

noncomputable def batchC02704PlusCellP010Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP010ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ + baseCoefficientError2540 ⟨10, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨10, by omega⟩ ≤ batchC02704PlusCellP010Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨10, by omega⟩ ≤ ((127404013805805441780758478077203 : ℝ)
      /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP010NormUpper2654, batchC02704PlusRightP010NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP010Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ +
      baseCoefficientError2540 ⟨10, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP010Charge2654]

noncomputable def batchC02704PlusCellP011Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP011ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ + baseCoefficientError2540 ⟨11, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨11, by omega⟩ ≤ batchC02704PlusCellP011Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨11, by omega⟩ ≤ ((63702564979565686102143725873381 : ℝ)
      /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP011NormUpper2654, batchC02704PlusRightP011NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP011Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ +
      baseCoefficientError2540 ⟨11, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP011Charge2654]

noncomputable def batchC02704PlusCellP012Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP012ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ + baseCoefficientError2540 ⟨12, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨12, by omega⟩ ≤ batchC02704PlusCellP012Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨12, by omega⟩ ≤ ((254812572131330226243208944386707 : ℝ)
      /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP012NormUpper2654, batchC02704PlusRightP012NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP012Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ +
      baseCoefficientError2540 ⟨12, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP012Charge2654]

noncomputable def batchC02704PlusCellP013Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP013ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ + baseCoefficientError2540 ⟨13, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨13, by omega⟩ ≤ batchC02704PlusCellP013Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨13, by omega⟩ ≤ ((127407339640702761260376225653557 : ℝ)
      /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP013NormUpper2654, batchC02704PlusRightP013NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP013Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ +
      baseCoefficientError2540 ⟨13, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP013Charge2654]

noncomputable def batchC02704PlusCellP014Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP014ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ + baseCoefficientError2540 ⟨14, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨14, by omega⟩ ≤ batchC02704PlusCellP014Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨14, by omega⟩ ≤ ((63704645935515719366624905017663 : ℝ)
      /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP014NormUpper2654, batchC02704PlusRightP014NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP014Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ +
      baseCoefficientError2540 ⟨14, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP014Charge2654]

noncomputable def batchC02704PlusCellP015Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP015ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ + baseCoefficientError2540 ⟨15, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨15, by omega⟩ ≤ batchC02704PlusCellP015Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨15, by omega⟩ ≤ ((63705345346051012668962475135807 : ℝ)
      /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP015NormUpper2654, batchC02704PlusRightP015NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP015Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ +
      baseCoefficientError2540 ⟨15, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP015Charge2654]

noncomputable def batchC02704PlusCellP016Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP016ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ + baseCoefficientError2540 ⟨16, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨16, by omega⟩ ≤ batchC02704PlusCellP016Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨16, by omega⟩ ≤ ((254823403215064118250537702081839 : ℝ)
      /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP016NormUpper2654, batchC02704PlusRightP016NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP016Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ +
      baseCoefficientError2540 ⟨16, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP016Charge2654]

noncomputable def batchC02704PlusCellP017Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP017ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ + baseCoefficientError2540 ⟨17, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨17, by omega⟩ ≤ batchC02704PlusCellP017Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨17, by omega⟩ ≤ ((15926708160658671556794394821689 : ℝ)
      /
        (935361047891777867 * 10^40
        + 6503582929384211325797968275046400000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP017NormUpper2654, batchC02704PlusRightP017NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP017Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ +
      baseCoefficientError2540 ⟨17, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP017Charge2654]

noncomputable def batchC02704PlusCellP018Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP018ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ + baseCoefficientError2540 ⟨18, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨18, by omega⟩ ≤ batchC02704PlusCellP018Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨18, by omega⟩ ≤ ((254828815443524013872106779087779 : ℝ)
      /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP018NormUpper2654, batchC02704PlusRightP018NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP018Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ +
      baseCoefficientError2540 ⟨18, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP018Charge2654]

noncomputable def batchC02704PlusCellP019Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP019ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ + baseCoefficientError2540 ⟨19, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨19, by omega⟩ ≤ batchC02704PlusCellP019Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨19, by omega⟩ ≤ ((127415749521421618989942267144163 : ℝ)
      /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP019NormUpper2654, batchC02704PlusRightP019NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP019Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ +
      baseCoefficientError2540 ⟨19, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP019Charge2654]

noncomputable def batchC02704PlusCellP020Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP020ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ + baseCoefficientError2540 ⟨20, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨20, by omega⟩ ≤ batchC02704PlusCellP020Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨20, by omega⟩ ≤ ((254834417283103413998364162119077 : ℝ)
      /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP020NormUpper2654, batchC02704PlusRightP020NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP020Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ +
      baseCoefficientError2540 ⟨20, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP020Charge2654]

noncomputable def batchC02704PlusCellP021Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP021ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ + baseCoefficientError2540 ⟨21, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨21, by omega⟩ ≤ batchC02704PlusCellP021Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨21, by omega⟩ ≤ ((50967370539785518967323689092871 : ℝ)
      /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP021NormUpper2654, batchC02704PlusRightP021NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP021Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ +
      baseCoefficientError2540 ⟨21, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP021Charge2654]

noncomputable def batchC02704PlusCellP022Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP022ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ + baseCoefficientError2540 ⟨22, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨22, by omega⟩ ≤ batchC02704PlusCellP022Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨22, by omega⟩ ≤ ((50967619848941996887667038335641 : ℝ)
      /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP022NormUpper2654, batchC02704PlusRightP022NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP022Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ +
      baseCoefficientError2540 ⟨22, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP022Charge2654]

noncomputable def batchC02704PlusCellP023Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP023ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ + baseCoefficientError2540 ⟨23, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨23, by omega⟩ ≤ batchC02704PlusCellP023Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨23, by omega⟩ ≤ ((254841693304631807559045972201067 : ℝ)
      /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP023NormUpper2654, batchC02704PlusRightP023NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP023Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ +
      baseCoefficientError2540 ⟨23, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP023Charge2654]

noncomputable def batchC02704PlusCellP024Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP024ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ + baseCoefficientError2540 ⟨24, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨24, by omega⟩ ≤ batchC02704PlusCellP024Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨24, by omega⟩ ≤ ((31855418125840176369765127309591 : ℝ)
      /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP024NormUpper2654, batchC02704PlusRightP024NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP024Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ +
      baseCoefficientError2540 ⟨24, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP024Charge2654]

noncomputable def batchC02704PlusCellP025Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP025ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ + baseCoefficientError2540 ⟨25, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨25, by omega⟩ ≤ batchC02704PlusCellP025Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨25, by omega⟩ ≤ ((12742270797663208979535341469353 : ℝ)
      /
        (748288838313422294 * 10^40
        + 1202866343507369060638374620037120000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP025NormUpper2654, batchC02704PlusRightP025NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP025Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ +
      baseCoefficientError2540 ⟨25, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP025Charge2654]

noncomputable def batchC02704PlusCellP026Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP026ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ + baseCoefficientError2540 ⟨26, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨26, by omega⟩ ≤ batchC02704PlusCellP026Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨26, by omega⟩ ≤ ((254847532393541581450095040947371 : ℝ)
      /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP026NormUpper2654, batchC02704PlusRightP026NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP026Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ +
      baseCoefficientError2540 ⟨26, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP026Charge2654]

noncomputable def batchC02704PlusCellP027Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP027ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ + baseCoefficientError2540 ⟨27, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨27, by omega⟩ ≤ batchC02704PlusCellP027Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨27, by omega⟩ ≤ ((127425293257726753262300675447871 : ℝ)
      /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP027NormUpper2654, batchC02704PlusRightP027NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP027Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ +
      baseCoefficientError2540 ⟨27, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP027Charge2654]

noncomputable def batchC02704PlusCellP028Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP028ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ + baseCoefficientError2540 ⟨28, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨28, by omega⟩ ≤ batchC02704PlusCellP028Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨28, by omega⟩ ≤ ((31856474461725216271264720387923 : ℝ)
      /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP028NormUpper2654, batchC02704PlusRightP028NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP028Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ +
      baseCoefficientError2540 ⟨28, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP028Charge2654]

noncomputable def batchC02704PlusCellP029Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02704PlusCellP029ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ + baseCoefficientError2540 ⟨29, by omega⟩) *
      batchC02704PlusThirdCell2654 ⟨29, by omega⟩ ≤ batchC02704PlusCellP029Charge2654 := by
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
  have ht : batchC02704PlusThirdCell2654 ⟨29, by omega⟩ ≤ ((25485363660032928284213436945443 : ℝ)
      /
        (1496577676626844588 * 10^40
        + 2405732687014738121276749240074240000000)) := by
    unfold batchC02704PlusThirdCell2654
    norm_num [batchC02704PlusLeftNormUpper2654, batchC02704PlusRightNormUpper2654,
      batchC02704PlusLeftP029NormUpper2654, batchC02704PlusRightP029NormUpper2654,
      batchC02704PlusFourthUpper2654, batchC02704PlusFourthP029Upper2654,
      batchN02704PlusPosition2654, batchN02705PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ +
      baseCoefficientError2540 ⟨29, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02704PlusCellP029Charge2654]

noncomputable def batchC02704PlusCellCharge2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02704PlusCellP000Charge2654
  | 1 => batchC02704PlusCellP001Charge2654
  | 2 => batchC02704PlusCellP002Charge2654
  | 3 => batchC02704PlusCellP003Charge2654
  | 4 => batchC02704PlusCellP004Charge2654
  | 5 => batchC02704PlusCellP005Charge2654
  | 6 => batchC02704PlusCellP006Charge2654
  | 7 => batchC02704PlusCellP007Charge2654
  | 8 => batchC02704PlusCellP008Charge2654
  | 9 => batchC02704PlusCellP009Charge2654
  | 10 => batchC02704PlusCellP010Charge2654
  | 11 => batchC02704PlusCellP011Charge2654
  | 12 => batchC02704PlusCellP012Charge2654
  | 13 => batchC02704PlusCellP013Charge2654
  | 14 => batchC02704PlusCellP014Charge2654
  | 15 => batchC02704PlusCellP015Charge2654
  | 16 => batchC02704PlusCellP016Charge2654
  | 17 => batchC02704PlusCellP017Charge2654
  | 18 => batchC02704PlusCellP018Charge2654
  | 19 => batchC02704PlusCellP019Charge2654
  | 20 => batchC02704PlusCellP020Charge2654
  | 21 => batchC02704PlusCellP021Charge2654
  | 22 => batchC02704PlusCellP022Charge2654
  | 23 => batchC02704PlusCellP023Charge2654
  | 24 => batchC02704PlusCellP024Charge2654
  | 25 => batchC02704PlusCellP025Charge2654
  | 26 => batchC02704PlusCellP026Charge2654
  | 27 => batchC02704PlusCellP027Charge2654
  | 28 => batchC02704PlusCellP028Charge2654
  | 29 => batchC02704PlusCellP029Charge2654
  | _ => 0

theorem batchC02704PlusCellChargeBound2654 (i : Fin 30) :
    (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC02704PlusThirdCell2654 i ≤ batchC02704PlusCellCharge2654 i := by
  fin_cases i
  · exact batchC02704PlusCellP000ChargeBound2654
  · exact batchC02704PlusCellP001ChargeBound2654
  · exact batchC02704PlusCellP002ChargeBound2654
  · exact batchC02704PlusCellP003ChargeBound2654
  · exact batchC02704PlusCellP004ChargeBound2654
  · exact batchC02704PlusCellP005ChargeBound2654
  · exact batchC02704PlusCellP006ChargeBound2654
  · exact batchC02704PlusCellP007ChargeBound2654
  · exact batchC02704PlusCellP008ChargeBound2654
  · exact batchC02704PlusCellP009ChargeBound2654
  · exact batchC02704PlusCellP010ChargeBound2654
  · exact batchC02704PlusCellP011ChargeBound2654
  · exact batchC02704PlusCellP012ChargeBound2654
  · exact batchC02704PlusCellP013ChargeBound2654
  · exact batchC02704PlusCellP014ChargeBound2654
  · exact batchC02704PlusCellP015ChargeBound2654
  · exact batchC02704PlusCellP016ChargeBound2654
  · exact batchC02704PlusCellP017ChargeBound2654
  · exact batchC02704PlusCellP018ChargeBound2654
  · exact batchC02704PlusCellP019ChargeBound2654
  · exact batchC02704PlusCellP020ChargeBound2654
  · exact batchC02704PlusCellP021ChargeBound2654
  · exact batchC02704PlusCellP022ChargeBound2654
  · exact batchC02704PlusCellP023ChargeBound2654
  · exact batchC02704PlusCellP024ChargeBound2654
  · exact batchC02704PlusCellP025ChargeBound2654
  · exact batchC02704PlusCellP026ChargeBound2654
  · exact batchC02704PlusCellP027ChargeBound2654
  · exact batchC02704PlusCellP028ChargeBound2654
  · exact batchC02704PlusCellP029ChargeBound2654

noncomputable def batchC02704PlusCellThirdUpper2654 : ℝ := ((4657 : ℝ) /
        500000)

noncomputable def batchC02704PlusCellCurvatureUpper2654 : ℝ := ((89 : ℝ) /
        500000)

noncomputable def batchC02704PlusCellIntegralUpper2654 : ℝ := ((101 : ℝ) /
        1000000000000)

theorem batchC02704PlusCellThirdBound2654 : batchC02704PlusThirdAggregate2654 ≤
    batchC02704PlusCellThirdUpper2654 := by
  have h : batchC02704PlusThirdAggregate2654 ≤ ∑ i : Fin 30, batchC02704PlusCellCharge2654 i :=
    Finset.sum_le_sum (fun i _ => batchC02704PlusCellChargeBound2654 i)
  apply h.trans
  rw [sum30_chain2541]
  norm_num [batchC02704PlusCellCharge2654, batchC02704PlusCellThirdUpper2654,
      batchC02704PlusCellP000Charge2654, batchC02704PlusCellP001Charge2654,
      batchC02704PlusCellP002Charge2654, batchC02704PlusCellP003Charge2654,
          batchC02704PlusCellP004Charge2654, batchC02704PlusCellP005Charge2654,
      batchC02704PlusCellP006Charge2654, batchC02704PlusCellP007Charge2654,
          batchC02704PlusCellP008Charge2654, batchC02704PlusCellP009Charge2654,
      batchC02704PlusCellP010Charge2654, batchC02704PlusCellP011Charge2654,
          batchC02704PlusCellP012Charge2654, batchC02704PlusCellP013Charge2654,
      batchC02704PlusCellP014Charge2654, batchC02704PlusCellP015Charge2654,
          batchC02704PlusCellP016Charge2654, batchC02704PlusCellP017Charge2654,
      batchC02704PlusCellP018Charge2654, batchC02704PlusCellP019Charge2654,
          batchC02704PlusCellP020Charge2654, batchC02704PlusCellP021Charge2654,
      batchC02704PlusCellP022Charge2654, batchC02704PlusCellP023Charge2654,
          batchC02704PlusCellP024Charge2654, batchC02704PlusCellP025Charge2654,
      batchC02704PlusCellP026Charge2654, batchC02704PlusCellP027Charge2654,
          batchC02704PlusCellP028Charge2654, batchC02704PlusCellP029Charge2654]

theorem batchC02704PlusCellCurvatureBound2654 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN02704PlusPosition2654 batchN02705PlusPosition2654 ≤
        batchC02704PlusCellCurvatureUpper2654 := by
  have h := batchC02704PlusCurvature_bound2654
  have ht := batchC02704PlusCellThirdBound2654
  norm_num [batchC02704PlusSignedMidpointUpper2654, batchC02704PlusCellThirdUpper2654,
      batchC02704PlusCellCurvatureUpper2654,
    batchN02704PlusPosition2654, batchN02705PlusPosition2654] at *
  linarith

theorem batchC02704PlusCellIntegralBound2654 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤ baseCoefficientError2540 i) :
    (∫ x in batchN02704PlusPosition2654..batchN02705PlusPosition2654,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤
        batchC02704PlusCellIntegralUpper2654 := by
  have h := weightedPhysical2539_norm_integral_le_signed_cell (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541 hcoeff
    (a := batchN02704PlusPosition2654) (b := batchN02705PlusPosition2654)
    (by norm_num [batchN02704PlusPosition2654, batchN02705PlusPosition2654])
  have hl := batchValueN02704PlusSigned_le2654
  have hr := batchValueN02705PlusSigned_le2654
  have hc := batchC02704PlusCellCurvatureBound2654
  have hleft : batchValueN02704PlusPosition2654 = batchN02704PlusPosition2654 := by
    norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654]
  have hright : batchValueN02705PlusPosition2654 = batchN02705PlusPosition2654 := by
    norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654]
  rw [hleft] at hl
  rw [hright] at hr
  norm_num [batchN02704PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02704PlusUpper2654,
    batchValueN02705PlusUpper2654, batchC02704PlusCellCurvatureUpper2654,
        batchC02704PlusCellIntegralUpper2654] at *
  linarith

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02704PlusCellChargeBound2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusCellThirdBound2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusCellCurvatureBound2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusCellIntegralBound2654
