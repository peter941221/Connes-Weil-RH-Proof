import ConnesWeilRH.Dev.C1RouteABatchC02701MinusAssembly2558
import ConnesWeilRH.Dev.C1RouteABatchValueN02702Minus2558
import ConnesWeilRH.Dev.C1RouteASharedN02701Minus2556

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def batchC02701MinusCellP000Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP000ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ + baseCoefficientError2540 ⟨0, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨0, by omega⟩ ≤ batchC02701MinusCellP000Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨0, by omega⟩ ≤ ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP000NormUpper2558, batchC02701MinusRightP000NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP000Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ +
      baseCoefficientError2540 ⟨0, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP000Charge2558]

noncomputable def batchC02701MinusCellP001Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP001ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ + baseCoefficientError2540 ⟨1, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨1, by omega⟩ ≤ batchC02701MinusCellP001Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨1, by omega⟩ ≤ ((19726710235392321359 : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP001NormUpper2558, batchC02701MinusRightP001NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP001Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ +
      baseCoefficientError2540 ⟨1, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP001Charge2558]

noncomputable def batchC02701MinusCellP002Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP002ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ + baseCoefficientError2540 ⟨2, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨2, by omega⟩ ≤ batchC02701MinusCellP002Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨2, by omega⟩ ≤ ((61367343755919927731662533764866274571
      : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP002NormUpper2558, batchC02701MinusRightP002NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP002Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ +
      baseCoefficientError2540 ⟨2, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP002Charge2558]

noncomputable def batchC02701MinusCellP003Charge2558 : ℝ := ((132577 : ℝ) /
        1000000)

theorem batchC02701MinusCellP003ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ + baseCoefficientError2540 ⟨3, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨3, by omega⟩ ≤ batchC02701MinusCellP003Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨3, by omega⟩ ≤ (((47427 * 10^40
        + 7241063049749891406876622777798274585017) : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP003NormUpper2558, batchC02701MinusRightP003NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP003Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ +
      baseCoefficientError2540 ⟨3, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP003Charge2558]

noncomputable def batchC02701MinusCellP004Charge2558 : ℝ := ((11667 : ℝ) /
        200000)

theorem batchC02701MinusCellP004ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ + baseCoefficientError2540 ⟨4, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨4, by omega⟩ ≤ batchC02701MinusCellP004Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨4, by omega⟩ ≤ (((9979447 * 10^40
        + 9244093395672562134031403897487256834941) : ℝ) /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP004NormUpper2558, batchC02701MinusRightP004NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP004Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ +
      baseCoefficientError2540 ⟨4, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP004Charge2558]

noncomputable def batchC02701MinusCellP005Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP005ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ + baseCoefficientError2540 ⟨5, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨5, by omega⟩ ≤ batchC02701MinusCellP005Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨5, by omega⟩ ≤ ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP005NormUpper2558, batchC02701MinusRightP005NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP005Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ +
      baseCoefficientError2540 ⟨5, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP005Charge2558]

noncomputable def batchC02701MinusCellP006Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP006ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ + baseCoefficientError2540 ⟨6, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨6, by omega⟩ ≤ batchC02701MinusCellP006Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨6, by omega⟩ ≤ ((844629648032303226897927004535711 : ℝ)
      /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP006NormUpper2558, batchC02701MinusRightP006NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP006Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ +
      baseCoefficientError2540 ⟨6, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP006Charge2558]

noncomputable def batchC02701MinusCellP007Charge2558 : ℝ := ((199 : ℝ) /
        250000)

theorem batchC02701MinusCellP007ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ + baseCoefficientError2540 ⟨7, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨7, by omega⟩ ≤ batchC02701MinusCellP007Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨7, by omega⟩ ≤ (((159 * 10^40
        + 2928279635534003322251166963968222163521) : ℝ) /
        (467680523945888933 * 10^40
        + 8251791464692105662898984137523200000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP007NormUpper2558, batchC02701MinusRightP007NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP007Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ +
      baseCoefficientError2540 ⟨7, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP007Charge2558]

noncomputable def batchC02701MinusCellP008Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP008ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ + baseCoefficientError2540 ⟨8, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨8, by omega⟩ ≤ batchC02701MinusCellP008Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨8, by omega⟩ ≤ ((391934981199400003428709928798941961 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP008NormUpper2558, batchC02701MinusRightP008NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP008Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ +
      baseCoefficientError2540 ⟨8, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP008Charge2558]

noncomputable def batchC02701MinusCellP009Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP009ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ + baseCoefficientError2540 ⟨9, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨9, by omega⟩ ≤ batchC02701MinusCellP009Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨9, by omega⟩ ≤ ((391936392770822716471700033691964899 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP009NormUpper2558, batchC02701MinusRightP009NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP009Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ +
      baseCoefficientError2540 ⟨9, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP009Charge2558]

noncomputable def batchC02701MinusCellP010Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP010ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ + baseCoefficientError2540 ⟨10, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨10, by omega⟩ ≤ batchC02701MinusCellP010Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨10, by omega⟩ ≤ ((391937210439377067220816202944478253
      : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP010NormUpper2558, batchC02701MinusRightP010NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP010Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ +
      baseCoefficientError2540 ⟨10, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP010Charge2558]

noncomputable def batchC02701MinusCellP011Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP011ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ + baseCoefficientError2540 ⟨11, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨11, by omega⟩ ≤ batchC02701MinusCellP011Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨11, by omega⟩ ≤ ((6124027431800928766067762063529223 :
      ℝ) /
        (233840261972944466 * 10^40
        + 9125895732346052831449492068761600000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP011NormUpper2558, batchC02701MinusRightP011NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP011Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ +
      baseCoefficientError2540 ⟨11, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP011Charge2558]

noncomputable def batchC02701MinusCellP012Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP012ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ + baseCoefficientError2540 ⟨12, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨12, by omega⟩ ≤ batchC02701MinusCellP012Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨12, by omega⟩ ≤ ((391938320343473012850595857866002539
      : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP012NormUpper2558, batchC02701MinusRightP012NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP012Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ +
      baseCoefficientError2540 ⟨12, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP012Charge2558]

noncomputable def batchC02701MinusCellP013Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP013ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ + baseCoefficientError2540 ⟨13, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨13, by omega⟩ ≤ batchC02701MinusCellP013Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨13, by omega⟩ ≤ ((391938834966634960974854617810469647
      : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP013NormUpper2558, batchC02701MinusRightP013NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP013Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ +
      baseCoefficientError2540 ⟨13, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP013Charge2558]

noncomputable def batchC02701MinusCellP014Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP014ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ + baseCoefficientError2540 ⟨14, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨14, by omega⟩ ≤ batchC02701MinusCellP014Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨14, by omega⟩ ≤ ((195969894267306026897265625568307689
      : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP014NormUpper2558, batchC02701MinusRightP014NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP014Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ +
      baseCoefficientError2540 ⟨14, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP014Charge2558]

noncomputable def batchC02701MinusCellP015Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP015ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ + baseCoefficientError2540 ⟨15, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨15, by omega⟩ ≤ batchC02701MinusCellP015Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨15, by omega⟩ ≤ ((39194047178382630239849148340196049 :
      ℝ) /
        (1496577676626844588 * 10^40
        + 2405732687014738121276749240074240000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP015NormUpper2558, batchC02701MinusRightP015NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP015Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ +
      baseCoefficientError2540 ⟨15, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP015Charge2558]

noncomputable def batchC02701MinusCellP016Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP016ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ + baseCoefficientError2540 ⟨16, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨16, by omega⟩ ≤ batchC02701MinusCellP016Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨16, by omega⟩ ≤ ((195970482779467157992015613120990819
      : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP016NormUpper2558, batchC02701MinusRightP016NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP016Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ +
      baseCoefficientError2540 ⟨16, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP016Charge2558]

noncomputable def batchC02701MinusCellP017Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP017ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ + baseCoefficientError2540 ⟨17, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨17, by omega⟩ ≤ batchC02701MinusCellP017Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨17, by omega⟩ ≤ ((15677676987900938548221241049240797 :
      ℝ) /
        (598631070650737835 * 10^40
        + 2962293074805895248510699696029696000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP017NormUpper2558, batchC02701MinusRightP017NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP017Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ +
      baseCoefficientError2540 ⟨17, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP017Charge2558]

noncomputable def batchC02701MinusCellP018Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP018ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ + baseCoefficientError2540 ⟨18, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨18, by omega⟩ ≤ batchC02701MinusCellP018Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨18, by omega⟩ ≤ ((391942287330696171555580903450765257
      : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP018NormUpper2558, batchC02701MinusRightP018NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP018Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ +
      baseCoefficientError2540 ⟨18, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP018Charge2558]

noncomputable def batchC02701MinusCellP019Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP019ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ + baseCoefficientError2540 ⟨19, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨19, by omega⟩ ≤ batchC02701MinusCellP019Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨19, by omega⟩ ≤ ((391942942711385859401259759511210109
      : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP019NormUpper2558, batchC02701MinusRightP019NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP019Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ +
      baseCoefficientError2540 ⟨19, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP019Charge2558]

noncomputable def batchC02701MinusCellP020Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP020ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ + baseCoefficientError2540 ⟨20, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨20, by omega⟩ ≤ batchC02701MinusCellP020Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨20, by omega⟩ ≤ ((195971827695209111913741199589617769
      : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP020NormUpper2558, batchC02701MinusRightP020NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP020Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ +
      baseCoefficientError2540 ⟨20, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP020Charge2558]

noncomputable def batchC02701MinusCellP021Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP021ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ + baseCoefficientError2540 ⟨21, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨21, by omega⟩ ≤ batchC02701MinusCellP021Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨21, by omega⟩ ≤ ((97986062538087643543810422105894021 :
      ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP021NormUpper2558, batchC02701MinusRightP021NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP021Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ +
      baseCoefficientError2540 ⟨21, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP021Charge2558]

noncomputable def batchC02701MinusCellP022Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP022ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ + baseCoefficientError2540 ⟨22, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨22, by omega⟩ ≤ batchC02701MinusCellP022Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨22, by omega⟩ ≤ ((391944554574523593347860973129827467
      : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP022NormUpper2558, batchC02701MinusRightP022NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP022Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ +
      baseCoefficientError2540 ⟨22, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP022Charge2558]

noncomputable def batchC02701MinusCellP023Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP023ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ + baseCoefficientError2540 ⟨23, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨23, by omega⟩ ≤ batchC02701MinusCellP023Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨23, by omega⟩ ≤ ((78389086456781924587249188159327113 :
      ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP023NormUpper2558, batchC02701MinusRightP023NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP023Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ +
      baseCoefficientError2540 ⟨23, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP023Charge2558]

noncomputable def batchC02701MinusCellP024Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP024ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ + baseCoefficientError2540 ⟨24, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨24, by omega⟩ ≤ batchC02701MinusCellP024Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨24, by omega⟩ ≤ ((391945835645284889396102357301731477
      : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP024NormUpper2558, batchC02701MinusRightP024NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP024Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ +
      baseCoefficientError2540 ⟨24, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP024Charge2558]

noncomputable def batchC02701MinusCellP025Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP025ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ + baseCoefficientError2540 ⟨25, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨25, by omega⟩ ≤ batchC02701MinusCellP025Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨25, by omega⟩ ≤ ((391946341387801584896920208924383453
      : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP025NormUpper2558, batchC02701MinusRightP025NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP025Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ +
      baseCoefficientError2540 ⟨25, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP025Charge2558]

noncomputable def batchC02701MinusCellP026Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP026ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ + baseCoefficientError2540 ⟨26, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨26, by omega⟩ ≤ batchC02701MinusCellP026Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨26, by omega⟩ ≤ ((391946858237573719970348754161601507
      : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP026NormUpper2558, batchC02701MinusRightP026NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP026Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ +
      baseCoefficientError2540 ⟨26, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP026Charge2558]

noncomputable def batchC02701MinusCellP027Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP027ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ + baseCoefficientError2540 ⟨27, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨27, by omega⟩ ≤ batchC02701MinusCellP027Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨27, by omega⟩ ≤ ((97986901017766899525579023486487169 :
      ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP027NormUpper2558, batchC02701MinusRightP027NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP027Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ +
      baseCoefficientError2540 ⟨27, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP027Charge2558]

noncomputable def batchC02701MinusCellP028Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP028ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ + baseCoefficientError2540 ⟨28, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨28, by omega⟩ ≤ batchC02701MinusCellP028Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨28, by omega⟩ ≤ ((391947899357552077742768582397450527
      : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP028NormUpper2558, batchC02701MinusRightP028NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP028Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ +
      baseCoefficientError2540 ⟨28, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP028Charge2558]

noncomputable def batchC02701MinusCellP029Charge2558 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02701MinusCellP029ChargeBound2558 :
    (‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ + baseCoefficientError2540 ⟨29, by omega⟩) *
      batchC02701MinusThirdCell2558 ⟨29, by omega⟩ ≤ batchC02701MinusCellP029Charge2558 := by
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
  have ht : batchC02701MinusThirdCell2558 ⟨29, by omega⟩ ≤ ((391948348913030939795448914608019547
      : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02701MinusThirdCell2558
    norm_num [batchC02701MinusLeftNormUpper2558, batchC02701MinusRightNormUpper2558,
      batchC02701MinusLeftP029NormUpper2558, batchC02701MinusRightP029NormUpper2558,
      batchC02701MinusFourthUpper2558, batchC02701MinusFourthP029Upper2558,
      kernelN02701MinusPosition2555, batchN02702MinusPosition2558]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ +
      baseCoefficientError2540 ⟨29, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02701MinusCellP029Charge2558]

noncomputable def batchC02701MinusCellCharge2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02701MinusCellP000Charge2558
  | 1 => batchC02701MinusCellP001Charge2558
  | 2 => batchC02701MinusCellP002Charge2558
  | 3 => batchC02701MinusCellP003Charge2558
  | 4 => batchC02701MinusCellP004Charge2558
  | 5 => batchC02701MinusCellP005Charge2558
  | 6 => batchC02701MinusCellP006Charge2558
  | 7 => batchC02701MinusCellP007Charge2558
  | 8 => batchC02701MinusCellP008Charge2558
  | 9 => batchC02701MinusCellP009Charge2558
  | 10 => batchC02701MinusCellP010Charge2558
  | 11 => batchC02701MinusCellP011Charge2558
  | 12 => batchC02701MinusCellP012Charge2558
  | 13 => batchC02701MinusCellP013Charge2558
  | 14 => batchC02701MinusCellP014Charge2558
  | 15 => batchC02701MinusCellP015Charge2558
  | 16 => batchC02701MinusCellP016Charge2558
  | 17 => batchC02701MinusCellP017Charge2558
  | 18 => batchC02701MinusCellP018Charge2558
  | 19 => batchC02701MinusCellP019Charge2558
  | 20 => batchC02701MinusCellP020Charge2558
  | 21 => batchC02701MinusCellP021Charge2558
  | 22 => batchC02701MinusCellP022Charge2558
  | 23 => batchC02701MinusCellP023Charge2558
  | 24 => batchC02701MinusCellP024Charge2558
  | 25 => batchC02701MinusCellP025Charge2558
  | 26 => batchC02701MinusCellP026Charge2558
  | 27 => batchC02701MinusCellP027Charge2558
  | 28 => batchC02701MinusCellP028Charge2558
  | 29 => batchC02701MinusCellP029Charge2558
  | _ => 0

theorem batchC02701MinusCellChargeBound2558 (i : Fin 30) :
    (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC02701MinusThirdCell2558 i ≤ batchC02701MinusCellCharge2558 i := by
  fin_cases i
  · exact batchC02701MinusCellP000ChargeBound2558
  · exact batchC02701MinusCellP001ChargeBound2558
  · exact batchC02701MinusCellP002ChargeBound2558
  · exact batchC02701MinusCellP003ChargeBound2558
  · exact batchC02701MinusCellP004ChargeBound2558
  · exact batchC02701MinusCellP005ChargeBound2558
  · exact batchC02701MinusCellP006ChargeBound2558
  · exact batchC02701MinusCellP007ChargeBound2558
  · exact batchC02701MinusCellP008ChargeBound2558
  · exact batchC02701MinusCellP009ChargeBound2558
  · exact batchC02701MinusCellP010ChargeBound2558
  · exact batchC02701MinusCellP011ChargeBound2558
  · exact batchC02701MinusCellP012ChargeBound2558
  · exact batchC02701MinusCellP013ChargeBound2558
  · exact batchC02701MinusCellP014ChargeBound2558
  · exact batchC02701MinusCellP015ChargeBound2558
  · exact batchC02701MinusCellP016ChargeBound2558
  · exact batchC02701MinusCellP017ChargeBound2558
  · exact batchC02701MinusCellP018ChargeBound2558
  · exact batchC02701MinusCellP019ChargeBound2558
  · exact batchC02701MinusCellP020ChargeBound2558
  · exact batchC02701MinusCellP021ChargeBound2558
  · exact batchC02701MinusCellP022ChargeBound2558
  · exact batchC02701MinusCellP023ChargeBound2558
  · exact batchC02701MinusCellP024ChargeBound2558
  · exact batchC02701MinusCellP025ChargeBound2558
  · exact batchC02701MinusCellP026ChargeBound2558
  · exact batchC02701MinusCellP027ChargeBound2558
  · exact batchC02701MinusCellP028ChargeBound2558
  · exact batchC02701MinusCellP029ChargeBound2558

noncomputable def batchC02701MinusCellThirdUpper2558 : ℝ := ((38347 : ℝ) /
        200000)

noncomputable def batchC02701MinusCellCurvatureUpper2558 : ℝ := ((3877 : ℝ) /
        1000000)

noncomputable def batchC02701MinusCellIntegralUpper2558 : ℝ := ((2433 : ℝ) /
        1000000000000)

theorem batchC02701MinusCellThirdBound2558 : batchC02701MinusThirdAggregate2558 ≤
    batchC02701MinusCellThirdUpper2558 := by
  have h : batchC02701MinusThirdAggregate2558 ≤ ∑ i : Fin 30, batchC02701MinusCellCharge2558 i :=
    Finset.sum_le_sum (fun i _ => batchC02701MinusCellChargeBound2558 i)
  apply h.trans
  rw [sum30_chain2541]
  norm_num [batchC02701MinusCellCharge2558, batchC02701MinusCellThirdUpper2558,
      batchC02701MinusCellP000Charge2558, batchC02701MinusCellP001Charge2558,
      batchC02701MinusCellP002Charge2558, batchC02701MinusCellP003Charge2558,
          batchC02701MinusCellP004Charge2558, batchC02701MinusCellP005Charge2558,
      batchC02701MinusCellP006Charge2558, batchC02701MinusCellP007Charge2558,
          batchC02701MinusCellP008Charge2558, batchC02701MinusCellP009Charge2558,
      batchC02701MinusCellP010Charge2558, batchC02701MinusCellP011Charge2558,
          batchC02701MinusCellP012Charge2558, batchC02701MinusCellP013Charge2558,
      batchC02701MinusCellP014Charge2558, batchC02701MinusCellP015Charge2558,
          batchC02701MinusCellP016Charge2558, batchC02701MinusCellP017Charge2558,
      batchC02701MinusCellP018Charge2558, batchC02701MinusCellP019Charge2558,
          batchC02701MinusCellP020Charge2558, batchC02701MinusCellP021Charge2558,
      batchC02701MinusCellP022Charge2558, batchC02701MinusCellP023Charge2558,
          batchC02701MinusCellP024Charge2558, batchC02701MinusCellP025Charge2558,
      batchC02701MinusCellP026Charge2558, batchC02701MinusCellP027Charge2558,
          batchC02701MinusCellP028Charge2558, batchC02701MinusCellP029Charge2558]

theorem batchC02701MinusCellCurvatureBound2558 :
    signedCurvatureUpper2539 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 kernelN02701MinusPosition2555 batchN02702MinusPosition2558 ≤
        batchC02701MinusCellCurvatureUpper2558 := by
  have h := batchC02701MinusCurvature_bound2558
  have ht := batchC02701MinusCellThirdBound2558
  norm_num [batchC02701MinusSignedMidpointUpper2558, batchC02701MinusCellThirdUpper2558,
      batchC02701MinusCellCurvatureUpper2558,
    kernelN02701MinusPosition2555, batchN02702MinusPosition2558] at *
  linarith

theorem batchC02701MinusCellIntegralBound2558 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤ baseCoefficientError2540 i) :
    (∫ x in kernelN02701MinusPosition2555..batchN02702MinusPosition2558,
      ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖) ≤
        batchC02701MinusCellIntegralUpper2558 := by
  have h := weightedPhysical2539_norm_integral_le_signed_cell (-1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541 hcoeff
    (a := kernelN02701MinusPosition2555) (b := batchN02702MinusPosition2558)
    (by norm_num [kernelN02701MinusPosition2555, batchN02702MinusPosition2558])
  have hl := sharedN02701MinusSigned_le2556
  have hr := batchValueN02702MinusSigned_le2558
  have hc := batchC02701MinusCellCurvatureBound2558
  have hleft : sharedN02701MinusPosition2556 = kernelN02701MinusPosition2555 := by
    norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555]
  have hright : batchValueN02702MinusPosition2558 = batchN02702MinusPosition2558 := by
    norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558]
  rw [hleft] at hl
  rw [hright] at hr
  norm_num [kernelN02701MinusPosition2555, batchN02702MinusPosition2558,
      sharedN02701MinusUpper2556,
    batchValueN02702MinusUpper2558, batchC02701MinusCellCurvatureUpper2558,
        batchC02701MinusCellIntegralUpper2558] at *
  linarith

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02701MinusCellChargeBound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusCellThirdBound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusCellCurvatureBound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusCellIntegralBound2558
