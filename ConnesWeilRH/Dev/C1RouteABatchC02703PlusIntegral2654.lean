import ConnesWeilRH.Dev.C1RouteABatchC02703PlusAssembly2654
import ConnesWeilRH.Dev.C1RouteABatchValueN02704Plus2654
import ConnesWeilRH.Dev.C1RouteABatchValueN02703Plus2654

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def batchC02703PlusCellP000Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP000ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ + baseCoefficientError2540 ⟨0, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨0, by omega⟩ ≤ batchC02703PlusCellP000Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨0, by omega⟩ ≤ ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP000NormUpper2654, batchC02703PlusRightP000NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP000Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ +
      baseCoefficientError2540 ⟨0, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP000Charge2654]

noncomputable def batchC02703PlusCellP001Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP001ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ + baseCoefficientError2540 ⟨1, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨1, by omega⟩ ≤ batchC02703PlusCellP001Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨1, by omega⟩ ≤ ((93693587202928785719 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP001NormUpper2654, batchC02703PlusRightP001NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP001Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ +
      baseCoefficientError2540 ⟨1, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP001Charge2654]

noncomputable def batchC02703PlusCellP002Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP002ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ + baseCoefficientError2540 ⟨2, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨2, by omega⟩ ≤ batchC02703PlusCellP002Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨2, by omega⟩ ≤ ((15859659280141796474424100241986122909
      : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP002NormUpper2654, batchC02703PlusRightP002NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP002Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ +
      baseCoefficientError2540 ⟨2, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP002Charge2654]

noncomputable def batchC02703PlusCellP003Charge2654 : ℝ := ((3183 : ℝ) /
        500000)

theorem batchC02703PlusCellP003ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ + baseCoefficientError2540 ⟨3, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨3, by omega⟩ ≤ batchC02703PlusCellP003Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨3, by omega⟩ ≤ (((4554 * 10^40
        + 6708821653520267628077575518344880819717) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP003NormUpper2654, batchC02703PlusRightP003NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP003Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ +
      baseCoefficientError2540 ⟨3, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP003Charge2654]

noncomputable def batchC02703PlusCellP004Charge2654 : ℝ := ((2727 : ℝ) /
        1000000)

theorem batchC02703PlusCellP004ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ + baseCoefficientError2540 ⟨4, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨4, by omega⟩ ≤ batchC02703PlusCellP004Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨4, by omega⟩ ≤ (((233245 * 10^40
        + 1728462141501977596914933867809965875711) : ℝ) /
        (935361047891777867 * 10^40
        + 6503582929384211325797968275046400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP004NormUpper2654, batchC02703PlusRightP004NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP004Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ +
      baseCoefficientError2540 ⟨4, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP004Charge2654]

noncomputable def batchC02703PlusCellP005Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP005ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ + baseCoefficientError2540 ⟨5, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨5, by omega⟩ ≤ batchC02703PlusCellP005Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨5, by omega⟩ ≤ ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP005NormUpper2654, batchC02703PlusRightP005NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP005Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ +
      baseCoefficientError2540 ⟨5, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP005Charge2654]

noncomputable def batchC02703PlusCellP006Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP006ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ + baseCoefficientError2540 ⟨6, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨6, by omega⟩ ≤ batchC02703PlusCellP006Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨6, by omega⟩ ≤ ((23575433847579963746715022380231 : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP006NormUpper2654, batchC02703PlusRightP006NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP006Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ +
      baseCoefficientError2540 ⟨6, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP006Charge2654]

noncomputable def batchC02703PlusCellP007Charge2654 : ℝ := ((3 : ℝ) /
        62500)

theorem batchC02703PlusCellP007ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ + baseCoefficientError2540 ⟨7, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨7, by omega⟩ ≤ batchC02703PlusCellP007Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨7, by omega⟩ ≤ (((37 * 10^40
        + 7936958621246386238273257721518450036873) : ℝ) /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP007NormUpper2654, batchC02703PlusRightP007NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP007Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ +
      baseCoefficientError2540 ⟨7, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP007Charge2654]

noncomputable def batchC02703PlusCellP008Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP008ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ + baseCoefficientError2540 ⟨8, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨8, by omega⟩ ≤ batchC02703PlusCellP008Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨8, by omega⟩ ≤ ((1518577577907063919599249902010067 : ℝ)
      /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP008NormUpper2654, batchC02703PlusRightP008NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP008Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ +
      baseCoefficientError2540 ⟨8, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP008Charge2654]

noncomputable def batchC02703PlusCellP009Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP009ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ + baseCoefficientError2540 ⟨9, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨9, by omega⟩ ≤ batchC02703PlusCellP009Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨9, by omega⟩ ≤ ((1518599618234256578845430000929089 : ℝ)
      /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP009NormUpper2654, batchC02703PlusRightP009NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP009Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ +
      baseCoefficientError2540 ⟨9, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP009Charge2654]

noncomputable def batchC02703PlusCellP010Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP010ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ + baseCoefficientError2540 ⟨10, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨10, by omega⟩ ≤ batchC02703PlusCellP010Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨10, by omega⟩ ≤ ((379653096356203900878674545695599 : ℝ)
      /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP010NormUpper2654, batchC02703PlusRightP010NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP010Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ +
      baseCoefficientError2540 ⟨10, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP010Charge2654]

noncomputable def batchC02703PlusCellP011Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP011ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ + baseCoefficientError2540 ⟨11, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨11, by omega⟩ ≤ batchC02703PlusCellP011Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨11, by omega⟩ ≤ ((151862089822326079027970941632197 : ℝ)
      /
        (1496577676626844588 * 10^40
        + 2405732687014738121276749240074240000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP011NormUpper2654, batchC02703PlusRightP011NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP011Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ +
      baseCoefficientError2540 ⟨11, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP011Charge2654]

noncomputable def batchC02703PlusCellP012Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP012ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ + baseCoefficientError2540 ⟨12, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨12, by omega⟩ ≤ batchC02703PlusCellP012Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨12, by omega⟩ ≤ ((1518629715719873773132598414562123 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP012NormUpper2654, batchC02703PlusRightP012NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP012Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ +
      baseCoefficientError2540 ⟨12, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP012Charge2654]

noncomputable def batchC02703PlusCellP013Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP013ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ + baseCoefficientError2540 ⟨13, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨13, by omega⟩ ≤ batchC02703PlusCellP013Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨13, by omega⟩ ≤ ((1518637751201244386783006055390563 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP013NormUpper2654, batchC02703PlusRightP013NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP013Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ +
      baseCoefficientError2540 ⟨13, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP013Charge2654]

noncomputable def batchC02703PlusCellP014Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP014ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ + baseCoefficientError2540 ⟨14, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨14, by omega⟩ ≤ batchC02703PlusCellP014Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨14, by omega⟩ ≤ ((1518652640563390500451882123462543 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP014NormUpper2654, batchC02703PlusRightP014NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP014Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ +
      baseCoefficientError2540 ⟨14, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP014Charge2654]

noncomputable def batchC02703PlusCellP015Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP015ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ + baseCoefficientError2540 ⟨15, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨15, by omega⟩ ≤ batchC02703PlusCellP015Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨15, by omega⟩ ≤ ((1518663309119708066120904603767153 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP015NormUpper2654, batchC02703PlusRightP015NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP015Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ +
      baseCoefficientError2540 ⟨15, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP015Charge2654]

noncomputable def batchC02703PlusCellP016Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP016ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ + baseCoefficientError2540 ⟨16, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨16, by omega⟩ ≤ batchC02703PlusCellP016Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨16, by omega⟩ ≤ ((47458469349056162792110185868987 : ℝ)
      /
        (467680523945888933 * 10^40
        + 8251791464692105662898984137523200000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP016NormUpper2654, batchC02703PlusRightP016NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP016Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ +
      baseCoefficientError2540 ⟨16, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP016Charge2654]

noncomputable def batchC02703PlusCellP017Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP017ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ + baseCoefficientError2540 ⟨17, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨17, by omega⟩ ≤ batchC02703PlusCellP017Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨17, by omega⟩ ≤ ((1518685995700262218532403036775857 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP017NormUpper2654, batchC02703PlusRightP017NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP017Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ +
      baseCoefficientError2540 ⟨17, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP017Charge2654]

noncomputable def batchC02703PlusCellP018Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP018ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ + baseCoefficientError2540 ⟨18, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨18, by omega⟩ ≤ batchC02703PlusCellP018Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨18, by omega⟩ ≤ ((379672914520210859738183328378747 : ℝ)
      /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP018NormUpper2654, batchC02703PlusRightP018NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP018Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ +
      baseCoefficientError2540 ⟨18, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP018Charge2654]

noncomputable def batchC02703PlusCellP019Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP019ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ + baseCoefficientError2540 ⟨19, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨19, by omega⟩ ≤ batchC02703PlusCellP019Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨19, by omega⟩ ≤ ((303740378326839515445943291356613 : ℝ)
      /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP019NormUpper2654, batchC02703PlusRightP019NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP019Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ +
      baseCoefficientError2540 ⟨19, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP019Charge2654]

noncomputable def batchC02703PlusCellP020Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP020ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ + baseCoefficientError2540 ⟨20, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨20, by omega⟩ ≤ batchC02703PlusCellP020Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨20, by omega⟩ ≤ ((1518713019926722592488449662793803 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP020NormUpper2654, batchC02703PlusRightP020NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP020Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ +
      baseCoefficientError2540 ⟨20, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP020Charge2654]

noncomputable def batchC02703PlusCellP021Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP021ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ + baseCoefficientError2540 ⟨21, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨21, by omega⟩ ≤ batchC02703PlusCellP021Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨21, by omega⟩ ≤ ((759361153505352192091501082868511 : ℝ)
      /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP021NormUpper2654, batchC02703PlusRightP021NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP021Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ +
      baseCoefficientError2540 ⟨21, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP021Charge2654]

noncomputable def batchC02703PlusCellP022Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP022ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ + baseCoefficientError2540 ⟨22, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨22, by omega⟩ ≤ batchC02703PlusCellP022Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨22, by omega⟩ ≤ ((759363530256076278693479908293863 : ℝ)
      /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP022NormUpper2654, batchC02703PlusRightP022NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP022Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ +
      baseCoefficientError2540 ⟨22, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP022Charge2654]

noncomputable def batchC02703PlusCellP023Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP023ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ + baseCoefficientError2540 ⟨23, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨23, by omega⟩ ≤ batchC02703PlusCellP023Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨23, by omega⟩ ≤ ((18984259573063517131820404680641 : ℝ)
      /
        (187072209578355573 * 10^40
        + 5300716585876842265159593655009280000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP023NormUpper2654, batchC02703PlusRightP023NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP023Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ +
      baseCoefficientError2540 ⟨23, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP023Charge2654]

noncomputable def batchC02703PlusCellP024Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP024ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ + baseCoefficientError2540 ⟨24, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨24, by omega⟩ ≤ batchC02703PlusCellP024Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨24, by omega⟩ ≤ ((1518747064310945819121969295341603 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP024NormUpper2654, batchC02703PlusRightP024NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP024Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ +
      baseCoefficientError2540 ⟨24, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP024Charge2654]

noncomputable def batchC02703PlusCellP025Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP025ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ + baseCoefficientError2540 ⟨25, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨25, by omega⟩ ≤ batchC02703PlusCellP025Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨25, by omega⟩ ≤ ((94922185092106127924293784191227 : ℝ)
      /
        (935361047891777867 * 10^40
        + 6503582929384211325797968275046400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP025NormUpper2654, batchC02703PlusRightP025NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP025Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ +
      baseCoefficientError2540 ⟨25, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP025Charge2654]

noncomputable def batchC02703PlusCellP026Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP026ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ + baseCoefficientError2540 ⟨26, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨26, by omega⟩ ≤ batchC02703PlusCellP026Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨26, by omega⟩ ≤ ((1518763032100181235141855197968117 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP026NormUpper2654, batchC02703PlusRightP026NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP026Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ +
      baseCoefficientError2540 ⟨26, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP026Charge2654]

noncomputable def batchC02703PlusCellP027Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP027ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ + baseCoefficientError2540 ⟨27, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨27, by omega⟩ ≤ batchC02703PlusCellP027Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨27, by omega⟩ ≤ ((1518774678358051161002154056231801 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP027NormUpper2654, batchC02703PlusRightP027NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP027Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ +
      baseCoefficientError2540 ⟨27, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP027Charge2654]

noncomputable def batchC02703PlusCellP028Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP028ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ + baseCoefficientError2540 ⟨28, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨28, by omega⟩ ≤ batchC02703PlusCellP028Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨28, by omega⟩ ≤ ((379694822324345482661951204589371 : ℝ)
      /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP028NormUpper2654, batchC02703PlusRightP028NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP028Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ +
      baseCoefficientError2540 ⟨28, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP028Charge2654]

noncomputable def batchC02703PlusCellP029Charge2654 : ℝ := ((1 : ℝ) /
        1000000)

theorem batchC02703PlusCellP029ChargeBound2654 :
    (‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ + baseCoefficientError2540 ⟨29, by omega⟩) *
      batchC02703PlusThirdCell2654 ⟨29, by omega⟩ ≤ batchC02703PlusCellP029Charge2654 := by
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
  have ht : batchC02703PlusThirdCell2654 ⟨29, by omega⟩ ≤ ((1518786309183671602635028548630181 :
      ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold batchC02703PlusThirdCell2654
    norm_num [batchC02703PlusLeftNormUpper2654, batchC02703PlusRightNormUpper2654,
      batchC02703PlusLeftP029NormUpper2654, batchC02703PlusRightP029NormUpper2654,
      batchC02703PlusFourthUpper2654, batchC02703PlusFourthP029Upper2654,
      batchN02703PlusPosition2654, batchN02704PlusPosition2654]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ +
      baseCoefficientError2540 ⟨29, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [batchC02703PlusCellP029Charge2654]

noncomputable def batchC02703PlusCellCharge2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02703PlusCellP000Charge2654
  | 1 => batchC02703PlusCellP001Charge2654
  | 2 => batchC02703PlusCellP002Charge2654
  | 3 => batchC02703PlusCellP003Charge2654
  | 4 => batchC02703PlusCellP004Charge2654
  | 5 => batchC02703PlusCellP005Charge2654
  | 6 => batchC02703PlusCellP006Charge2654
  | 7 => batchC02703PlusCellP007Charge2654
  | 8 => batchC02703PlusCellP008Charge2654
  | 9 => batchC02703PlusCellP009Charge2654
  | 10 => batchC02703PlusCellP010Charge2654
  | 11 => batchC02703PlusCellP011Charge2654
  | 12 => batchC02703PlusCellP012Charge2654
  | 13 => batchC02703PlusCellP013Charge2654
  | 14 => batchC02703PlusCellP014Charge2654
  | 15 => batchC02703PlusCellP015Charge2654
  | 16 => batchC02703PlusCellP016Charge2654
  | 17 => batchC02703PlusCellP017Charge2654
  | 18 => batchC02703PlusCellP018Charge2654
  | 19 => batchC02703PlusCellP019Charge2654
  | 20 => batchC02703PlusCellP020Charge2654
  | 21 => batchC02703PlusCellP021Charge2654
  | 22 => batchC02703PlusCellP022Charge2654
  | 23 => batchC02703PlusCellP023Charge2654
  | 24 => batchC02703PlusCellP024Charge2654
  | 25 => batchC02703PlusCellP025Charge2654
  | 26 => batchC02703PlusCellP026Charge2654
  | 27 => batchC02703PlusCellP027Charge2654
  | 28 => batchC02703PlusCellP028Charge2654
  | 29 => batchC02703PlusCellP029Charge2654
  | _ => 0

theorem batchC02703PlusCellChargeBound2654 (i : Fin 30) :
    (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC02703PlusThirdCell2654 i ≤ batchC02703PlusCellCharge2654 i := by
  fin_cases i
  · exact batchC02703PlusCellP000ChargeBound2654
  · exact batchC02703PlusCellP001ChargeBound2654
  · exact batchC02703PlusCellP002ChargeBound2654
  · exact batchC02703PlusCellP003ChargeBound2654
  · exact batchC02703PlusCellP004ChargeBound2654
  · exact batchC02703PlusCellP005ChargeBound2654
  · exact batchC02703PlusCellP006ChargeBound2654
  · exact batchC02703PlusCellP007ChargeBound2654
  · exact batchC02703PlusCellP008ChargeBound2654
  · exact batchC02703PlusCellP009ChargeBound2654
  · exact batchC02703PlusCellP010ChargeBound2654
  · exact batchC02703PlusCellP011ChargeBound2654
  · exact batchC02703PlusCellP012ChargeBound2654
  · exact batchC02703PlusCellP013ChargeBound2654
  · exact batchC02703PlusCellP014ChargeBound2654
  · exact batchC02703PlusCellP015ChargeBound2654
  · exact batchC02703PlusCellP016ChargeBound2654
  · exact batchC02703PlusCellP017ChargeBound2654
  · exact batchC02703PlusCellP018ChargeBound2654
  · exact batchC02703PlusCellP019ChargeBound2654
  · exact batchC02703PlusCellP020ChargeBound2654
  · exact batchC02703PlusCellP021ChargeBound2654
  · exact batchC02703PlusCellP022ChargeBound2654
  · exact batchC02703PlusCellP023ChargeBound2654
  · exact batchC02703PlusCellP024ChargeBound2654
  · exact batchC02703PlusCellP025ChargeBound2654
  · exact batchC02703PlusCellP026ChargeBound2654
  · exact batchC02703PlusCellP027ChargeBound2654
  · exact batchC02703PlusCellP028ChargeBound2654
  · exact batchC02703PlusCellP029ChargeBound2654

noncomputable def batchC02703PlusCellThirdUpper2654 : ℝ := ((573 : ℝ) /
        62500)

noncomputable def batchC02703PlusCellCurvatureUpper2654 : ℝ := ((9 : ℝ) /
        50000)

noncomputable def batchC02703PlusCellIntegralUpper2654 : ℝ := ((13 : ℝ) /
        125000000000)

theorem batchC02703PlusCellThirdBound2654 : batchC02703PlusThirdAggregate2654 ≤
    batchC02703PlusCellThirdUpper2654 := by
  have h : batchC02703PlusThirdAggregate2654 ≤ ∑ i : Fin 30, batchC02703PlusCellCharge2654 i :=
    Finset.sum_le_sum (fun i _ => batchC02703PlusCellChargeBound2654 i)
  apply h.trans
  rw [sum30_chain2541]
  norm_num [batchC02703PlusCellCharge2654, batchC02703PlusCellThirdUpper2654,
      batchC02703PlusCellP000Charge2654, batchC02703PlusCellP001Charge2654,
      batchC02703PlusCellP002Charge2654, batchC02703PlusCellP003Charge2654,
          batchC02703PlusCellP004Charge2654, batchC02703PlusCellP005Charge2654,
      batchC02703PlusCellP006Charge2654, batchC02703PlusCellP007Charge2654,
          batchC02703PlusCellP008Charge2654, batchC02703PlusCellP009Charge2654,
      batchC02703PlusCellP010Charge2654, batchC02703PlusCellP011Charge2654,
          batchC02703PlusCellP012Charge2654, batchC02703PlusCellP013Charge2654,
      batchC02703PlusCellP014Charge2654, batchC02703PlusCellP015Charge2654,
          batchC02703PlusCellP016Charge2654, batchC02703PlusCellP017Charge2654,
      batchC02703PlusCellP018Charge2654, batchC02703PlusCellP019Charge2654,
          batchC02703PlusCellP020Charge2654, batchC02703PlusCellP021Charge2654,
      batchC02703PlusCellP022Charge2654, batchC02703PlusCellP023Charge2654,
          batchC02703PlusCellP024Charge2654, batchC02703PlusCellP025Charge2654,
      batchC02703PlusCellP026Charge2654, batchC02703PlusCellP027Charge2654,
          batchC02703PlusCellP028Charge2654, batchC02703PlusCellP029Charge2654]

theorem batchC02703PlusCellCurvatureBound2654 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN02703PlusPosition2654 batchN02704PlusPosition2654 ≤
        batchC02703PlusCellCurvatureUpper2654 := by
  have h := batchC02703PlusCurvature_bound2654
  have ht := batchC02703PlusCellThirdBound2654
  norm_num [batchC02703PlusSignedMidpointUpper2654, batchC02703PlusCellThirdUpper2654,
      batchC02703PlusCellCurvatureUpper2654,
    batchN02703PlusPosition2654, batchN02704PlusPosition2654] at *
  linarith

theorem batchC02703PlusCellIntegralBound2654 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤ baseCoefficientError2540 i) :
    (∫ x in batchN02703PlusPosition2654..batchN02704PlusPosition2654,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤
        batchC02703PlusCellIntegralUpper2654 := by
  have h := weightedPhysical2539_norm_integral_le_signed_cell (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541 hcoeff
    (a := batchN02703PlusPosition2654) (b := batchN02704PlusPosition2654)
    (by norm_num [batchN02703PlusPosition2654, batchN02704PlusPosition2654])
  have hl := batchValueN02703PlusSigned_le2654
  have hr := batchValueN02704PlusSigned_le2654
  have hc := batchC02703PlusCellCurvatureBound2654
  have hleft : batchValueN02703PlusPosition2654 = batchN02703PlusPosition2654 := by
    norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654]
  have hright : batchValueN02704PlusPosition2654 = batchN02704PlusPosition2654 := by
    norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654]
  rw [hleft] at hl
  rw [hright] at hr
  norm_num [batchN02703PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02703PlusUpper2654,
    batchValueN02704PlusUpper2654, batchC02703PlusCellCurvatureUpper2654,
        batchC02703PlusCellIntegralUpper2654] at *
  linarith

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02703PlusCellChargeBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusCellThirdBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusCellCurvatureBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusCellIntegralBound2654
