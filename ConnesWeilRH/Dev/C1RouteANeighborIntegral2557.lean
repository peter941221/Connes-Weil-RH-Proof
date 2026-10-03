import ConnesWeilRH.Dev.C1RouteANeighborAssembly2557
import ConnesWeilRH.Dev.C1RouteANeighborValueRight2557
import ConnesWeilRH.Dev.C1RouteASharedN02701Plus2556

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def neighborCellP000Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP000ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ + baseCoefficientError2540 ⟨0, by omega⟩) *
      neighborThirdCell2557 ⟨0, by omega⟩ ≤ neighborCellP000Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨0, by omega⟩ ≤ ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP000NormUpper2557, neighborRightP000NormUpper2557,
      neighborFourthUpper2557, neighborFourthP000Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ +
      baseCoefficientError2540 ⟨0, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP000Charge2557]

noncomputable def neighborCellP001Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP001ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ + baseCoefficientError2540 ⟨1, by omega⟩) *
      neighborThirdCell2557 ⟨1, by omega⟩ ≤ neighborCellP001Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨1, by omega⟩ ≤ ((19799247159552321359 : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP001NormUpper2557, neighborRightP001NormUpper2557,
      neighborFourthUpper2557, neighborFourthP001Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ +
      baseCoefficientError2540 ⟨1, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP001Charge2557]

noncomputable def neighborCellP002Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP002ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ + baseCoefficientError2540 ⟨2, by omega⟩) *
      neighborThirdCell2557 ⟨2, by omega⟩ ≤ neighborCellP002Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨2, by omega⟩ ≤ ((286789116650650663565686765163451207 : ℝ) /
        (299315535325368917 * 10^40
        + 6481146537402947624255349848014848000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP002NormUpper2557, neighborRightP002NormUpper2557,
      neighborFourthUpper2557, neighborFourthP002Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ +
      baseCoefficientError2540 ⟨2, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP002Charge2557]

noncomputable def neighborCellP003Charge2557 : ℝ := ((767 : ℝ) /
        125000)

theorem neighborCellP003ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ + baseCoefficientError2540 ⟨3, by omega⟩) *
      neighborThirdCell2557 ⟨3, by omega⟩ ≤ neighborCellP003Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨3, by omega⟩ ≤ (((8779 * 10^40
        + 8767775537733971787150261862995492264637) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP003NormUpper2557, neighborRightP003NormUpper2557,
      neighborFourthUpper2557, neighborFourthP003Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ +
      baseCoefficientError2540 ⟨3, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP003Charge2557]

noncomputable def neighborCellP004Charge2557 : ℝ := ((107 : ℝ) /
        40000)

theorem neighborCellP004ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ + baseCoefficientError2540 ⟨4, by omega⟩) *
      neighborThirdCell2557 ⟨4, by omega⟩ ≤ neighborCellP004Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨4, by omega⟩ ≤ (((1830180 * 10^40
        + 557432440421360861673688430276956324613) : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP004NormUpper2557, neighborRightP004NormUpper2557,
      neighborFourthUpper2557, neighborFourthP004Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ +
      baseCoefficientError2540 ⟨4, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP004Charge2557]

noncomputable def neighborCellP005Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP005ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ + baseCoefficientError2540 ⟨5, by omega⟩) *
      neighborThirdCell2557 ⟨5, by omega⟩ ≤ neighborCellP005Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨5, by omega⟩ ≤ ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP005NormUpper2557, neighborRightP005NormUpper2557,
      neighborFourthUpper2557, neighborFourthP005Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ +
      baseCoefficientError2540 ⟨5, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP005Charge2557]

noncomputable def neighborCellP006Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP006ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ + baseCoefficientError2540 ⟨6, by omega⟩) *
      neighborThirdCell2557 ⟨6, by omega⟩ ≤ neighborCellP006Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨6, by omega⟩ ≤ ((9969546890060584574742440076011 : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP006NormUpper2557, neighborRightP006NormUpper2557,
      neighborFourthUpper2557, neighborFourthP006Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ +
      baseCoefficientError2540 ⟨6, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP006Charge2557]

noncomputable def neighborCellP007Charge2557 : ℝ := ((23 : ℝ) /
        500000)

theorem neighborCellP007ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ + baseCoefficientError2540 ⟨7, by omega⟩) *
      neighborThirdCell2557 ⟨7, by omega⟩ ≤ neighborCellP007Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨7, by omega⟩ ≤ (((5 * 10^40
        + 8660296872434606616143426152377119921201) : ℝ) /
        (299315535325368917 * 10^40
        + 6481146537402947624255349848014848000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP007NormUpper2557, neighborRightP007NormUpper2557,
      neighborFourthUpper2557, neighborFourthP007Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ +
      baseCoefficientError2540 ⟨7, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP007Charge2557]

noncomputable def neighborCellP008Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP008ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ + baseCoefficientError2540 ⟨8, by omega⟩) *
      neighborThirdCell2557 ⟨8, by omega⟩ ≤ neighborCellP008Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨8, by omega⟩ ≤ ((391934981693579938445124443998941961 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP008NormUpper2557, neighborRightP008NormUpper2557,
      neighborFourthUpper2557, neighborFourthP008Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ +
      baseCoefficientError2540 ⟨8, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP008Charge2557]

noncomputable def neighborCellP009Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP009ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ + baseCoefficientError2540 ⟨9, by omega⟩) *
      neighborThirdCell2557 ⟨9, by omega⟩ ≤ neighborCellP009Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨9, by omega⟩ ≤ ((391936393265002891514810024091964899 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP009NormUpper2557, neighborRightP009NormUpper2557,
      neighborFourthUpper2557, neighborFourthP009Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ +
      baseCoefficientError2540 ⟨9, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP009Charge2557]

noncomputable def neighborCellP010Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP010ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ + baseCoefficientError2540 ⟨10, by omega⟩) *
      neighborThirdCell2557 ⟨10, by omega⟩ ≤ neighborCellP010Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨10, by omega⟩ ≤ ((391937210933557381276397182144478253 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP010NormUpper2557, neighborRightP010NormUpper2557,
      neighborFourthUpper2557, neighborFourthP010Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ +
      baseCoefficientError2540 ⟨10, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP010Charge2557]

noncomputable def neighborCellP011Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP011ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ + baseCoefficientError2540 ⟨11, by omega⟩) *
      neighborThirdCell2557 ⟨11, by omega⟩ ≤ neighborCellP011Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨11, by omega⟩ ≤ ((6124027439522497621370051663529223 : ℝ) /
        (233840261972944466 * 10^40
        + 9125895732346052831449492068761600000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP011NormUpper2557, neighborRightP011NormUpper2557,
      neighborFourthUpper2557, neighborFourthP011Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ +
      baseCoefficientError2540 ⟨11, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP011Charge2557]

noncomputable def neighborCellP012Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP012ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ + baseCoefficientError2540 ⟨12, by omega⟩) *
      neighborThirdCell2557 ⟨12, by omega⟩ ≤ neighborCellP012Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨12, by omega⟩ ≤ ((391938320837653515587631224266002539 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP012NormUpper2557, neighborRightP012NormUpper2557,
      neighborFourthUpper2557, neighborFourthP012Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ +
      baseCoefficientError2540 ⟨12, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP012Charge2557]

noncomputable def neighborCellP013Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP013ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ + baseCoefficientError2540 ⟨13, by omega⟩) *
      neighborThirdCell2557 ⟨13, by omega⟩ ≤ neighborCellP013Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨13, by omega⟩ ≤ ((391938835460815551193189440210469647 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP013NormUpper2557, neighborRightP013NormUpper2557,
      neighborFourthUpper2557, neighborFourthP013Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ +
      baseCoefficientError2540 ⟨13, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP013Charge2557]

noncomputable def neighborCellP014Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP014ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ + baseCoefficientError2540 ⟨14, by omega⟩) *
      neighborThirdCell2557 ⟨14, by omega⟩ ≤ neighborCellP014Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨14, by omega⟩ ≤ ((195969894514396403053366847968307689 : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP014NormUpper2557, neighborRightP014NormUpper2557,
      neighborFourthUpper2557, neighborFourthP014Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ +
      baseCoefficientError2540 ⟨14, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP014Charge2557]

noncomputable def neighborCellP015Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP015ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ + baseCoefficientError2540 ⟨15, by omega⟩) *
      neighborThirdCell2557 ⟨15, by omega⟩ ≤ neighborCellP015Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨15, by omega⟩ ≤ ((39194047227800717085148563380196049 : ℝ) /
        (1496577676626844588 * 10^40
        + 2405732687014738121276749240074240000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP015NormUpper2557, neighborRightP015NormUpper2557,
      neighborFourthUpper2557, neighborFourthP015Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ +
      baseCoefficientError2540 ⟨15, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP015Charge2557]

noncomputable def neighborCellP016Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP016ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ + baseCoefficientError2540 ⟨16, by omega⟩) *
      neighborThirdCell2557 ⟨16, by omega⟩ ≤ neighborCellP016Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨16, by omega⟩ ≤ ((195970483026557634184711267520990819 : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP016NormUpper2557, neighborRightP016NormUpper2557,
      neighborFourthUpper2557, neighborFourthP016Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ +
      baseCoefficientError2540 ⟨16, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP016Charge2557]

noncomputable def neighborCellP017Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP017ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ + baseCoefficientError2540 ⟨17, by omega⟩) *
      neighborThirdCell2557 ⟨17, by omega⟩ ≤ neighborCellP017Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨17, by omega⟩ ≤ ((15677677007668183164973455065240797 : ℝ) /
        (598631070650737835 * 10^40
        + 2962293074805895248510699696029696000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP017NormUpper2557, neighborRightP017NormUpper2557,
      neighborFourthUpper2557, neighborFourthP017Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ +
      baseCoefficientError2540 ⟨17, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP017Charge2557]

noncomputable def neighborCellP018Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP018ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ + baseCoefficientError2540 ⟨18, by omega⟩) *
      neighborThirdCell2557 ⟨18, by omega⟩ ≤ neighborCellP018Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨18, by omega⟩ ≤ ((391942287824877348613843841050765257 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP018NormUpper2557, neighborRightP018NormUpper2557,
      neighborFourthUpper2557, neighborFourthP018Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ +
      baseCoefficientError2540 ⟨18, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP018Charge2557]

noncomputable def neighborCellP019Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP019ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ + baseCoefficientError2540 ⟨19, by omega⟩) *
      neighborThirdCell2557 ⟨19, by omega⟩ ≤ neighborCellP019Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨19, by omega⟩ ≤ ((391942943205567147858788489111210109 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP019NormUpper2557, neighborRightP019NormUpper2557,
      neighborFourthUpper2557, neighborFourthP019Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ +
      baseCoefficientError2540 ⟨19, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP019Charge2557]

noncomputable def neighborCellP020Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP020ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ + baseCoefficientError2540 ⟨20, by omega⟩) *
      neighborThirdCell2557 ⟨20, by omega⟩ ≤ neighborCellP020Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨20, by omega⟩ ≤ ((195971827942299816711395829989617769 : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP020NormUpper2557, neighborRightP020NormUpper2557,
      neighborFourthUpper2557, neighborFourthP020Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ +
      baseCoefficientError2540 ⟨20, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP020Charge2557]

noncomputable def neighborCellP021Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP021ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ + baseCoefficientError2540 ⟨21, by omega⟩) *
      neighborThirdCell2557 ⟨21, by omega⟩ ≤ neighborCellP021Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨21, by omega⟩ ≤ ((97986062661633021216188201305894021 : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP021NormUpper2557, neighborRightP021NormUpper2557,
      neighborFourthUpper2557, neighborFourthP021Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ +
      baseCoefficientError2540 ⟨21, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP021Charge2557]

noncomputable def neighborCellP022Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP022ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ + baseCoefficientError2540 ⟨22, by omega⟩) *
      neighborThirdCell2557 ⟨22, by omega⟩ ≤ neighborCellP022Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨22, by omega⟩ ≤ ((391944555068705155781108614729827467 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP022NormUpper2557, neighborRightP022NormUpper2557,
      neighborFourthUpper2557, neighborFourthP022Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ +
      baseCoefficientError2540 ⟨22, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP022Charge2557]

noncomputable def neighborCellP023Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP023ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ + baseCoefficientError2540 ⟨23, by omega⟩) *
      neighborThirdCell2557 ⟨23, by omega⟩ ≤ neighborCellP023Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨23, by omega⟩ ≤ ((78389086555618266911257185599327113 : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP023NormUpper2557, neighborRightP023NormUpper2557,
      neighborFourthUpper2557, neighborFourthP023Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ +
      baseCoefficientError2540 ⟨23, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP023Charge2557]

noncomputable def neighborCellP024Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP024ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ + baseCoefficientError2540 ⟨24, by omega⟩) *
      neighborThirdCell2557 ⟨24, by omega⟩ ≤ neighborCellP024Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨24, by omega⟩ ≤ ((391945836139466669576343253301731477 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP024NormUpper2557, neighborRightP024NormUpper2557,
      neighborFourthUpper2557, neighborFourthP024Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ +
      baseCoefficientError2540 ⟨24, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP024Charge2557]

noncomputable def neighborCellP025Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP025ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ + baseCoefficientError2540 ⟨25, by omega⟩) *
      neighborThirdCell2557 ⟨25, by omega⟩ ≤ neighborCellP025Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨25, by omega⟩ ≤ ((391946341881983451039065744924383453 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP025NormUpper2557, neighborRightP025NormUpper2557,
      neighborFourthUpper2557, neighborFourthP025Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ +
      baseCoefficientError2540 ⟨25, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP025Charge2557]

noncomputable def neighborCellP026Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP026ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ + baseCoefficientError2540 ⟨26, by omega⟩) *
      neighborThirdCell2557 ⟨26, by omega⟩ ≤ neighborCellP026Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨26, by omega⟩ ≤ ((391946858731755673962060088561601507 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP026NormUpper2557, neighborRightP026NormUpper2557,
      neighborFourthUpper2557, neighborFourthP026Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ +
      baseCoefficientError2540 ⟨26, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP026Charge2557]

noncomputable def neighborCellP027Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP027ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ + baseCoefficientError2540 ⟨27, by omega⟩) *
      neighborThirdCell2557 ⟨27, by omega⟩ ≤ neighborCellP027Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨27, by omega⟩ ≤ ((97986901141312419715950223486487169 : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP027NormUpper2557, neighborRightP027NormUpper2557,
      neighborFourthUpper2557, neighborFourthP027Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ +
      baseCoefficientError2540 ⟨27, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP027Charge2557]

noncomputable def neighborCellP028Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP028ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ + baseCoefficientError2540 ⟨28, by omega⟩) *
      neighborThirdCell2557 ⟨28, by omega⟩ ≤ neighborCellP028Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨28, by omega⟩ ≤ ((391947899851734208694146195197450527 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP028NormUpper2557, neighborRightP028NormUpper2557,
      neighborFourthUpper2557, neighborFourthP028Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ +
      baseCoefficientError2540 ⟨28, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP028Charge2557]

noncomputable def neighborCellP029Charge2557 : ℝ := ((1 : ℝ) /
        1000000)

theorem neighborCellP029ChargeBound2557 :
    (‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ + baseCoefficientError2540 ⟨29, by omega⟩) *
      neighborThirdCell2557 ⟨29, by omega⟩ ≤ neighborCellP029Charge2557 := by
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
  have ht : neighborThirdCell2557 ⟨29, by omega⟩ ≤ ((391948349407213147157711135408019547 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold neighborThirdCell2557
    norm_num [neighborLeftNormUpper2557, neighborRightNormUpper2557,
      neighborLeftP029NormUpper2557, neighborRightP029NormUpper2557,
      neighborFourthUpper2557, neighborFourthP029Upper2557,
      kernelN02701PlusPosition2555, neighborRightPosition2557]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ +
      baseCoefficientError2540 ⟨29, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [neighborCellP029Charge2557]

noncomputable def neighborCellCharge2557 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => neighborCellP000Charge2557
  | 1 => neighborCellP001Charge2557
  | 2 => neighborCellP002Charge2557
  | 3 => neighborCellP003Charge2557
  | 4 => neighborCellP004Charge2557
  | 5 => neighborCellP005Charge2557
  | 6 => neighborCellP006Charge2557
  | 7 => neighborCellP007Charge2557
  | 8 => neighborCellP008Charge2557
  | 9 => neighborCellP009Charge2557
  | 10 => neighborCellP010Charge2557
  | 11 => neighborCellP011Charge2557
  | 12 => neighborCellP012Charge2557
  | 13 => neighborCellP013Charge2557
  | 14 => neighborCellP014Charge2557
  | 15 => neighborCellP015Charge2557
  | 16 => neighborCellP016Charge2557
  | 17 => neighborCellP017Charge2557
  | 18 => neighborCellP018Charge2557
  | 19 => neighborCellP019Charge2557
  | 20 => neighborCellP020Charge2557
  | 21 => neighborCellP021Charge2557
  | 22 => neighborCellP022Charge2557
  | 23 => neighborCellP023Charge2557
  | 24 => neighborCellP024Charge2557
  | 25 => neighborCellP025Charge2557
  | 26 => neighborCellP026Charge2557
  | 27 => neighborCellP027Charge2557
  | 28 => neighborCellP028Charge2557
  | 29 => neighborCellP029Charge2557
  | _ => 0

theorem neighborCellChargeBound2557 (i : Fin 30) :
    (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      neighborThirdCell2557 i ≤ neighborCellCharge2557 i := by
  fin_cases i
  · exact neighborCellP000ChargeBound2557
  · exact neighborCellP001ChargeBound2557
  · exact neighborCellP002ChargeBound2557
  · exact neighborCellP003ChargeBound2557
  · exact neighborCellP004ChargeBound2557
  · exact neighborCellP005ChargeBound2557
  · exact neighborCellP006ChargeBound2557
  · exact neighborCellP007ChargeBound2557
  · exact neighborCellP008ChargeBound2557
  · exact neighborCellP009ChargeBound2557
  · exact neighborCellP010ChargeBound2557
  · exact neighborCellP011ChargeBound2557
  · exact neighborCellP012ChargeBound2557
  · exact neighborCellP013ChargeBound2557
  · exact neighborCellP014ChargeBound2557
  · exact neighborCellP015ChargeBound2557
  · exact neighborCellP016ChargeBound2557
  · exact neighborCellP017ChargeBound2557
  · exact neighborCellP018ChargeBound2557
  · exact neighborCellP019ChargeBound2557
  · exact neighborCellP020ChargeBound2557
  · exact neighborCellP021ChargeBound2557
  · exact neighborCellP022ChargeBound2557
  · exact neighborCellP023ChargeBound2557
  · exact neighborCellP024ChargeBound2557
  · exact neighborCellP025ChargeBound2557
  · exact neighborCellP026ChargeBound2557
  · exact neighborCellP027ChargeBound2557
  · exact neighborCellP028ChargeBound2557
  · exact neighborCellP029ChargeBound2557

noncomputable def neighborCellThirdUpper2557 : ℝ := ((2221 : ℝ) /
        250000)

noncomputable def neighborCellCurvatureUpper2557 : ℝ := ((181 : ℝ) /
        1000000)

noncomputable def neighborCellIntegralUpper2557 : ℝ := ((111 : ℝ) /
        1000000000000)

theorem neighborCellThirdBound2557 : neighborThirdAggregate2557 ≤ neighborCellThirdUpper2557 := by
  have h : neighborThirdAggregate2557 ≤ ∑ i : Fin 30, neighborCellCharge2557 i :=
    Finset.sum_le_sum (fun i _ => neighborCellChargeBound2557 i)
  apply h.trans
  rw [sum30_chain2541]
  norm_num [neighborCellCharge2557, neighborCellThirdUpper2557, neighborCellP000Charge2557,
      neighborCellP001Charge2557,
      neighborCellP002Charge2557, neighborCellP003Charge2557, neighborCellP004Charge2557,
          neighborCellP005Charge2557,
      neighborCellP006Charge2557, neighborCellP007Charge2557, neighborCellP008Charge2557,
          neighborCellP009Charge2557,
      neighborCellP010Charge2557, neighborCellP011Charge2557, neighborCellP012Charge2557,
          neighborCellP013Charge2557,
      neighborCellP014Charge2557, neighborCellP015Charge2557, neighborCellP016Charge2557,
          neighborCellP017Charge2557,
      neighborCellP018Charge2557, neighborCellP019Charge2557, neighborCellP020Charge2557,
          neighborCellP021Charge2557,
      neighborCellP022Charge2557, neighborCellP023Charge2557, neighborCellP024Charge2557,
          neighborCellP025Charge2557,
      neighborCellP026Charge2557, neighborCellP027Charge2557, neighborCellP028Charge2557,
          neighborCellP029Charge2557]

theorem neighborCellCurvatureBound2557 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 kernelN02701PlusPosition2555 neighborRightPosition2557 ≤
        neighborCellCurvatureUpper2557 := by
  have h := neighborCurvature_bound2557
  have ht := neighborCellThirdBound2557
  norm_num [neighborSignedMidpointUpper2557, neighborCellThirdUpper2557,
      neighborCellCurvatureUpper2557,
    kernelN02701PlusPosition2555, neighborRightPosition2557] at *
  linarith

theorem neighborCellIntegralBound2557 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤ baseCoefficientError2540 i) :
    (∫ x in kernelN02701PlusPosition2555..neighborRightPosition2557,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤
        neighborCellIntegralUpper2557 := by
  have h := weightedPhysical2539_norm_integral_le_signed_cell (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541 hcoeff
    (a := kernelN02701PlusPosition2555) (b := neighborRightPosition2557)
    (by norm_num [kernelN02701PlusPosition2555, neighborRightPosition2557])
  have hl := sharedN02701PlusSigned_le2556
  have hr := neighborValueRightSigned_le2557
  have hc := neighborCellCurvatureBound2557
  have hleft : sharedN02701PlusPosition2556 = kernelN02701PlusPosition2555 := by
    norm_num [sharedN02701PlusPosition2556, kernelN02701PlusPosition2555]
  have hright : neighborValueRightPosition2557 = neighborRightPosition2557 := by
    norm_num [neighborValueRightPosition2557, neighborRightPosition2557]
  rw [hleft] at hl
  rw [hright] at hr
  norm_num [kernelN02701PlusPosition2555, neighborRightPosition2557, sharedN02701PlusUpper2556,
    neighborValueRightUpper2557, neighborCellCurvatureUpper2557, neighborCellIntegralUpper2557] at
        *
  linarith

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.neighborCellChargeBound2557
#print axioms ConnesWeilRH.Dev.neighborCellThirdBound2557
#print axioms ConnesWeilRH.Dev.neighborCellCurvatureBound2557
#print axioms ConnesWeilRH.Dev.neighborCellIntegralBound2557
