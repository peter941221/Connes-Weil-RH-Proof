import ConnesWeilRH.Dev.C1RouteABoundaryAssembly2550
import ConnesWeilRH.Dev.C1RouteABoundaryValueRight2551
import ConnesWeilRH.Dev.C1RouteABoundaryValueLeft2551

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def boundaryCellP000Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP000ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ + baseCoefficientError2540 ⟨0, by omega⟩) *
      edgeThirdCell2550 ⟨0, by omega⟩ ≤ boundaryCellP000Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨0, by omega⟩ ≤ ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP000NormUpper2549, edgeRightP000NormUpper2549,
      edgeFourthUpper2550, edgeFourthP000Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨0, by omega⟩‖ +
      baseCoefficientError2540 ⟨0, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP000Charge2551]

noncomputable def boundaryCellP001Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP001ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ + baseCoefficientError2540 ⟨1, by omega⟩) *
      edgeThirdCell2550 ⟨1, by omega⟩ ≤ boundaryCellP001Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨1, by omega⟩ ≤ ((20356111266665792517 : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP001NormUpper2549, edgeRightP001NormUpper2549,
      edgeFourthUpper2550, edgeFourthP001Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨1, by omega⟩‖ +
      baseCoefficientError2540 ⟨1, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP001Charge2551]

noncomputable def boundaryCellP002Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP002ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ + baseCoefficientError2540 ⟨2, by omega⟩) *
      edgeThirdCell2550 ⟨2, by omega⟩ ≤ boundaryCellP002Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨2, by omega⟩ ≤ ((852047900139394303430845906506174511 : ℝ) /
        (935361047891777867 * 10^40
        + 6503582929384211325797968275046400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP002NormUpper2549, edgeRightP002NormUpper2549,
      edgeFourthUpper2550, edgeFourthP002Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨2, by omega⟩‖ +
      baseCoefficientError2540 ⟨2, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP002Charge2551]

noncomputable def boundaryCellP003Charge2551 : ℝ := ((753 : ℝ) /
        125000)

theorem boundaryCellP003ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ + baseCoefficientError2540 ⟨3, by omega⟩) *
      edgeThirdCell2550 ⟨3, by omega⟩ ≤ boundaryCellP003Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨3, by omega⟩ ≤ (((2154 * 10^40
        + 8410585359055697323655654453908580028651) : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP003NormUpper2549, edgeRightP003NormUpper2549,
      edgeFourthUpper2550, edgeFourthP003Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨3, by omega⟩‖ +
      baseCoefficientError2540 ⟨3, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP003Charge2551]

noncomputable def boundaryCellP004Charge2551 : ℝ := ((2649 : ℝ) /
        1000000)

theorem boundaryCellP004ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ + baseCoefficientError2540 ⟨4, by omega⟩) *
      edgeThirdCell2550 ⟨4, by omega⟩ ≤ boundaryCellP004Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨4, by omega⟩ ≤ (((3625051 * 10^40
        + 8369394265609153458649771050270817889037) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP004NormUpper2549, edgeRightP004NormUpper2549,
      edgeFourthUpper2550, edgeFourthP004Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨4, by omega⟩‖ +
      baseCoefficientError2540 ⟨4, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP004Charge2551]

noncomputable def boundaryCellP005Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP005ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ + baseCoefficientError2540 ⟨5, by omega⟩) *
      edgeThirdCell2550 ⟨5, by omega⟩ ≤ boundaryCellP005Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨5, by omega⟩ ≤ ((1 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP005NormUpper2549, edgeRightP005NormUpper2549,
      edgeFourthUpper2550, edgeFourthP005Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨5, by omega⟩‖ +
      baseCoefficientError2540 ⟨5, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP005Charge2551]

noncomputable def boundaryCellP006Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP006ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ + baseCoefficientError2540 ⟨6, by omega⟩) *
      edgeThirdCell2550 ⟨6, by omega⟩ ≤ boundaryCellP006Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨6, by omega⟩ ≤ ((9165018958630623965445645124361 : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP006NormUpper2549, edgeRightP006NormUpper2549,
      edgeFourthUpper2550, edgeFourthP006Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨6, by omega⟩‖ +
      baseCoefficientError2540 ⟨6, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP006Charge2551]

noncomputable def boundaryCellP007Charge2551 : ℝ := ((23 : ℝ) /
        500000)

theorem boundaryCellP007ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ + baseCoefficientError2540 ⟨7, by omega⟩) *
      edgeThirdCell2550 ⟨7, by omega⟩ ≤ boundaryCellP007Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨7, by omega⟩ ≤ (((288 * 10^40
        + 8703792835999986678359205315598115852811) : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP007NormUpper2549, edgeRightP007NormUpper2549,
      edgeFourthUpper2550, edgeFourthP007Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨7, by omega⟩‖ +
      baseCoefficientError2540 ⟨7, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP007Charge2551]

noncomputable def boundaryCellP008Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP008ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ + baseCoefficientError2540 ⟨8, by omega⟩) *
      edgeThirdCell2550 ⟨8, by omega⟩ ≤ boundaryCellP008Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨8, by omega⟩ ≤ ((99174536462797026207317754732205720467 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP008NormUpper2549, edgeRightP008NormUpper2549,
      edgeFourthUpper2550, edgeFourthP008Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨8, by omega⟩‖ +
      baseCoefficientError2540 ⟨8, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP008Charge2551]

noncomputable def boundaryCellP009Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP009ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ + baseCoefficientError2540 ⟨9, by omega⟩) *
      edgeThirdCell2550 ⟨9, by omega⟩ ≤ boundaryCellP009Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨9, by omega⟩ ≤ ((49587313302850177538886698874582744231 : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP009NormUpper2549, edgeRightP009NormUpper2549,
      edgeFourthUpper2550, edgeFourthP009Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨9, by omega⟩‖ +
      baseCoefficientError2540 ⟨9, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP009Charge2551]

noncomputable def boundaryCellP010Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP010ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ + baseCoefficientError2540 ⟨10, by omega⟩) *
      edgeThirdCell2550 ⟨10, by omega⟩ ≤ boundaryCellP010Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨10, by omega⟩ ≤ ((99174678821924455067934025321866595401 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP010NormUpper2549, edgeRightP010NormUpper2549,
      edgeFourthUpper2550, edgeFourthP010Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨10, by omega⟩‖ +
      baseCoefficientError2540 ⟨10, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP010Charge2551]

noncomputable def boundaryCellP011Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP011ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ + baseCoefficientError2540 ⟨11, by omega⟩) *
      edgeThirdCell2550 ⟨11, by omega⟩ ≤ boundaryCellP011Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨11, by omega⟩ ≤ ((12396839204755474392705968366210242821 : ℝ) /
        (1870722095783555735 * 10^40
        + 3007165858768422651595936550092800000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP011NormUpper2549, edgeRightP011NormUpper2549,
      edgeFourthUpper2550, edgeFourthP011Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨11, by omega⟩‖ +
      baseCoefficientError2540 ⟨11, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP011Charge2551]

noncomputable def boundaryCellP012Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP012ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ + baseCoefficientError2540 ⟨12, by omega⟩) *
      edgeThirdCell2550 ⟨12, by omega⟩ ≤ boundaryCellP012Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨12, by omega⟩ ≤ ((3966989988007639585664236311280118719 : ℝ) /
        (598631070650737835 * 10^40
        + 2962293074805895248510699696029696000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP012NormUpper2549, edgeRightP012NormUpper2549,
      edgeFourthUpper2550, edgeFourthP012Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨12, by omega⟩‖ +
      baseCoefficientError2540 ⟨12, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP012Charge2551]

noncomputable def boundaryCellP013Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP013ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ + baseCoefficientError2540 ⟨13, by omega⟩) *
      edgeThirdCell2550 ⟨13, by omega⟩ ≤ boundaryCellP013Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨13, by omega⟩ ≤ ((99174782563893383880014699994412231037 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP013NormUpper2549, edgeRightP013NormUpper2549,
      edgeFourthUpper2550, edgeFourthP013Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨13, by omega⟩‖ +
      baseCoefficientError2540 ⟨13, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP013Charge2551]

noncomputable def boundaryCellP014Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP014ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ + baseCoefficientError2540 ⟨14, by omega⟩) *
      edgeThirdCell2550 ⟨14, by omega⟩ ≤ boundaryCellP014Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨14, by omega⟩ ≤ ((24793710864609193709208641670865320261 : ℝ) /
        (3741444191567111470 * 10^40
        + 6014331717536845303191873100185600000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP014NormUpper2549, edgeRightP014NormUpper2549,
      edgeFourthUpper2550, edgeFourthP014Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨14, by omega⟩‖ +
      baseCoefficientError2540 ⟨14, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP014Charge2551]

noncomputable def boundaryCellP015Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP015ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ + baseCoefficientError2540 ⟨15, by omega⟩) *
      edgeThirdCell2550 ⟨15, by omega⟩ ≤ boundaryCellP015Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨15, by omega⟩ ≤ ((247937217726152989123768817889942391 : ℝ) /
        (37414441915671114 * 10^40
        + 7060143317175368453031918731001856000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP015NormUpper2549, edgeRightP015NormUpper2549,
      edgeFourthUpper2550, edgeFourthP015Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨15, by omega⟩‖ +
      baseCoefficientError2540 ⟨15, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP015Charge2551]

noncomputable def boundaryCellP016Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP016ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ + baseCoefficientError2540 ⟨16, by omega⟩) *
      edgeThirdCell2550 ⟨16, by omega⟩ ≤ boundaryCellP016Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨16, by omega⟩ ≤ ((9917491862271794982618411794301142207 : ℝ) /
        (1496577676626844588 * 10^40
        + 2405732687014738121276749240074240000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP016NormUpper2549, edgeRightP016NormUpper2549,
      edgeFourthUpper2550, edgeFourthP016Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨16, by omega⟩‖ +
      baseCoefficientError2540 ⟨16, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP016Charge2551]

noncomputable def boundaryCellP017Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP017ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ + baseCoefficientError2540 ⟨17, by omega⟩) *
      edgeThirdCell2550 ⟨17, by omega⟩ ≤ boundaryCellP017Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨17, by omega⟩ ≤ ((99174979872814410630913195269053261019 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP017NormUpper2549, edgeRightP017NormUpper2549,
      edgeFourthUpper2550, edgeFourthP017Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨17, by omega⟩‖ +
      baseCoefficientError2540 ⟨17, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP017Charge2551]

noncomputable def boundaryCellP018Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP018ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ + baseCoefficientError2540 ⟨18, by omega⟩) *
      edgeThirdCell2550 ⟨18, by omega⟩ ≤ boundaryCellP018Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨18, by omega⟩ ≤ ((99175003030360239091699548433123033407 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP018NormUpper2549, edgeRightP018NormUpper2549,
      edgeFourthUpper2550, edgeFourthP018Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨18, by omega⟩‖ +
      baseCoefficientError2540 ⟨18, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP018Charge2551]

noncomputable def boundaryCellP019Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP019ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ + baseCoefficientError2540 ⟨19, by omega⟩) *
      edgeThirdCell2550 ⟨19, by omega⟩ ≤ boundaryCellP019Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨19, by omega⟩ ≤ ((99175044882563571234159069157227744211 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP019NormUpper2549, edgeRightP019NormUpper2549,
      edgeFourthUpper2550, edgeFourthP019Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨19, by omega⟩‖ +
      baseCoefficientError2540 ⟨19, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP019Charge2551]

noncomputable def boundaryCellP020Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP020ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ + baseCoefficientError2540 ⟨20, by omega⟩) *
      edgeThirdCell2550 ⟨20, by omega⟩ ≤ boundaryCellP020Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨20, by omega⟩ ≤ ((99175090393758692967836143409038369839 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP020NormUpper2549, edgeRightP020NormUpper2549,
      edgeFourthUpper2550, edgeFourthP020Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨20, by omega⟩‖ +
      baseCoefficientError2540 ⟨20, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP020Charge2551]

noncomputable def boundaryCellP021Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP021ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ + baseCoefficientError2540 ⟨21, by omega⟩) *
      edgeThirdCell2550 ⟨21, by omega⟩ ≤ boundaryCellP021Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨21, by omega⟩ ≤ ((99175128374812765754442466861166267039 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP021NormUpper2549, edgeRightP021NormUpper2549,
      edgeFourthUpper2550, edgeFourthP021Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨21, by omega⟩‖ +
      baseCoefficientError2540 ⟨21, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP021Charge2551]

noncomputable def boundaryCellP022Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP022ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ + baseCoefficientError2540 ⟨22, by omega⟩) *
      edgeThirdCell2550 ⟨22, by omega⟩ ≤ boundaryCellP022Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨22, by omega⟩ ≤ ((99175147814973419152916450136400278747 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP022NormUpper2549, edgeRightP022NormUpper2549,
      edgeFourthUpper2550, edgeFourthP022Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨22, by omega⟩‖ +
      baseCoefficientError2540 ⟨22, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP022Charge2551]

noncomputable def boundaryCellP023Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP023ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ + baseCoefficientError2540 ⟨23, by omega⟩) *
      edgeThirdCell2550 ⟨23, by omega⟩ ≤ boundaryCellP023Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨23, by omega⟩ ≤ ((99175203864756962762814882566868821981 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP023NormUpper2549, edgeRightP023NormUpper2549,
      edgeFourthUpper2550, edgeFourthP023Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨23, by omega⟩‖ +
      baseCoefficientError2540 ⟨23, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP023Charge2551]

noncomputable def boundaryCellP024Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP024ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ + baseCoefficientError2540 ⟨24, by omega⟩) *
      edgeThirdCell2550 ⟨24, by omega⟩ ≤ boundaryCellP024Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨24, by omega⟩ ≤ ((99175229623051444878153794625519579107 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP024NormUpper2549, edgeRightP024NormUpper2549,
      edgeFourthUpper2550, edgeFourthP024Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨24, by omega⟩‖ +
      baseCoefficientError2540 ⟨24, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP024Charge2551]

noncomputable def boundaryCellP025Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP025ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ + baseCoefficientError2540 ⟨25, by omega⟩) *
      edgeThirdCell2550 ⟨25, by omega⟩ ≤ boundaryCellP025Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨25, by omega⟩ ≤ ((99175261919292250596948521200458558937 : ℝ) /
        (14965776766268445882 * 10^40
        + 4057326870147381212767492400742400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP025NormUpper2549, edgeRightP025NormUpper2549,
      edgeFourthUpper2550, edgeFourthP025Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨25, by omega⟩‖ +
      baseCoefficientError2540 ⟨25, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP025Charge2551]

noncomputable def boundaryCellP026Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP026ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ + baseCoefficientError2540 ⟨26, by omega⟩) *
      edgeThirdCell2550 ⟨26, by omega⟩ ≤ boundaryCellP026Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨26, by omega⟩ ≤ ((6198455932800468074447644950782963529 : ℝ) /
        (935361047891777867 * 10^40
        + 6503582929384211325797968275046400000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP026NormUpper2549, edgeRightP026NormUpper2549,
      edgeFourthUpper2550, edgeFourthP026Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨26, by omega⟩‖ +
      baseCoefficientError2540 ⟨26, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP026Charge2551]

noncomputable def boundaryCellP027Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP027ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ + baseCoefficientError2540 ⟨27, by omega⟩) *
      edgeThirdCell2550 ⟨27, by omega⟩ ≤ boundaryCellP027Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨27, by omega⟩ ≤ ((49587671276476569022203792114907608787 : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP027NormUpper2549, edgeRightP027NormUpper2549,
      edgeFourthUpper2550, edgeFourthP027Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨27, by omega⟩‖ +
      baseCoefficientError2540 ⟨27, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP027Charge2551]

noncomputable def boundaryCellP028Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP028ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ + baseCoefficientError2540 ⟨28, by omega⟩) *
      edgeThirdCell2550 ⟨28, by omega⟩ ≤ boundaryCellP028Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨28, by omega⟩ ≤ ((19835072281924897667584022558789149491 : ℝ) /
        (2993155353253689176 * 10^40
        + 4811465374029476242553498480148480000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP028NormUpper2549, edgeRightP028NormUpper2549,
      edgeFourthUpper2550, edgeFourthP028Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨28, by omega⟩‖ +
      baseCoefficientError2540 ⟨28, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP028Charge2551]

noncomputable def boundaryCellP029Charge2551 : ℝ := ((1 : ℝ) /
        1000000)

theorem boundaryCellP029ChargeBound2551 :
    (‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ + baseCoefficientError2540 ⟨29, by omega⟩) *
      edgeThirdCell2550 ⟨29, by omega⟩ ≤ boundaryCellP029Charge2551 := by
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
  have ht : edgeThirdCell2550 ⟨29, by omega⟩ ≤ ((49587695058864638735997353482356204939 : ℝ) /
        (7482888383134222941 * 10^40
        + 2028663435073690606383746200371200000000)) := by
    unfold edgeThirdCell2550
    norm_num [edgeLeftNormUpper2549, edgeRightNormUpper2549,
      edgeLeftP029NormUpper2549, edgeRightP029NormUpper2549,
      edgeFourthUpper2550, edgeFourthP029Upper2550,
      edgeLeftPosition2548, edgeRightPosition2548]
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨29, by omega⟩‖ +
      baseCoefficientError2540 ⟨29, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [boundaryCellP029Charge2551]

noncomputable def boundaryCellCharge2551 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => boundaryCellP000Charge2551
  | 1 => boundaryCellP001Charge2551
  | 2 => boundaryCellP002Charge2551
  | 3 => boundaryCellP003Charge2551
  | 4 => boundaryCellP004Charge2551
  | 5 => boundaryCellP005Charge2551
  | 6 => boundaryCellP006Charge2551
  | 7 => boundaryCellP007Charge2551
  | 8 => boundaryCellP008Charge2551
  | 9 => boundaryCellP009Charge2551
  | 10 => boundaryCellP010Charge2551
  | 11 => boundaryCellP011Charge2551
  | 12 => boundaryCellP012Charge2551
  | 13 => boundaryCellP013Charge2551
  | 14 => boundaryCellP014Charge2551
  | 15 => boundaryCellP015Charge2551
  | 16 => boundaryCellP016Charge2551
  | 17 => boundaryCellP017Charge2551
  | 18 => boundaryCellP018Charge2551
  | 19 => boundaryCellP019Charge2551
  | 20 => boundaryCellP020Charge2551
  | 21 => boundaryCellP021Charge2551
  | 22 => boundaryCellP022Charge2551
  | 23 => boundaryCellP023Charge2551
  | 24 => boundaryCellP024Charge2551
  | 25 => boundaryCellP025Charge2551
  | 26 => boundaryCellP026Charge2551
  | 27 => boundaryCellP027Charge2551
  | 28 => boundaryCellP028Charge2551
  | 29 => boundaryCellP029Charge2551
  | _ => 0

theorem boundaryCellChargeBound2551 (i : Fin 30) :
    (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      edgeThirdCell2550 i ≤ boundaryCellCharge2551 i := by
  fin_cases i
  · exact boundaryCellP000ChargeBound2551
  · exact boundaryCellP001ChargeBound2551
  · exact boundaryCellP002ChargeBound2551
  · exact boundaryCellP003ChargeBound2551
  · exact boundaryCellP004ChargeBound2551
  · exact boundaryCellP005ChargeBound2551
  · exact boundaryCellP006ChargeBound2551
  · exact boundaryCellP007ChargeBound2551
  · exact boundaryCellP008ChargeBound2551
  · exact boundaryCellP009ChargeBound2551
  · exact boundaryCellP010ChargeBound2551
  · exact boundaryCellP011ChargeBound2551
  · exact boundaryCellP012ChargeBound2551
  · exact boundaryCellP013ChargeBound2551
  · exact boundaryCellP014ChargeBound2551
  · exact boundaryCellP015ChargeBound2551
  · exact boundaryCellP016ChargeBound2551
  · exact boundaryCellP017ChargeBound2551
  · exact boundaryCellP018ChargeBound2551
  · exact boundaryCellP019ChargeBound2551
  · exact boundaryCellP020ChargeBound2551
  · exact boundaryCellP021ChargeBound2551
  · exact boundaryCellP022ChargeBound2551
  · exact boundaryCellP023ChargeBound2551
  · exact boundaryCellP024ChargeBound2551
  · exact boundaryCellP025ChargeBound2551
  · exact boundaryCellP026ChargeBound2551
  · exact boundaryCellP027ChargeBound2551
  · exact boundaryCellP028ChargeBound2551
  · exact boundaryCellP029ChargeBound2551

noncomputable def boundaryCellThirdUpper2551 : ℝ := ((4373 : ℝ) /
        500000)

noncomputable def boundaryCellCurvatureUpper2551 : ℝ := ((91 : ℝ) /
        500000)

noncomputable def boundaryCellIntegralUpper2551 : ℝ := ((57 : ℝ) /
        500000000000)

theorem boundaryCellThirdBound2551 : edgeThirdAggregate2550 ≤ boundaryCellThirdUpper2551 := by
  have h : edgeThirdAggregate2550 ≤ ∑ i : Fin 30, boundaryCellCharge2551 i :=
    Finset.sum_le_sum (fun i _ => boundaryCellChargeBound2551 i)
  apply h.trans
  rw [sum30_chain2541]
  norm_num [boundaryCellCharge2551, boundaryCellThirdUpper2551, boundaryCellP000Charge2551,
      boundaryCellP001Charge2551,
      boundaryCellP002Charge2551, boundaryCellP003Charge2551, boundaryCellP004Charge2551,
          boundaryCellP005Charge2551,
      boundaryCellP006Charge2551, boundaryCellP007Charge2551, boundaryCellP008Charge2551,
          boundaryCellP009Charge2551,
      boundaryCellP010Charge2551, boundaryCellP011Charge2551, boundaryCellP012Charge2551,
          boundaryCellP013Charge2551,
      boundaryCellP014Charge2551, boundaryCellP015Charge2551, boundaryCellP016Charge2551,
          boundaryCellP017Charge2551,
      boundaryCellP018Charge2551, boundaryCellP019Charge2551, boundaryCellP020Charge2551,
          boundaryCellP021Charge2551,
      boundaryCellP022Charge2551, boundaryCellP023Charge2551, boundaryCellP024Charge2551,
          boundaryCellP025Charge2551,
      boundaryCellP026Charge2551, boundaryCellP027Charge2551, boundaryCellP028Charge2551,
          boundaryCellP029Charge2551]

theorem boundaryCellCurvatureBound2551 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 edgeLeftPosition2548 edgeRightPosition2548 ≤
        boundaryCellCurvatureUpper2551 := by
  have h := edgeCurvature_bound2550
  have ht := boundaryCellThirdBound2551
  norm_num [edgeSignedMidpointUpper2549, boundaryCellThirdUpper2551,
      boundaryCellCurvatureUpper2551,
    edgeLeftPosition2548, edgeRightPosition2548] at *
  linarith

theorem boundaryCellIntegralBound2551 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤ baseCoefficientError2540 i) :
    (∫ x in edgeLeftPosition2548..edgeRightPosition2548,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤
        boundaryCellIntegralUpper2551 := by
  have h := weightedPhysical2539_norm_integral_le_signed_cell (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541 hcoeff
    (a := edgeLeftPosition2548) (b := edgeRightPosition2548)
    (by norm_num [edgeLeftPosition2548, edgeRightPosition2548])
  have hl := adaptiveN02700PlusSigned_le2542
  have hr := adaptiveN02701PlusSigned_le2542
  have hc := boundaryCellCurvatureBound2551
  have hleft : adaptiveN02700PlusPosition2542 = edgeLeftPosition2548 := by
    norm_num [adaptiveN02700PlusPosition2542, edgeLeftPosition2548]
  have hright : adaptiveN02701PlusPosition2542 = edgeRightPosition2548 := by
    norm_num [adaptiveN02701PlusPosition2542, edgeRightPosition2548]
  rw [hleft] at hl
  rw [hright] at hr
  norm_num [edgeLeftPosition2548, edgeRightPosition2548, adaptiveN02700PlusUpper2542,
    adaptiveN02701PlusUpper2542, boundaryCellCurvatureUpper2551, boundaryCellIntegralUpper2551] at
        *
  linarith

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.boundaryCellChargeBound2551
#print axioms ConnesWeilRH.Dev.boundaryCellThirdBound2551
#print axioms ConnesWeilRH.Dev.boundaryCellCurvatureBound2551
#print axioms ConnesWeilRH.Dev.boundaryCellIntegralBound2551
