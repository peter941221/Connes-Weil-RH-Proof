import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteABatchN02703Plus2654
import ConnesWeilRH.Dev.C1RouteABatchN02704Plus2654

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC02703PlusFourthCell2654 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 batchN02703PlusPosition2654 batchN02704PlusPosition2654 < storedWidth i ^ 2
      then
    weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 batchN02703PlusPosition2654 batchN02704PlusPosition2654 / (storedWidth i ^
          2))
      (min (max |batchN02703PlusPosition2654| |batchN02704PlusPosition2654|) (storedWidth i ^ 2) /
        (storedWidth i ^ 2)) batchN02703PlusPosition2654 batchN02704PlusPosition2654
  else 0


def batchC02703PlusFourthP001Input2654 : RatPair2542 := ((((-((21 * 10^40
        + 2590665986622484827322845344600412856161) * 10^40
        + 1339369612967568308599015150185097693111)) : ℚ) /
        ((29 * 10^40
        + 7982574714943793053554229740921947830732) * 10^40
        + 284166734867110280795345651302400000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP001Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP001Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP001ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP001Frequency2654 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02703PlusFourthP001Upper2654 : ℝ := ((351072401719 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP001Exponent2654 : ℝ := (((-((21 * 10^40
        + 2590665986622484827322845344600412856161) * 10^40
        + 1339369612967568308599015150185097693111)) : ℝ) /
        (1163994432480249191615446209925476358713 * 10^40
        + 7969860026308074649534356818950400000000))

theorem batchC02703PlusFourthP001ExpBound2654 :
    Real.exp batchC02703PlusFourthP001Exponent2654 ≤ batchC02703PlusFourthP001ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP001Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP001Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP001Input2654 8).1 =
      batchC02703PlusFourthP001Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP001Input2654 8).2 : ℝ) =
      batchC02703PlusFourthP001Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP001Input2654 8).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP001Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP001Input2654 hz 8
  rw [hc, he] at h
  have ha : (2 : ℂ)^8 * embedPair2542 batchC02703PlusFourthP001Input2654 =
      (batchC02703PlusFourthP001Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP001Input2654,
        batchC02703PlusFourthP001Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP001Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP001Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP001Center2654))).trans
  norm_num [batchC02703PlusFourthP001Error2654, batchC02703PlusFourthP001ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP001Center2654]

theorem batchC02703PlusFourthP001Bound2654 : batchC02703PlusFourthCell2654 ⟨1, by omega⟩ ≤
    batchC02703PlusFourthP001Upper2654 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      batchC02703PlusFourthP001Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP001Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP001Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((95707621777613709907473135050948608 : ℝ) /
        104779244925114570282650713456640625) ((95747235859475304986077221613469696 : ℝ) /
        104779244925114570282650713456640625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP001ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP001Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((95707621777613709907473135050948608 : ℝ) /
        104779244925114570282650713456640625) ((95747235859475304986077221613469696 : ℝ) /
        104779244925114570282650713456640625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP001ExpUpper2654, batchC02703PlusFourthP001Frequency2654,
        batchC02703PlusFourthP001Upper2654]

def batchC02703PlusFourthP002Input2654 : RatPair2542 := ((((-((564 * 10^40
        + 6320295773356197331617375810041260089035) * 10^40
        + 1909897556892439653628817325904678324151)) : ℚ) /
        ((574 * 10^40
        + 6249826376838879765075486226973322645238) * 10^40
        + 963226378906970185681382605209600000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP002Center2654 : RatPair2542 := (((356685717808485830007 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP002Error2654 : ℝ := ((134104875955754021 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP002ExpUpper2654 : ℝ := ((784360188384118626858529946702885
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP002Frequency2654 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02703PlusFourthP002Upper2654 : ℝ := ((31281354476122908326285898909 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP002Exponent2654 : ℝ := (((-((564 * 10^40
        + 6320295773356197331617375810041260089035) * 10^40
        + 1909897556892439653628817325904678324151)) : ℝ) /
        ((8 * 10^40
        + 9785153537138107496329304472296458166331) * 10^40
        + 8452550412170421409151271603206400000000))

theorem batchC02703PlusFourthP002ExpBound2654 :
    Real.exp batchC02703PlusFourthP002Exponent2654 ≤ batchC02703PlusFourthP002ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP002Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP002Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP002Input2654 6).1 =
      batchC02703PlusFourthP002Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP002Input2654 6).2 : ℝ) =
      batchC02703PlusFourthP002Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP002Input2654 6).2 =
        ((134104875955754021 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP002Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP002Input2654 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02703PlusFourthP002Input2654 =
      (batchC02703PlusFourthP002Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP002Input2654,
        batchC02703PlusFourthP002Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP002Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP002Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP002Center2654))).trans
  norm_num [batchC02703PlusFourthP002Error2654, batchC02703PlusFourthP002ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP002Center2654]

theorem batchC02703PlusFourthP002Bound2654 : batchC02703PlusFourthCell2654 ⟨2, by omega⟩ ≤
    batchC02703PlusFourthP002Upper2654 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      batchC02703PlusFourthP002Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP002Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP002Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((382830487110454839629892540203794432 : ℝ) /
        535582378596426958724104076656640625) ((382988943437901219944308886453878784 : ℝ) /
        535582378596426958724104076656640625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP002ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP002Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((382830487110454839629892540203794432 : ℝ) /
        535582378596426958724104076656640625) ((382988943437901219944308886453878784 : ℝ) /
        535582378596426958724104076656640625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP002ExpUpper2654, batchC02703PlusFourthP002Frequency2654,
        batchC02703PlusFourthP002Upper2654]

def batchC02703PlusFourthP003Input2654 : RatPair2542 := ((((-((75251 * 10^40
        + 1057389726409136056781964181355512754308) * 10^40
        + 182014849813444389447983162613849155677)) : ℚ) /
        ((103951 * 10^40
        + 7342811202324181443180901668794111589450) * 10^40
        + 5111809480188745198977982311219200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP003Center2654 : RatPair2542 := (((11065998679404049300331925531 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP003Error2654 : ℝ := ((803023130034719983008463 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02703PlusFourthP003ExpUpper2654 : ℝ :=
    ((6083597110479307108929984703565094582991 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02703PlusFourthP003Frequency2654 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02703PlusFourthP003Upper2654 : ℝ := ((46047072442478261003870299939507717
    : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02703PlusFourthP003Exponent2654 : ℝ := (((-((75251 * 10^40
        + 1057389726409136056781964181355512754308) * 10^40
        + 182014849813444389447983162613849155677)) : ℝ) /
        ((1624 * 10^40
        + 2458481425036315335049701588574907993585) * 10^40
        + 1642372023127949143734030973612800000000))

theorem batchC02703PlusFourthP003ExpBound2654 :
    Real.exp batchC02703PlusFourthP003Exponent2654 ≤ batchC02703PlusFourthP003ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP003Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP003Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP003Input2654 6).1 =
      batchC02703PlusFourthP003Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP003Input2654 6).2 : ℝ) =
      batchC02703PlusFourthP003Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP003Input2654 6).2 =
        ((803023130034719983008463 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP003Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP003Input2654 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02703PlusFourthP003Input2654 =
      (batchC02703PlusFourthP003Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP003Input2654,
        batchC02703PlusFourthP003Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP003Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP003Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP003Center2654))).trans
  norm_num [batchC02703PlusFourthP003Error2654, batchC02703PlusFourthP003ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP003Center2654]

theorem batchC02703PlusFourthP003Bound2654 : batchC02703PlusFourthCell2654 ⟨3, by omega⟩ ≤
    batchC02703PlusFourthP003Upper2654 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      batchC02703PlusFourthP003Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP003Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP003Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP003ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP003Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP003ExpUpper2654, batchC02703PlusFourthP003Frequency2654,
        batchC02703PlusFourthP003Upper2654]

def batchC02703PlusFourthP004Input2654 : RatPair2542 := ((((-((1314 * 10^40
        + 3793291039928624094795639072353193421464) * 10^40
        + 9080182155977962095085629655006240824151)) : ℚ) /
        ((2095 * 10^40
        + 6882578114756578562996035324885650009660) * 10^40
        + 3829744574362800185681382605209600000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP004Center2654 : RatPair2542 := (((5399498464704499731115098979005 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP004Error2654 : ℝ := ((711402176420183029093185407 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP004ExpUpper2654 : ℝ := (((593 * 10^40
        + 6811346101258093592293214200172292028287) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP004Frequency2654 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02703PlusFourthP004Upper2654 : ℝ :=
    ((1576656906165466790577005683625779711 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC02703PlusFourthP004Exponent2654 : ℝ := (((-((1314 * 10^40
        + 3793291039928624094795639072353193421464) * 10^40
        + 9080182155977962095085629655006240824151)) : ℝ) /
        ((32 * 10^40
        + 7451290283043071540046813051951338281400) * 10^40
        + 9434839758974418752901271603206400000000))

theorem batchC02703PlusFourthP004ExpBound2654 :
    Real.exp batchC02703PlusFourthP004Exponent2654 ≤ batchC02703PlusFourthP004ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP004Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP004Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP004Input2654 6).1 =
      batchC02703PlusFourthP004Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP004Input2654 6).2 : ℝ) =
      batchC02703PlusFourthP004Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP004Input2654 6).2 =
        ((711402176420183029093185407 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP004Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP004Input2654 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02703PlusFourthP004Input2654 =
      (batchC02703PlusFourthP004Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP004Input2654,
        batchC02703PlusFourthP004Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP004Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP004Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP004Center2654))).trans
  norm_num [batchC02703PlusFourthP004Error2654, batchC02703PlusFourthP004ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP004Center2654]

theorem batchC02703PlusFourthP004Bound2654 : batchC02703PlusFourthCell2654 ⟨4, by omega⟩ ≤
    batchC02703PlusFourthP004Upper2654 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      batchC02703PlusFourthP004Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP004Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP004Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((382830487110454839629892540203794432 : ℝ) /
        811296384146067132209863967375390625) ((382988943437901219944308886453878784 : ℝ) /
        811296384146067132209863967375390625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP004ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP004Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((382830487110454839629892540203794432 : ℝ) /
        811296384146067132209863967375390625) ((382988943437901219944308886453878784 : ℝ) /
        811296384146067132209863967375390625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP004ExpUpper2654, batchC02703PlusFourthP004Frequency2654,
        batchC02703PlusFourthP004Upper2654]

def batchC02703PlusFourthP006Input2654 : RatPair2542 := ((((-10703175194025607899013599449683) :
    ℚ) /
        17997946250671801739673600000000),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP006Center2654 : RatPair2542 := (((638567541572489 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP006Error2654 : ℝ := ((2524797428367 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP006ExpUpper2654 : ℝ := ((1404224874158574386977137295 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP006Frequency2654 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02703PlusFourthP006Upper2654 : ℝ := ((19071347246377579564231 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02703PlusFourthP006Exponent2654 : ℝ :=
    (((-10703175194025607899013599449683) : ℝ) /
        140608955083373451091200000000)

theorem batchC02703PlusFourthP006ExpBound2654 :
    Real.exp batchC02703PlusFourthP006Exponent2654 ≤ batchC02703PlusFourthP006ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP006Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP006Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP006Input2654 7).1 =
      batchC02703PlusFourthP006Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP006Input2654 7).2 : ℝ) =
      batchC02703PlusFourthP006Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP006Input2654 7).2 =
        ((2524797428367 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP006Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP006Input2654 hz 7
  rw [hc, he] at h
  have ha : (2 : ℂ)^7 * embedPair2542 batchC02703PlusFourthP006Input2654 =
      (batchC02703PlusFourthP006Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP006Input2654,
        batchC02703PlusFourthP006Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP006Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP006Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP006Center2654))).trans
  norm_num [batchC02703PlusFourthP006Error2654, batchC02703PlusFourthP006ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP006Center2654]

theorem batchC02703PlusFourthP006Bound2654 : batchC02703PlusFourthCell2654 ⟨6, by omega⟩ ≤
    batchC02703PlusFourthP006Upper2654 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      batchC02703PlusFourthP006Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP006Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP006Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) ((9895936151 : ℝ) /
        12800000000) ((158400514417 : ℝ) /
        204800000000) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP006ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP006Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) ((9895936151 : ℝ) /
        12800000000) ((158400514417 : ℝ) /
        204800000000) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP006ExpUpper2654, batchC02703PlusFourthP006Frequency2654,
        batchC02703PlusFourthP006Upper2654]

def batchC02703PlusFourthP007Input2654 : RatPair2542 := ((((-((75251 * 10^40
        + 1057389726409136056781964181355512754308) * 10^40
        + 182014849813444389447983162613849155677)) : ℚ) /
        ((103951 * 10^40
        + 7342811202324181443180901668794111589450) * 10^40
        + 5111809480188745198977982311219200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP007Center2654 : RatPair2542 := (((11065998679404049300331925531 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP007Error2654 : ℝ := ((803023130034719983008463 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02703PlusFourthP007ExpUpper2654 : ℝ :=
    ((6083597110479307108929984703565094582991 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02703PlusFourthP007Frequency2654 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02703PlusFourthP007Upper2654 : ℝ := ((74752337942073155155996149108873 :
    ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC02703PlusFourthP007Exponent2654 : ℝ := (((-((75251 * 10^40
        + 1057389726409136056781964181355512754308) * 10^40
        + 182014849813444389447983162613849155677)) : ℝ) /
        ((1624 * 10^40
        + 2458481425036315335049701588574907993585) * 10^40
        + 1642372023127949143734030973612800000000))

theorem batchC02703PlusFourthP007ExpBound2654 :
    Real.exp batchC02703PlusFourthP007Exponent2654 ≤ batchC02703PlusFourthP007ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP007Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP007Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP007Input2654 6).1 =
      batchC02703PlusFourthP007Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP007Input2654 6).2 : ℝ) =
      batchC02703PlusFourthP007Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP007Input2654 6).2 =
        ((803023130034719983008463 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP007Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP007Input2654 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02703PlusFourthP007Input2654 =
      (batchC02703PlusFourthP007Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP007Input2654,
        batchC02703PlusFourthP007Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP007Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP007Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP007Center2654))).trans
  norm_num [batchC02703PlusFourthP007Error2654, batchC02703PlusFourthP007ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP007Center2654]

theorem batchC02703PlusFourthP007Bound2654 : batchC02703PlusFourthCell2654 ⟨7, by omega⟩ ≤
    batchC02703PlusFourthP007Upper2654 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      batchC02703PlusFourthP007Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP007Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP007Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP007ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP007Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) ((6127823095006419519108942183262060544 : ℝ) /
        10660941547919407797287895527587890625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP007ExpUpper2654, batchC02703PlusFourthP007Frequency2654,
        batchC02703PlusFourthP007Upper2654]

def batchC02703PlusFourthP008Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP008Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP008Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP008ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP008Frequency2654 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def batchC02703PlusFourthP008Upper2654 : ℝ := ((23073923062811818183098067 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP008Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP008ExpBound2654 :
    Real.exp batchC02703PlusFourthP008Exponent2654 ≤ batchC02703PlusFourthP008ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP008Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP008Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP008Input2654 14).1 =
      batchC02703PlusFourthP008Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP008Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP008Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP008Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP008Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP008Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP008Input2654 =
      (batchC02703PlusFourthP008Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP008Input2654,
        batchC02703PlusFourthP008Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP008Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP008Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP008Center2654))).trans
  norm_num [batchC02703PlusFourthP008Error2654, batchC02703PlusFourthP008ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP008Center2654]

theorem batchC02703PlusFourthP008Bound2654 : batchC02703PlusFourthCell2654 ⟨8, by omega⟩ ≤
    batchC02703PlusFourthP008Upper2654 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      batchC02703PlusFourthP008Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP008Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP008Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP008ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP008Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP008ExpUpper2654, batchC02703PlusFourthP008Frequency2654,
        batchC02703PlusFourthP008Upper2654]

def batchC02703PlusFourthP009Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP009Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP009Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP009ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP009Frequency2654 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def batchC02703PlusFourthP009Upper2654 : ℝ := ((23074258730486614568225089 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP009Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP009ExpBound2654 :
    Real.exp batchC02703PlusFourthP009Exponent2654 ≤ batchC02703PlusFourthP009ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP009Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP009Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP009Input2654 14).1 =
      batchC02703PlusFourthP009Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP009Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP009Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP009Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP009Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP009Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP009Input2654 =
      (batchC02703PlusFourthP009Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP009Input2654,
        batchC02703PlusFourthP009Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP009Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP009Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP009Center2654))).trans
  norm_num [batchC02703PlusFourthP009Error2654, batchC02703PlusFourthP009ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP009Center2654]

theorem batchC02703PlusFourthP009Bound2654 : batchC02703PlusFourthCell2654 ⟨9, by omega⟩ ≤
    batchC02703PlusFourthP009Upper2654 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      batchC02703PlusFourthP009Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP009Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP009Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP009ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP009Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP009ExpUpper2654, batchC02703PlusFourthP009Frequency2654,
        batchC02703PlusFourthP009Upper2654]

def batchC02703PlusFourthP010Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP010Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP010Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP010ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP010Frequency2654 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def batchC02703PlusFourthP010Upper2654 : ℝ := ((5768613292775253273631599 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02703PlusFourthP010Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP010ExpBound2654 :
    Real.exp batchC02703PlusFourthP010Exponent2654 ≤ batchC02703PlusFourthP010ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP010Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP010Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP010Input2654 14).1 =
      batchC02703PlusFourthP010Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP010Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP010Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP010Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP010Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP010Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP010Input2654 =
      (batchC02703PlusFourthP010Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP010Input2654,
        batchC02703PlusFourthP010Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP010Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP010Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP010Center2654))).trans
  norm_num [batchC02703PlusFourthP010Error2654, batchC02703PlusFourthP010ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP010Center2654]

theorem batchC02703PlusFourthP010Bound2654 : batchC02703PlusFourthCell2654 ⟨10, by omega⟩ ≤
    batchC02703PlusFourthP010Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      batchC02703PlusFourthP010Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP010Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP010Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP010ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP010Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP010ExpUpper2654, batchC02703PlusFourthP010Frequency2654,
        batchC02703PlusFourthP010Upper2654]

def batchC02703PlusFourthP011Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP011Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP011Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP011ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP011Frequency2654 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def batchC02703PlusFourthP011Upper2654 : ℝ := ((11537291409285838155200985 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02703PlusFourthP011Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP011ExpBound2654 :
    Real.exp batchC02703PlusFourthP011Exponent2654 ≤ batchC02703PlusFourthP011ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP011Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP011Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP011Input2654 14).1 =
      batchC02703PlusFourthP011Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP011Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP011Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP011Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP011Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP011Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP011Input2654 =
      (batchC02703PlusFourthP011Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP011Input2654,
        batchC02703PlusFourthP011Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP011Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP011Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP011Center2654))).trans
  norm_num [batchC02703PlusFourthP011Error2654, batchC02703PlusFourthP011ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP011Center2654]

theorem batchC02703PlusFourthP011Bound2654 : batchC02703PlusFourthCell2654 ⟨11, by omega⟩ ≤
    batchC02703PlusFourthP011Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      batchC02703PlusFourthP011Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP011Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP011Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP011ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP011Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP011ExpUpper2654, batchC02703PlusFourthP011Frequency2654,
        batchC02703PlusFourthP011Upper2654]

def batchC02703PlusFourthP012Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP012Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP012Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP012ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP012Frequency2654 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def batchC02703PlusFourthP012Upper2654 : ℝ := ((23074717106517523729634123 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP012Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP012ExpBound2654 :
    Real.exp batchC02703PlusFourthP012Exponent2654 ≤ batchC02703PlusFourthP012ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP012Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP012Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP012Input2654 14).1 =
      batchC02703PlusFourthP012Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP012Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP012Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP012Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP012Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP012Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP012Input2654 =
      (batchC02703PlusFourthP012Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP012Input2654,
        batchC02703PlusFourthP012Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP012Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP012Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP012Center2654))).trans
  norm_num [batchC02703PlusFourthP012Error2654, batchC02703PlusFourthP012ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP012Center2654]

theorem batchC02703PlusFourthP012Bound2654 : batchC02703PlusFourthCell2654 ⟨12, by omega⟩ ≤
    batchC02703PlusFourthP012Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      batchC02703PlusFourthP012Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP012Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP012Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP012ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP012Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP012ExpUpper2654, batchC02703PlusFourthP012Frequency2654,
        batchC02703PlusFourthP012Upper2654]

def batchC02703PlusFourthP013Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP013Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP013Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP013ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP013Frequency2654 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def batchC02703PlusFourthP013Upper2654 : ℝ := ((23074839484602301766622563 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP013Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP013ExpBound2654 :
    Real.exp batchC02703PlusFourthP013Exponent2654 ≤ batchC02703PlusFourthP013ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP013Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP013Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP013Input2654 14).1 =
      batchC02703PlusFourthP013Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP013Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP013Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP013Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP013Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP013Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP013Input2654 =
      (batchC02703PlusFourthP013Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP013Input2654,
        batchC02703PlusFourthP013Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP013Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP013Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP013Center2654))).trans
  norm_num [batchC02703PlusFourthP013Error2654, batchC02703PlusFourthP013ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP013Center2654]

theorem batchC02703PlusFourthP013Bound2654 : batchC02703PlusFourthCell2654 ⟨13, by omega⟩ ≤
    batchC02703PlusFourthP013Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      batchC02703PlusFourthP013Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP013Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP013Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP013ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP013Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP013ExpUpper2654, batchC02703PlusFourthP013Frequency2654,
        batchC02703PlusFourthP013Upper2654]

def batchC02703PlusFourthP014Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP014Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP014Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP014ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP014Frequency2654 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def batchC02703PlusFourthP014Upper2654 : ℝ := ((23075066245346212233414543 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP014Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP014ExpBound2654 :
    Real.exp batchC02703PlusFourthP014Exponent2654 ≤ batchC02703PlusFourthP014ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP014Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP014Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP014Input2654 14).1 =
      batchC02703PlusFourthP014Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP014Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP014Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP014Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP014Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP014Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP014Input2654 =
      (batchC02703PlusFourthP014Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP014Input2654,
        batchC02703PlusFourthP014Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP014Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP014Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP014Center2654))).trans
  norm_num [batchC02703PlusFourthP014Error2654, batchC02703PlusFourthP014ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP014Center2654]

theorem batchC02703PlusFourthP014Bound2654 : batchC02703PlusFourthCell2654 ⟨14, by omega⟩ ≤
    batchC02703PlusFourthP014Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      batchC02703PlusFourthP014Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP014Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP014Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP014ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP014Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP014ExpUpper2654, batchC02703PlusFourthP014Frequency2654,
        batchC02703PlusFourthP014Upper2654]

def batchC02703PlusFourthP015Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP015Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP015Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP015ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP015Frequency2654 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def batchC02703PlusFourthP015Upper2654 : ℝ := ((23075228724428605552759153 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP015Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP015ExpBound2654 :
    Real.exp batchC02703PlusFourthP015Exponent2654 ≤ batchC02703PlusFourthP015ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP015Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP015Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP015Input2654 14).1 =
      batchC02703PlusFourthP015Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP015Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP015Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP015Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP015Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP015Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP015Input2654 =
      (batchC02703PlusFourthP015Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP015Input2654,
        batchC02703PlusFourthP015Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP015Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP015Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP015Center2654))).trans
  norm_num [batchC02703PlusFourthP015Error2654, batchC02703PlusFourthP015ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP015Center2654]

theorem batchC02703PlusFourthP015Bound2654 : batchC02703PlusFourthCell2654 ⟨15, by omega⟩ ≤
    batchC02703PlusFourthP015Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      batchC02703PlusFourthP015Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP015Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP015Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP015ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP015Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP015ExpUpper2654, batchC02703PlusFourthP015Frequency2654,
        batchC02703PlusFourthP015Upper2654]

def batchC02703PlusFourthP016Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP016Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP016Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP016ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP016Frequency2654 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def batchC02703PlusFourthP016Upper2654 : ℝ := ((721104567072041405836987 : ℝ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968))

noncomputable def batchC02703PlusFourthP016Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP016ExpBound2654 :
    Real.exp batchC02703PlusFourthP016Exponent2654 ≤ batchC02703PlusFourthP016ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP016Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP016Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP016Input2654 14).1 =
      batchC02703PlusFourthP016Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP016Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP016Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP016Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP016Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP016Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP016Input2654 =
      (batchC02703PlusFourthP016Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP016Input2654,
        batchC02703PlusFourthP016Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP016Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP016Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP016Center2654))).trans
  norm_num [batchC02703PlusFourthP016Error2654, batchC02703PlusFourthP016ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP016Center2654]

theorem batchC02703PlusFourthP016Bound2654 : batchC02703PlusFourthCell2654 ⟨16, by omega⟩ ≤
    batchC02703PlusFourthP016Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      batchC02703PlusFourthP016Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP016Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP016Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP016ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP016Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP016ExpUpper2654, batchC02703PlusFourthP016Frequency2654,
        batchC02703PlusFourthP016Upper2654]

def batchC02703PlusFourthP017Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP017Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP017Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP017ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP017Frequency2654 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def batchC02703PlusFourthP017Upper2654 : ℝ := ((23075574234625764344423857 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP017Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP017ExpBound2654 :
    Real.exp batchC02703PlusFourthP017Exponent2654 ≤ batchC02703PlusFourthP017ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP017Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP017Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP017Input2654 14).1 =
      batchC02703PlusFourthP017Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP017Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP017Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP017Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP017Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP017Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP017Input2654 =
      (batchC02703PlusFourthP017Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP017Input2654,
        batchC02703PlusFourthP017Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP017Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP017Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP017Center2654))).trans
  norm_num [batchC02703PlusFourthP017Error2654, batchC02703PlusFourthP017ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP017Center2654]

theorem batchC02703PlusFourthP017Bound2654 : batchC02703PlusFourthCell2654 ⟨17, by omega⟩ ≤
    batchC02703PlusFourthP017Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      batchC02703PlusFourthP017Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP017Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP017Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP017ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP017Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP017ExpUpper2654, batchC02703PlusFourthP017Frequency2654,
        batchC02703PlusFourthP017Upper2654]

def batchC02703PlusFourthP018Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP018Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP018Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP018ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP018Frequency2654 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def batchC02703PlusFourthP018Upper2654 : ℝ := ((5768915117770488676986747 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02703PlusFourthP018Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP018ExpBound2654 :
    Real.exp batchC02703PlusFourthP018Exponent2654 ≤ batchC02703PlusFourthP018ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP018Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP018Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP018Input2654 14).1 =
      batchC02703PlusFourthP018Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP018Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP018Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP018Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP018Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP018Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP018Input2654 =
      (batchC02703PlusFourthP018Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP018Input2654,
        batchC02703PlusFourthP018Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP018Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP018Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP018Center2654))).trans
  norm_num [batchC02703PlusFourthP018Error2654, batchC02703PlusFourthP018ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP018Center2654]

theorem batchC02703PlusFourthP018Bound2654 : batchC02703PlusFourthCell2654 ⟨18, by omega⟩ ≤
    batchC02703PlusFourthP018Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      batchC02703PlusFourthP018Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP018Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP018Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP018ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP018Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP018ExpUpper2654, batchC02703PlusFourthP018Frequency2654,
        batchC02703PlusFourthP018Upper2654]

def batchC02703PlusFourthP019Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP019Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP019Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP019ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP019Frequency2654 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def batchC02703PlusFourthP019Upper2654 : ℝ := ((23075816325210868548943065 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP019Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP019ExpBound2654 :
    Real.exp batchC02703PlusFourthP019Exponent2654 ≤ batchC02703PlusFourthP019ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP019Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP019Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP019Input2654 14).1 =
      batchC02703PlusFourthP019Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP019Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP019Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP019Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP019Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP019Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP019Input2654 =
      (batchC02703PlusFourthP019Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP019Input2654,
        batchC02703PlusFourthP019Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP019Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP019Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP019Center2654))).trans
  norm_num [batchC02703PlusFourthP019Error2654, batchC02703PlusFourthP019ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP019Center2654]

theorem batchC02703PlusFourthP019Bound2654 : batchC02703PlusFourthCell2654 ⟨19, by omega⟩ ≤
    batchC02703PlusFourthP019Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      batchC02703PlusFourthP019Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP019Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP019Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP019ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP019Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP019ExpUpper2654, batchC02703PlusFourthP019Frequency2654,
        batchC02703PlusFourthP019Upper2654]

def batchC02703PlusFourthP020Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP020Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP020Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP020ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP020Frequency2654 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def batchC02703PlusFourthP020Upper2654 : ℝ := ((23075985805969008877385803 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP020Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP020ExpBound2654 :
    Real.exp batchC02703PlusFourthP020Exponent2654 ≤ batchC02703PlusFourthP020ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP020Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP020Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP020Input2654 14).1 =
      batchC02703PlusFourthP020Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP020Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP020Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP020Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP020Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP020Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP020Input2654 =
      (batchC02703PlusFourthP020Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP020Input2654,
        batchC02703PlusFourthP020Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP020Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP020Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP020Center2654))).trans
  norm_num [batchC02703PlusFourthP020Error2654, batchC02703PlusFourthP020ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP020Center2654]

theorem batchC02703PlusFourthP020Bound2654 : batchC02703PlusFourthCell2654 ⟨20, by omega⟩ ≤
    batchC02703PlusFourthP020Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      batchC02703PlusFourthP020Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP020Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP020Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP020ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP020Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP020ExpUpper2654, batchC02703PlusFourthP020Frequency2654,
        batchC02703PlusFourthP020Upper2654]

def batchC02703PlusFourthP021Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP021Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP021Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP021ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP021Frequency2654 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def batchC02703PlusFourthP021Upper2654 : ℝ := ((11538063622821597001972511 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02703PlusFourthP021Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP021ExpBound2654 :
    Real.exp batchC02703PlusFourthP021Exponent2654 ≤ batchC02703PlusFourthP021ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP021Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP021Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP021Input2654 14).1 =
      batchC02703PlusFourthP021Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP021Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP021Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP021Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP021Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP021Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP021Input2654 =
      (batchC02703PlusFourthP021Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP021Input2654,
        batchC02703PlusFourthP021Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP021Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP021Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP021Center2654))).trans
  norm_num [batchC02703PlusFourthP021Error2654, batchC02703PlusFourthP021ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP021Center2654]

theorem batchC02703PlusFourthP021Bound2654 : batchC02703PlusFourthCell2654 ⟨21, by omega⟩ ≤
    batchC02703PlusFourthP021Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      batchC02703PlusFourthP021Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP021Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP021Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP021ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP021Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP021ExpUpper2654, batchC02703PlusFourthP021Frequency2654,
        batchC02703PlusFourthP021Upper2654]

def batchC02703PlusFourthP022Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP022Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP022Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP022ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP022Frequency2654 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def batchC02703PlusFourthP022Upper2654 : ℝ := ((11538099820066453750725863 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02703PlusFourthP022Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP022ExpBound2654 :
    Real.exp batchC02703PlusFourthP022Exponent2654 ≤ batchC02703PlusFourthP022ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP022Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP022Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP022Input2654 14).1 =
      batchC02703PlusFourthP022Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP022Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP022Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP022Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP022Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP022Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP022Input2654 =
      (batchC02703PlusFourthP022Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP022Input2654,
        batchC02703PlusFourthP022Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP022Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP022Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP022Center2654))).trans
  norm_num [batchC02703PlusFourthP022Error2654, batchC02703PlusFourthP022ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP022Center2654]

theorem batchC02703PlusFourthP022Bound2654 : batchC02703PlusFourthCell2654 ⟨22, by omega⟩ ≤
    batchC02703PlusFourthP022Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      batchC02703PlusFourthP022Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP022Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP022Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP022ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP022Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP022ExpUpper2654, batchC02703PlusFourthP022Frequency2654,
        batchC02703PlusFourthP022Upper2654]

def batchC02703PlusFourthP023Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP023Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP023Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP023ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP023Frequency2654 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def batchC02703PlusFourthP023Upper2654 : ℝ := ((1442275523031334860523205 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC02703PlusFourthP023Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP023ExpBound2654 :
    Real.exp batchC02703PlusFourthP023Exponent2654 ≤ batchC02703PlusFourthP023ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP023Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP023Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP023Input2654 14).1 =
      batchC02703PlusFourthP023Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP023Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP023Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP023Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP023Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP023Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP023Input2654 =
      (batchC02703PlusFourthP023Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP023Input2654,
        batchC02703PlusFourthP023Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP023Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP023Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP023Center2654))).trans
  norm_num [batchC02703PlusFourthP023Error2654, batchC02703PlusFourthP023ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP023Center2654]

theorem batchC02703PlusFourthP023Bound2654 : batchC02703PlusFourthCell2654 ⟨23, by omega⟩ ≤
    batchC02703PlusFourthP023Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      batchC02703PlusFourthP023Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP023Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP023Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP023ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP023Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP023ExpUpper2654, batchC02703PlusFourthP023Frequency2654,
        batchC02703PlusFourthP023Upper2654]

def batchC02703PlusFourthP024Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP024Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP024Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP024ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP024Frequency2654 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def batchC02703PlusFourthP024Upper2654 : ℝ := ((23076504292368023089133603 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP024Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP024ExpBound2654 :
    Real.exp batchC02703PlusFourthP024Exponent2654 ≤ batchC02703PlusFourthP024ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP024Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP024Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP024Input2654 14).1 =
      batchC02703PlusFourthP024Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP024Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP024Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP024Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP024Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP024Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP024Input2654 =
      (batchC02703PlusFourthP024Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP024Input2654,
        batchC02703PlusFourthP024Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP024Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP024Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP024Center2654))).trans
  norm_num [batchC02703PlusFourthP024Error2654, batchC02703PlusFourthP024ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP024Center2654]

theorem batchC02703PlusFourthP024Bound2654 : batchC02703PlusFourthCell2654 ⟨24, by omega⟩ ≤
    batchC02703PlusFourthP024Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      batchC02703PlusFourthP024Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP024Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP024Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP024ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP024Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP024ExpUpper2654, batchC02703PlusFourthP024Frequency2654,
        batchC02703PlusFourthP024Upper2654]

def batchC02703PlusFourthP025Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP025Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP025Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP025ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP025Frequency2654 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def batchC02703PlusFourthP025Upper2654 : ℝ := ((1442289035246310523519227 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC02703PlusFourthP025Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP025ExpBound2654 :
    Real.exp batchC02703PlusFourthP025Exponent2654 ≤ batchC02703PlusFourthP025ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP025Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP025Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP025Input2654 14).1 =
      batchC02703PlusFourthP025Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP025Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP025Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP025Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP025Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP025Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP025Input2654 =
      (batchC02703PlusFourthP025Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP025Input2654,
        batchC02703PlusFourthP025Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP025Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP025Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP025Center2654))).trans
  norm_num [batchC02703PlusFourthP025Error2654, batchC02703PlusFourthP025ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP025Center2654]

theorem batchC02703PlusFourthP025Bound2654 : batchC02703PlusFourthCell2654 ⟨25, by omega⟩ ≤
    batchC02703PlusFourthP025Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      batchC02703PlusFourthP025Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP025Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP025Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP025ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP025Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP025ExpUpper2654, batchC02703PlusFourthP025Frequency2654,
        batchC02703PlusFourthP025Upper2654]

def batchC02703PlusFourthP026Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP026Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP026Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP026ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP026Frequency2654 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def batchC02703PlusFourthP026Upper2654 : ℝ := ((23076747477319604714256117 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP026Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP026ExpBound2654 :
    Real.exp batchC02703PlusFourthP026Exponent2654 ≤ batchC02703PlusFourthP026ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP026Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP026Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP026Input2654 14).1 =
      batchC02703PlusFourthP026Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP026Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP026Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP026Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP026Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP026Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP026Input2654 =
      (batchC02703PlusFourthP026Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP026Input2654,
        batchC02703PlusFourthP026Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP026Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP026Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP026Center2654))).trans
  norm_num [batchC02703PlusFourthP026Error2654, batchC02703PlusFourthP026ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP026Center2654]

theorem batchC02703PlusFourthP026Bound2654 : batchC02703PlusFourthCell2654 ⟨26, by omega⟩ ≤
    batchC02703PlusFourthP026Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      batchC02703PlusFourthP026Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP026Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP026Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP026ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP026Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP026ExpUpper2654, batchC02703PlusFourthP026Frequency2654,
        batchC02703PlusFourthP026Upper2654]

def batchC02703PlusFourthP027Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP027Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP027Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP027ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP027Frequency2654 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def batchC02703PlusFourthP027Upper2654 : ℝ := ((23076924846564797241895801 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP027Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP027ExpBound2654 :
    Real.exp batchC02703PlusFourthP027Exponent2654 ≤ batchC02703PlusFourthP027ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP027Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP027Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP027Input2654 14).1 =
      batchC02703PlusFourthP027Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP027Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP027Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP027Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP027Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP027Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP027Input2654 =
      (batchC02703PlusFourthP027Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP027Input2654,
        batchC02703PlusFourthP027Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP027Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP027Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP027Center2654))).trans
  norm_num [batchC02703PlusFourthP027Error2654, batchC02703PlusFourthP027ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP027Center2654]

theorem batchC02703PlusFourthP027Bound2654 : batchC02703PlusFourthCell2654 ⟨27, by omega⟩ ≤
    batchC02703PlusFourthP027Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      batchC02703PlusFourthP027Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP027Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP027Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP027ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP027Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP027ExpUpper2654, batchC02703PlusFourthP027Frequency2654,
        batchC02703PlusFourthP027Upper2654]

def batchC02703PlusFourthP028Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP028Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP028Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP028ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP028Frequency2654 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def batchC02703PlusFourthP028Upper2654 : ℝ := ((5769248767470055402733371 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02703PlusFourthP028Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP028ExpBound2654 :
    Real.exp batchC02703PlusFourthP028Exponent2654 ≤ batchC02703PlusFourthP028ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP028Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP028Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP028Input2654 14).1 =
      batchC02703PlusFourthP028Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP028Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP028Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP028Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP028Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP028Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP028Input2654 =
      (batchC02703PlusFourthP028Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP028Input2654,
        batchC02703PlusFourthP028Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP028Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP028Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP028Center2654))).trans
  norm_num [batchC02703PlusFourthP028Error2654, batchC02703PlusFourthP028ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP028Center2654]

theorem batchC02703PlusFourthP028Bound2654 : batchC02703PlusFourthCell2654 ⟨28, by omega⟩ ≤
    batchC02703PlusFourthP028Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      batchC02703PlusFourthP028Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP028Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP028Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP028ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP028Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP028ExpUpper2654, batchC02703PlusFourthP028Frequency2654,
        batchC02703PlusFourthP028Upper2654]

def batchC02703PlusFourthP029Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusFourthP029Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusFourthP029Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP029ExpUpper2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02703PlusFourthP029Frequency2654 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def batchC02703PlusFourthP029Upper2654 : ℝ := ((23077101980784601582614181 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02703PlusFourthP029Exponent2654 : ℝ := (((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℝ) /
        ((2 * 10^40
        + 6525289198724544868783953343635993853315) * 10^40
        + 729354322361873471859030973612800000000))

theorem batchC02703PlusFourthP029ExpBound2654 :
    Real.exp batchC02703PlusFourthP029Exponent2654 ≤ batchC02703PlusFourthP029ExpUpper2654 := by
  have hz : ‖embedPair2542 batchC02703PlusFourthP029Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusFourthP029Input2654]
  have hc : (compactExp2547 batchC02703PlusFourthP029Input2654 14).1 =
      batchC02703PlusFourthP029Center2654 := by decide +kernel
  have he : ((compactExp2547 batchC02703PlusFourthP029Input2654 14).2 : ℝ) =
      batchC02703PlusFourthP029Error2654 := by
    have hq : (compactExp2547 batchC02703PlusFourthP029Input2654 14).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02703PlusFourthP029Error2654]
  have h := compactExp_error2547 batchC02703PlusFourthP029Input2654 hz 14
  rw [hc, he] at h
  have ha : (2 : ℂ)^14 * embedPair2542 batchC02703PlusFourthP029Input2654 =
      (batchC02703PlusFourthP029Exponent2654 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02703PlusFourthP029Input2654,
        batchC02703PlusFourthP029Exponent2654,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02703PlusFourthP029Exponent2654 : ℂ)) (embedPair2542
        batchC02703PlusFourthP029Center2654) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02703PlusFourthP029Center2654))).trans
  norm_num [batchC02703PlusFourthP029Error2654, batchC02703PlusFourthP029ExpUpper2654,
      pairMagnitude2542,
      batchC02703PlusFourthP029Center2654]

theorem batchC02703PlusFourthP029Bound2654 : batchC02703PlusFourthCell2654 ⟨29, by omega⟩ ≤
    batchC02703PlusFourthP029Upper2654 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      batchC02703PlusFourthP029Frequency2654 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02703PlusFourthP029Frequency2654])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02703PlusFourthP029Frequency2654,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02703PlusFourthP029ExpBound2654 using 1; norm_num
        [batchC02703PlusFourthP029Exponent2654])
  have hid : batchC02703PlusFourthCell2654 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) ((6127823095006419519108942183262060544 : ℝ) /
        6135428905104631913280910298972265625) (((-158400514417) : ℝ) /
        51200000000) (((-9895936151) : ℝ) /
        3200000000) := by
    norm_num [batchC02703PlusFourthCell2654, cellNearAbs2538, batchN02703PlusPosition2654,
      batchN02704PlusPosition2654, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02703PlusFourthP029ExpUpper2654, batchC02703PlusFourthP029Frequency2654,
        batchC02703PlusFourthP029Upper2654]

noncomputable def batchC02703PlusFourthP000Upper2654 : ℝ := 0

theorem batchC02703PlusFourthP000Bound2654 :
    batchC02703PlusFourthCell2654 ⟨0, by omega⟩ ≤ batchC02703PlusFourthP000Upper2654 := by
  norm_num [batchC02703PlusFourthCell2654, batchC02703PlusFourthP000Upper2654, cellNearAbs2538,
    batchN02703PlusPosition2654, batchN02704PlusPosition2654, storedWidth]

noncomputable def batchC02703PlusFourthP005Upper2654 : ℝ := 0

theorem batchC02703PlusFourthP005Bound2654 :
    batchC02703PlusFourthCell2654 ⟨5, by omega⟩ ≤ batchC02703PlusFourthP005Upper2654 := by
  norm_num [batchC02703PlusFourthCell2654, batchC02703PlusFourthP005Upper2654, cellNearAbs2538,
    batchN02703PlusPosition2654, batchN02704PlusPosition2654, storedWidth]

noncomputable def batchC02703PlusFourthUpper2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02703PlusFourthP000Upper2654
  | 1 => batchC02703PlusFourthP001Upper2654
  | 2 => batchC02703PlusFourthP002Upper2654
  | 3 => batchC02703PlusFourthP003Upper2654
  | 4 => batchC02703PlusFourthP004Upper2654
  | 5 => batchC02703PlusFourthP005Upper2654
  | 6 => batchC02703PlusFourthP006Upper2654
  | 7 => batchC02703PlusFourthP007Upper2654
  | 8 => batchC02703PlusFourthP008Upper2654
  | 9 => batchC02703PlusFourthP009Upper2654
  | 10 => batchC02703PlusFourthP010Upper2654
  | 11 => batchC02703PlusFourthP011Upper2654
  | 12 => batchC02703PlusFourthP012Upper2654
  | 13 => batchC02703PlusFourthP013Upper2654
  | 14 => batchC02703PlusFourthP014Upper2654
  | 15 => batchC02703PlusFourthP015Upper2654
  | 16 => batchC02703PlusFourthP016Upper2654
  | 17 => batchC02703PlusFourthP017Upper2654
  | 18 => batchC02703PlusFourthP018Upper2654
  | 19 => batchC02703PlusFourthP019Upper2654
  | 20 => batchC02703PlusFourthP020Upper2654
  | 21 => batchC02703PlusFourthP021Upper2654
  | 22 => batchC02703PlusFourthP022Upper2654
  | 23 => batchC02703PlusFourthP023Upper2654
  | 24 => batchC02703PlusFourthP024Upper2654
  | 25 => batchC02703PlusFourthP025Upper2654
  | 26 => batchC02703PlusFourthP026Upper2654
  | 27 => batchC02703PlusFourthP027Upper2654
  | 28 => batchC02703PlusFourthP028Upper2654
  | 29 => batchC02703PlusFourthP029Upper2654
  | _ => 0

theorem batchC02703PlusFourthBound2654 (i : Fin 30) :
    batchC02703PlusFourthCell2654 i ≤ batchC02703PlusFourthUpper2654 i := by
  fin_cases i
  · exact batchC02703PlusFourthP000Bound2654
  · exact batchC02703PlusFourthP001Bound2654
  · exact batchC02703PlusFourthP002Bound2654
  · exact batchC02703PlusFourthP003Bound2654
  · exact batchC02703PlusFourthP004Bound2654
  · exact batchC02703PlusFourthP005Bound2654
  · exact batchC02703PlusFourthP006Bound2654
  · exact batchC02703PlusFourthP007Bound2654
  · exact batchC02703PlusFourthP008Bound2654
  · exact batchC02703PlusFourthP009Bound2654
  · exact batchC02703PlusFourthP010Bound2654
  · exact batchC02703PlusFourthP011Bound2654
  · exact batchC02703PlusFourthP012Bound2654
  · exact batchC02703PlusFourthP013Bound2654
  · exact batchC02703PlusFourthP014Bound2654
  · exact batchC02703PlusFourthP015Bound2654
  · exact batchC02703PlusFourthP016Bound2654
  · exact batchC02703PlusFourthP017Bound2654
  · exact batchC02703PlusFourthP018Bound2654
  · exact batchC02703PlusFourthP019Bound2654
  · exact batchC02703PlusFourthP020Bound2654
  · exact batchC02703PlusFourthP021Bound2654
  · exact batchC02703PlusFourthP022Bound2654
  · exact batchC02703PlusFourthP023Bound2654
  · exact batchC02703PlusFourthP024Bound2654
  · exact batchC02703PlusFourthP025Bound2654
  · exact batchC02703PlusFourthP026Bound2654
  · exact batchC02703PlusFourthP027Bound2654
  · exact batchC02703PlusFourthP028Bound2654
  · exact batchC02703PlusFourthP029Bound2654

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP001Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP002Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP003Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP004Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP006Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP007Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP008Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP009Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP010Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP011Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP012Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP013Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP014Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP015Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP016Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP017Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP018Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP019Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP020Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP021Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP022Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP023Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP024Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP025Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP026Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP027Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP028Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP029Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthBound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP000Bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusFourthP005Bound2654
