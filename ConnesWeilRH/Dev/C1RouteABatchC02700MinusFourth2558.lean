import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteAKernelN02700Minus2555
import ConnesWeilRH.Dev.C1RouteAKernelN02701Minus2555

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC02700MinusFourthCell2558 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 kernelN02700MinusPosition2555 kernelN02701MinusPosition2555 < storedWidth i ^
      2 then
    weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 kernelN02700MinusPosition2555 kernelN02701MinusPosition2555 / (storedWidth
          i ^ 2))
      (min (max |kernelN02700MinusPosition2555| |kernelN02701MinusPosition2555|) (storedWidth i ^
          2) /
        (storedWidth i ^ 2)) kernelN02700MinusPosition2555 kernelN02701MinusPosition2555
  else 0


def batchC02700MinusFourthP001Input2558 : RatPair2542 := ((((-((16 * 10^40
        + 7208495491479642524820600190156438588749) * 10^40
        + 8000452220062014509668545377025959708839)) : ℚ) /
        ((23 * 10^40
        + 5402554230412661371225856431058952468867) * 10^40
        + 1100009211545199561035541697003520000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP001Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP001Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP001ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP001Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02700MinusFourthP001Upper2558 : ℝ := ((387918402585 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP001Exponent2558 : ℝ := (((-((16 * 10^40
        + 7208495491479642524820600190156438588749) * 10^40
        + 8000452220062014509668545377025959708839)) : ℝ) /
        (919541227462549458481351001683824033081 * 10^40
        + 5121484410982598435785295084753920000000))

theorem batchC02700MinusFourthP001ExpBound2558 :
    Real.exp batchC02700MinusFourthP001Exponent2558 ≤ batchC02700MinusFourthP001ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP001Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP001Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP001Input2558 8).1 =
      batchC02700MinusFourthP001Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP001Input2558 8).2 : ℝ) =
      batchC02700MinusFourthP001Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP001Input2558 8).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP001Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP001Input2558 hz 8
  rw [hc, he] at h
  have ha : (2 : ℂ)^8 * embedPair2542 batchC02700MinusFourthP001Input2558 =
      (batchC02700MinusFourthP001Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP001Input2558,
        batchC02700MinusFourthP001Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP001Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP001Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP001Center2558))).trans
  norm_num [batchC02700MinusFourthP001Error2558, batchC02700MinusFourthP001ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP001Center2558]

theorem batchC02700MinusFourthP001Bound2558 : batchC02700MinusFourthCell2558 ⟨1, by omega⟩ ≤
    batchC02700MinusFourthP001Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      batchC02700MinusFourthP001Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP001Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP001Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((95826464023198495143285394738511872 : ℝ) /
        104779244925114570282650713456640625) ((19173215621012018044377896260206592 : ℝ) /
        20955848985022914056530142691328125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP001ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP001Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((95826464023198495143285394738511872 : ℝ) /
        104779244925114570282650713456640625) ((19173215621012018044377896260206592 : ℝ) /
        20955848985022914056530142691328125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP001ExpUpper2558, batchC02700MinusFourthP001Frequency2558,
        batchC02700MinusFourthP001Upper2558]

def batchC02700MinusFourthP002Input2558 : RatPair2542 := ((((-((429 * 10^40
        + 5034123284450574114274979515214449602564) * 10^40
        + 8092590241423277358579777749792064325799)) : ℚ) /
        ((458 * 10^40
        + 5065838935301611525590279534864234933316) * 10^40
        + 4261284397731621494142166788014080000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP002Center2558 : RatPair2542 := (((209872720872778328307 : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP002Error2558 : ℝ := ((2411787434317140637 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP002ExpUpper2558 : ℝ :=
    ((14768479804966824246311959645475485 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP002Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02700MinusFourthP002Upper2558 : ℝ := ((596940360827649742619778241985 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP002Exponent2558 : ℝ := (((-((429 * 10^40
        + 5034123284450574114274979515214449602564) * 10^40
        + 8092590241423277358579777749792064325799)) : ℝ) /
        ((7 * 10^40
        + 1641653733364087680087348117732253670833) * 10^40
        + 691582568714556585845971356062720000000))

theorem batchC02700MinusFourthP002ExpBound2558 :
    Real.exp batchC02700MinusFourthP002Exponent2558 ≤ batchC02700MinusFourthP002ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP002Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP002Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP002Input2558 6).1 =
      batchC02700MinusFourthP002Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP002Input2558 6).2 : ℝ) =
      batchC02700MinusFourthP002Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP002Input2558 6).2 =
        ((2411787434317140637 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP002Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP002Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02700MinusFourthP002Input2558 =
      (batchC02700MinusFourthP002Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP002Input2558,
        batchC02700MinusFourthP002Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP002Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP002Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP002Center2558))).trans
  norm_num [batchC02700MinusFourthP002Error2558, batchC02700MinusFourthP002ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP002Center2558]

theorem batchC02700MinusFourthP002Bound2558 : batchC02700MinusFourthCell2558 ⟨2, by omega⟩ ≤
    batchC02700MinusFourthP002Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      batchC02700MinusFourthP002Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP002Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP002Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((383305856092793980573141578954047488 : ℝ) /
        535582378596426958724104076656640625) ((76692862484048072177511585040826368 : ℝ) /
        107116475719285391744820815331328125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP002ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP002Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((383305856092793980573141578954047488 : ℝ) /
        535582378596426958724104076656640625) ((76692862484048072177511585040826368 : ℝ) /
        107116475719285391744820815331328125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP002ExpUpper2558, batchC02700MinusFourthP002Frequency2558,
        batchC02700MinusFourthP002Upper2558]

def batchC02700MinusFourthP003Input2558 : RatPair2542 := ((((-((56181 * 10^40
        + 6642891191611046743714979785529808183349) * 10^40
        + 3894938324993206024073952914252819212973)) : ℚ) /
        ((83059 * 10^40
        + 5504357448729336709095381882071177666308) * 10^40
        + 629462057200198983464899243868160000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP003Center2558 : RatPair2542 := (((115683976396322413419377887111 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP003Error2558 : ℝ := ((32021432464259763299405889 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP003ExpUpper2558 : ℝ := (((25 * 10^40
        + 4391754390241670579138477857113659396161) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP003Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02700MinusFourthP003Upper2558 : ℝ :=
    ((1933178468315529751202796868875469943 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP003Exponent2558 : ℝ := (((-((56181 * 10^40
        + 6642891191611046743714979785529808183349) * 10^40
        + 3894938324993206024073952914252819212973)) : ℝ) /
        ((1297 * 10^40
        + 8054755585136395886079615341907362151036) * 10^40
        + 634835344643753109116639050685440000000))

theorem batchC02700MinusFourthP003ExpBound2558 :
    Real.exp batchC02700MinusFourthP003Exponent2558 ≤ batchC02700MinusFourthP003ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP003Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP003Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP003Input2558 6).1 =
      batchC02700MinusFourthP003Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP003Input2558 6).2 : ℝ) =
      batchC02700MinusFourthP003Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP003Input2558 6).2 =
        ((32021432464259763299405889 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP003Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP003Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02700MinusFourthP003Input2558 =
      (batchC02700MinusFourthP003Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP003Input2558,
        batchC02700MinusFourthP003Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP003Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP003Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP003Center2558))).trans
  norm_num [batchC02700MinusFourthP003Error2558, batchC02700MinusFourthP003ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP003Center2558]

theorem batchC02700MinusFourthP003Bound2558 : batchC02700MinusFourthCell2558 ⟨3, by omega⟩ ≤
    batchC02700MinusFourthP003Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      batchC02700MinusFourthP003Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP003Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP003Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) ((1227085799744769154840185360653221888 : ℝ) /
        2132188309583881559457579105517578125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP003ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP003Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) ((1227085799744769154840185360653221888 : ℝ) /
        2132188309583881559457579105517578125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP003ExpUpper2558, batchC02700MinusFourthP003Frequency2558,
        batchC02700MinusFourthP003Upper2558]

def batchC02700MinusFourthP004Input2558 : RatPair2542 := ((((-((970 * 10^40
        + 4543550619148226662501717144861843122347) * 10^40
        + 8741083521071280776766702969518626825799)) : ℚ) /
        ((1675 * 10^40
        + 3572040325635770563926718813194096824854) * 10^40
        + 2554498954096285494142166788014080000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP004Center2558 : RatPair2542 := (((3625959921806247159280567233113 : ℚ)
    /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP004Error2558 : ℝ := ((1821498541059315016755101221 : ℝ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))

noncomputable def batchC02700MinusFourthP004ExpUpper2558 : ℝ := (((1594 * 10^40
        + 7140383502899790243950753573749066087973) : ℝ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))

noncomputable def batchC02700MinusFourthP004Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02700MinusFourthP004Upper2558 : ℝ :=
    ((271497126578590859237492813434844351481 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02700MinusFourthP004Exponent2558 : ℝ := (((-((970 * 10^40
        + 4543550619148226662501717144861843122347) * 10^40
        + 8741083521071280776766702969518626825799)) : ℝ) /
        ((26 * 10^40
        + 1774563130088058915061354981456157762888) * 10^40
        + 3477414046157754460845971356062720000000))

theorem batchC02700MinusFourthP004ExpBound2558 :
    Real.exp batchC02700MinusFourthP004Exponent2558 ≤ batchC02700MinusFourthP004ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP004Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP004Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP004Input2558 6).1 =
      batchC02700MinusFourthP004Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP004Input2558 6).2 : ℝ) =
      batchC02700MinusFourthP004Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP004Input2558 6).2 =
        ((1821498541059315016755101221 : ℚ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP004Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP004Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02700MinusFourthP004Input2558 =
      (batchC02700MinusFourthP004Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP004Input2558,
        batchC02700MinusFourthP004Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP004Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP004Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP004Center2558))).trans
  norm_num [batchC02700MinusFourthP004Error2558, batchC02700MinusFourthP004ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP004Center2558]

theorem batchC02700MinusFourthP004Bound2558 : batchC02700MinusFourthCell2558 ⟨4, by omega⟩ ≤
    batchC02700MinusFourthP004Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      batchC02700MinusFourthP004Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP004Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP004Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((383305856092793980573141578954047488 : ℝ) /
        811296384146067132209863967375390625) ((76692862484048072177511585040826368 : ℝ) /
        162259276829213426441972793475078125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP004ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP004Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((383305856092793980573141578954047488 : ℝ) /
        811296384146067132209863967375390625) ((76692862484048072177511585040826368 : ℝ) /
        162259276829213426441972793475078125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP004ExpUpper2558, batchC02700MinusFourthP004Frequency2558,
        batchC02700MinusFourthP004Upper2558]

def batchC02700MinusFourthP006Input2558 : RatPair2542 := ((((-2103047969395125916265450783895627)
    : ℚ) /
        3672370076598301437993287680000000),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP006Center2558 : RatPair2542 := (((5349504961984621 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP006Error2558 : ℝ := ((7538390995201 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP006ExpUpper2558 : ℝ := ((23527371634190006079144726785 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP006Frequency2558 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02700MinusFourthP006Upper2558 : ℝ := ((661438324180436832541745 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP006Exponent2558 : ℝ :=
    (((-2103047969395125916265450783895627) : ℝ) /
        28690391223424229984322560000000)

theorem batchC02700MinusFourthP006ExpBound2558 :
    Real.exp batchC02700MinusFourthP006Exponent2558 ≤ batchC02700MinusFourthP006ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP006Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP006Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP006Input2558 7).1 =
      batchC02700MinusFourthP006Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP006Input2558 7).2 : ℝ) =
      batchC02700MinusFourthP006Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP006Input2558 7).2 =
        ((7538390995201 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP006Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP006Input2558 hz 7
  rw [hc, he] at h
  have ha : (2 : ℂ)^7 * embedPair2542 batchC02700MinusFourthP006Input2558 =
      (batchC02700MinusFourthP006Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP006Input2558,
        batchC02700MinusFourthP006Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP006Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP006Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP006Center2558))).trans
  norm_num [batchC02700MinusFourthP006Error2558, batchC02700MinusFourthP006ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP006Center2558]

theorem batchC02700MinusFourthP006Bound2558 : batchC02700MinusFourthCell2558 ⟨6, by omega⟩ ≤
    batchC02700MinusFourthP006Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      batchC02700MinusFourthP006Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP006Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP006Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) ((158531586419 : ℝ) /
        204800000000) ((7929856121 : ℝ) /
        10240000000) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP006ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP006Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) ((158531586419 : ℝ) /
        204800000000) ((7929856121 : ℝ) /
        10240000000) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP006ExpUpper2558, batchC02700MinusFourthP006Frequency2558,
        batchC02700MinusFourthP006Upper2558]

def batchC02700MinusFourthP007Input2558 : RatPair2542 := ((((-((56181 * 10^40
        + 6642891191611046743714979785529808183349) * 10^40
        + 3894938324993206024073952914252819212973)) : ℚ) /
        ((83059 * 10^40
        + 5504357448729336709095381882071177666308) * 10^40
        + 629462057200198983464899243868160000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP007Center2558 : RatPair2542 := (((115683976396322413419377887111 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP007Error2558 : ℝ := ((32021432464259763299405889 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP007ExpUpper2558 : ℝ := (((25 * 10^40
        + 4391754390241670579138477857113659396161) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP007Frequency2558 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02700MinusFourthP007Upper2558 : ℝ := ((12678843943410242828296117337719441
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP007Exponent2558 : ℝ := (((-((56181 * 10^40
        + 6642891191611046743714979785529808183349) * 10^40
        + 3894938324993206024073952914252819212973)) : ℝ) /
        ((1297 * 10^40
        + 8054755585136395886079615341907362151036) * 10^40
        + 634835344643753109116639050685440000000))

theorem batchC02700MinusFourthP007ExpBound2558 :
    Real.exp batchC02700MinusFourthP007Exponent2558 ≤ batchC02700MinusFourthP007ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP007Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP007Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP007Input2558 6).1 =
      batchC02700MinusFourthP007Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP007Input2558 6).2 : ℝ) =
      batchC02700MinusFourthP007Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP007Input2558 6).2 =
        ((32021432464259763299405889 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP007Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP007Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02700MinusFourthP007Input2558 =
      (batchC02700MinusFourthP007Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP007Input2558,
        batchC02700MinusFourthP007Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP007Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP007Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP007Center2558))).trans
  norm_num [batchC02700MinusFourthP007Error2558, batchC02700MinusFourthP007ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP007Center2558]

theorem batchC02700MinusFourthP007Bound2558 : batchC02700MinusFourthCell2558 ⟨7, by omega⟩ ≤
    batchC02700MinusFourthP007Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      batchC02700MinusFourthP007Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP007Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP007Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) ((1227085799744769154840185360653221888 : ℝ) /
        2132188309583881559457579105517578125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP007ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP007Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) ((1227085799744769154840185360653221888 : ℝ) /
        2132188309583881559457579105517578125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP007ExpUpper2558, batchC02700MinusFourthP007Frequency2558,
        batchC02700MinusFourthP007Upper2558]

def batchC02700MinusFourthP008Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP008Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP008Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP008ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP008Frequency2558 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def batchC02700MinusFourthP008Upper2558 : ℝ := ((1513212029608543513716512408467 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP008Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP008ExpBound2558 :
    Real.exp batchC02700MinusFourthP008Exponent2558 ≤ batchC02700MinusFourthP008ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP008Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP008Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP008Input2558 16).1 =
      batchC02700MinusFourthP008Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP008Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP008Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP008Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP008Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP008Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP008Input2558 =
      (batchC02700MinusFourthP008Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP008Input2558,
        batchC02700MinusFourthP008Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP008Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP008Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP008Center2558))).trans
  norm_num [batchC02700MinusFourthP008Error2558, batchC02700MinusFourthP008ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP008Center2558]

theorem batchC02700MinusFourthP008Bound2558 : batchC02700MinusFourthCell2558 ⟨8, by omega⟩ ≤
    batchC02700MinusFourthP008Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      batchC02700MinusFourthP008Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP008Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP008Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP008ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP008Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP008ExpUpper2558, batchC02700MinusFourthP008Frequency2558,
        batchC02700MinusFourthP008Upper2558]

def batchC02700MinusFourthP009Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP009Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP009Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP009ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP009Frequency2558 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def batchC02700MinusFourthP009Upper2558 : ℝ := ((756606702514067810266035928231 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02700MinusFourthP009Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP009ExpBound2558 :
    Real.exp batchC02700MinusFourthP009Exponent2558 ≤ batchC02700MinusFourthP009ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP009Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP009Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP009Input2558 16).1 =
      batchC02700MinusFourthP009Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP009Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP009Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP009Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP009Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP009Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP009Input2558 =
      (batchC02700MinusFourthP009Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP009Input2558,
        batchC02700MinusFourthP009Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP009Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP009Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP009Center2558))).trans
  norm_num [batchC02700MinusFourthP009Error2558, batchC02700MinusFourthP009ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP009Center2558]

theorem batchC02700MinusFourthP009Bound2558 : batchC02700MinusFourthCell2558 ⟨9, by omega⟩ ≤
    batchC02700MinusFourthP009Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      batchC02700MinusFourthP009Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP009Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP009Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP009ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP009Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP009ExpUpper2558, batchC02700MinusFourthP009Frequency2558,
        batchC02700MinusFourthP009Upper2558]

def batchC02700MinusFourthP010Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP010Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP010Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP010ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP010Frequency2558 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def batchC02700MinusFourthP010Upper2558 : ℝ := ((1513214201754394692916962659401 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP010Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP010ExpBound2558 :
    Real.exp batchC02700MinusFourthP010Exponent2558 ≤ batchC02700MinusFourthP010ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP010Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP010Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP010Input2558 16).1 =
      batchC02700MinusFourthP010Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP010Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP010Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP010Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP010Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP010Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP010Input2558 =
      (batchC02700MinusFourthP010Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP010Input2558,
        batchC02700MinusFourthP010Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP010Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP010Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP010Center2558))).trans
  norm_num [batchC02700MinusFourthP010Error2558, batchC02700MinusFourthP010ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP010Center2558]

theorem batchC02700MinusFourthP010Bound2558 : batchC02700MinusFourthCell2558 ⟨10, by omega⟩ ≤
    batchC02700MinusFourthP010Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      batchC02700MinusFourthP010Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP010Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP010Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP010ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP010Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP010ExpUpper2558, batchC02700MinusFourthP010Frequency2558,
        batchC02700MinusFourthP010Upper2558]

def batchC02700MinusFourthP011Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP011Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP011Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP011ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP011Frequency2558 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def batchC02700MinusFourthP011Upper2558 : ℝ := ((189151841623269213146709186821 : ℝ)
    /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC02700MinusFourthP011Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP011ExpBound2558 :
    Real.exp batchC02700MinusFourthP011Exponent2558 ≤ batchC02700MinusFourthP011ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP011Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP011Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP011Input2558 16).1 =
      batchC02700MinusFourthP011Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP011Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP011Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP011Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP011Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP011Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP011Input2558 =
      (batchC02700MinusFourthP011Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP011Input2558,
        batchC02700MinusFourthP011Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP011Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP011Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP011Center2558))).trans
  norm_num [batchC02700MinusFourthP011Error2558, batchC02700MinusFourthP011ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP011Center2558]

theorem batchC02700MinusFourthP011Bound2558 : batchC02700MinusFourthCell2558 ⟨11, by omega⟩ ≤
    batchC02700MinusFourthP011Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      batchC02700MinusFourthP011Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP011Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP011Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP011ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP011Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP011ExpUpper2558, batchC02700MinusFourthP011Frequency2558,
        batchC02700MinusFourthP011Upper2558]

def batchC02700MinusFourthP012Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP012Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP012Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP012ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP012Frequency2558 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def batchC02700MinusFourthP012Upper2558 : ℝ := ((1513215283230071596715993367975 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP012Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP012ExpBound2558 :
    Real.exp batchC02700MinusFourthP012Exponent2558 ≤ batchC02700MinusFourthP012ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP012Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP012Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP012Input2558 16).1 =
      batchC02700MinusFourthP012Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP012Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP012Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP012Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP012Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP012Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP012Input2558 =
      (batchC02700MinusFourthP012Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP012Input2558,
        batchC02700MinusFourthP012Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP012Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP012Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP012Center2558))).trans
  norm_num [batchC02700MinusFourthP012Error2558, batchC02700MinusFourthP012ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP012Center2558]

theorem batchC02700MinusFourthP012Bound2558 : batchC02700MinusFourthCell2558 ⟨12, by omega⟩ ≤
    batchC02700MinusFourthP012Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      batchC02700MinusFourthP012Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP012Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP012Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP012ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP012Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP012ExpUpper2558, batchC02700MinusFourthP012Frequency2558,
        batchC02700MinusFourthP012Upper2558]

def batchC02700MinusFourthP013Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP013Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP013Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP013ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP013Frequency2558 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def batchC02700MinusFourthP013Upper2558 : ℝ := ((1513215784671438379443123399037 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP013Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP013ExpBound2558 :
    Real.exp batchC02700MinusFourthP013Exponent2558 ≤ batchC02700MinusFourthP013ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP013Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP013Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP013Input2558 16).1 =
      batchC02700MinusFourthP013Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP013Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP013Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP013Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP013Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP013Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP013Input2558 =
      (batchC02700MinusFourthP013Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP013Input2558,
        batchC02700MinusFourthP013Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP013Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP013Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP013Center2558))).trans
  norm_num [batchC02700MinusFourthP013Error2558, batchC02700MinusFourthP013ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP013Center2558]

theorem batchC02700MinusFourthP013Bound2558 : batchC02700MinusFourthCell2558 ⟨13, by omega⟩ ≤
    batchC02700MinusFourthP013Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      batchC02700MinusFourthP013Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP013Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP013Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP013ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP013Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP013ExpUpper2558, batchC02700MinusFourthP013Frequency2558,
        batchC02700MinusFourthP013Upper2558]

def batchC02700MinusFourthP014Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP014Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP014Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP014ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP014Frequency2558 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def batchC02700MinusFourthP014Upper2558 : ℝ := ((378304178453336207927296424261 : ℝ)
    /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02700MinusFourthP014Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP014ExpBound2558 :
    Real.exp batchC02700MinusFourthP014Exponent2558 ≤ batchC02700MinusFourthP014ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP014Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP014Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP014Input2558 16).1 =
      batchC02700MinusFourthP014Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP014Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP014Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP014Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP014Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP014Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP014Input2558 =
      (batchC02700MinusFourthP014Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP014Input2558,
        batchC02700MinusFourthP014Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP014Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP014Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP014Center2558))).trans
  norm_num [batchC02700MinusFourthP014Error2558, batchC02700MinusFourthP014ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP014Center2558]

theorem batchC02700MinusFourthP014Bound2558 : batchC02700MinusFourthCell2558 ⟨14, by omega⟩ ≤
    batchC02700MinusFourthP014Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      batchC02700MinusFourthP014Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP014Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP014Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP014ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP014Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP014ExpUpper2558, batchC02700MinusFourthP014Frequency2558,
        batchC02700MinusFourthP014Upper2558]

def batchC02700MinusFourthP015Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP015Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP015Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP015ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP015Frequency2558 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def batchC02700MinusFourthP015Upper2558 : ℝ := ((94576086222503903653034159775 : ℝ)
    /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC02700MinusFourthP015Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP015ExpBound2558 :
    Real.exp batchC02700MinusFourthP015Exponent2558 ≤ batchC02700MinusFourthP015ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP015Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP015Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP015Input2558 16).1 =
      batchC02700MinusFourthP015Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP015Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP015Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP015Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP015Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP015Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP015Input2558 =
      (batchC02700MinusFourthP015Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP015Input2558,
        batchC02700MinusFourthP015Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP015Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP015Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP015Center2558))).trans
  norm_num [batchC02700MinusFourthP015Error2558, batchC02700MinusFourthP015ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP015Center2558]

theorem batchC02700MinusFourthP015Bound2558 : batchC02700MinusFourthCell2558 ⟨15, by omega⟩ ≤
    batchC02700MinusFourthP015Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      batchC02700MinusFourthP015Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP015Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP015Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP015ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP015Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP015ExpUpper2558, batchC02700MinusFourthP015Frequency2558,
        batchC02700MinusFourthP015Upper2558]

def batchC02700MinusFourthP016Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP016Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP016Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP016ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP016Frequency2558 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def batchC02700MinusFourthP016Upper2558 : ℝ := ((756608930342974629604475951035 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02700MinusFourthP016Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP016ExpBound2558 :
    Real.exp batchC02700MinusFourthP016Exponent2558 ≤ batchC02700MinusFourthP016ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP016Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP016Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP016Input2558 16).1 =
      batchC02700MinusFourthP016Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP016Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP016Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP016Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP016Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP016Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP016Input2558 =
      (batchC02700MinusFourthP016Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP016Input2558,
        batchC02700MinusFourthP016Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP016Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP016Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP016Center2558))).trans
  norm_num [batchC02700MinusFourthP016Error2558, batchC02700MinusFourthP016ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP016Center2558]

theorem batchC02700MinusFourthP016Bound2558 : batchC02700MinusFourthCell2558 ⟨16, by omega⟩ ≤
    batchC02700MinusFourthP016Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      batchC02700MinusFourthP016Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP016Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP016Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP016ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP016Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP016ExpUpper2558, batchC02700MinusFourthP016Frequency2558,
        batchC02700MinusFourthP016Upper2558]

def batchC02700MinusFourthP017Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP017Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP017Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP017ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP017Frequency2558 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def batchC02700MinusFourthP017Upper2558 : ℝ := ((1513218795252961646618336077019 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP017Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP017ExpBound2558 :
    Real.exp batchC02700MinusFourthP017Exponent2558 ≤ batchC02700MinusFourthP017ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP017Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP017Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP017Input2558 16).1 =
      batchC02700MinusFourthP017Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP017Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP017Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP017Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP017Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP017Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP017Input2558 =
      (batchC02700MinusFourthP017Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP017Input2558,
        batchC02700MinusFourthP017Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP017Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP017Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP017Center2558))).trans
  norm_num [batchC02700MinusFourthP017Error2558, batchC02700MinusFourthP017ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP017Center2558]

theorem batchC02700MinusFourthP017Bound2558 : batchC02700MinusFourthCell2558 ⟨17, by omega⟩ ≤
    batchC02700MinusFourthP017Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      batchC02700MinusFourthP017Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP017Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP017Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP017ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP017Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP017ExpUpper2558, batchC02700MinusFourthP017Frequency2558,
        batchC02700MinusFourthP017Upper2558]

def batchC02700MinusFourthP018Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP018Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP018Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP018ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP018Frequency2558 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def batchC02700MinusFourthP018Upper2558 : ℝ := ((1513219148595726417363633881407 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP018Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP018ExpBound2558 :
    Real.exp batchC02700MinusFourthP018Exponent2558 ≤ batchC02700MinusFourthP018ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP018Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP018Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP018Input2558 16).1 =
      batchC02700MinusFourthP018Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP018Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP018Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP018Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP018Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP018Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP018Input2558 =
      (batchC02700MinusFourthP018Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP018Input2558,
        batchC02700MinusFourthP018Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP018Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP018Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP018Center2558))).trans
  norm_num [batchC02700MinusFourthP018Error2558, batchC02700MinusFourthP018ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP018Center2558]

theorem batchC02700MinusFourthP018Bound2558 : batchC02700MinusFourthCell2558 ⟨18, by omega⟩ ≤
    batchC02700MinusFourthP018Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      batchC02700MinusFourthP018Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP018Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP018Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP018ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP018Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP018ExpUpper2558, batchC02700MinusFourthP018Frequency2558,
        batchC02700MinusFourthP018Upper2558]

def batchC02700MinusFourthP019Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP019Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP019Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP019ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP019Frequency2558 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def batchC02700MinusFourthP019Upper2558 : ℝ := ((1513219787185555825140071648211 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP019Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP019ExpBound2558 :
    Real.exp batchC02700MinusFourthP019Exponent2558 ≤ batchC02700MinusFourthP019ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP019Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP019Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP019Input2558 16).1 =
      batchC02700MinusFourthP019Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP019Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP019Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP019Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP019Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP019Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP019Input2558 =
      (batchC02700MinusFourthP019Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP019Input2558,
        batchC02700MinusFourthP019Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP019Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP019Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP019Center2558))).trans
  norm_num [batchC02700MinusFourthP019Error2558, batchC02700MinusFourthP019ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP019Center2558]

theorem batchC02700MinusFourthP019Bound2558 : batchC02700MinusFourthCell2558 ⟨19, by omega⟩ ≤
    batchC02700MinusFourthP019Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      batchC02700MinusFourthP019Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP019Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP019Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP019ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP019Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP019ExpUpper2558, batchC02700MinusFourthP019Frequency2558,
        batchC02700MinusFourthP019Upper2558]

def batchC02700MinusFourthP020Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP020Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP020Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP020ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP020Frequency2558 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def batchC02700MinusFourthP020Upper2558 : ℝ := ((1513220481605061174870213665839 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP020Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP020ExpBound2558 :
    Real.exp batchC02700MinusFourthP020Exponent2558 ≤ batchC02700MinusFourthP020ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP020Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP020Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP020Input2558 16).1 =
      batchC02700MinusFourthP020Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP020Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP020Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP020Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP020Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP020Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP020Input2558 =
      (batchC02700MinusFourthP020Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP020Input2558,
        batchC02700MinusFourthP020Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP020Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP020Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP020Center2558))).trans
  norm_num [batchC02700MinusFourthP020Error2558, batchC02700MinusFourthP020ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP020Center2558]

theorem batchC02700MinusFourthP020Bound2558 : batchC02700MinusFourthCell2558 ⟨20, by omega⟩ ≤
    batchC02700MinusFourthP020Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      batchC02700MinusFourthP020Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP020Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP020Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP020ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP020Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP020ExpUpper2558, batchC02700MinusFourthP020Frequency2558,
        batchC02700MinusFourthP020Upper2558]

def batchC02700MinusFourthP021Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP021Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP021Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP021ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP021Frequency2558 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def batchC02700MinusFourthP021Upper2558 : ℝ := ((1513221061128071202416242363039 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP021Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP021ExpBound2558 :
    Real.exp batchC02700MinusFourthP021Exponent2558 ≤ batchC02700MinusFourthP021ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP021Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP021Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP021Input2558 16).1 =
      batchC02700MinusFourthP021Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP021Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP021Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP021Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP021Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP021Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP021Input2558 =
      (batchC02700MinusFourthP021Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP021Input2558,
        batchC02700MinusFourthP021Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP021Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP021Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP021Center2558))).trans
  norm_num [batchC02700MinusFourthP021Error2558, batchC02700MinusFourthP021ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP021Center2558]

theorem batchC02700MinusFourthP021Bound2558 : batchC02700MinusFourthCell2558 ⟨21, by omega⟩ ≤
    batchC02700MinusFourthP021Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      batchC02700MinusFourthP021Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP021Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP021Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP021ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP021Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP021ExpUpper2558, batchC02700MinusFourthP021Frequency2558,
        batchC02700MinusFourthP021Upper2558]

def batchC02700MinusFourthP022Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP022Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP022Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP022ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP022Frequency2558 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def batchC02700MinusFourthP022Upper2558 : ℝ := ((1513221357750181715440148886747 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP022Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP022ExpBound2558 :
    Real.exp batchC02700MinusFourthP022Exponent2558 ≤ batchC02700MinusFourthP022ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP022Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP022Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP022Input2558 16).1 =
      batchC02700MinusFourthP022Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP022Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP022Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP022Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP022Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP022Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP022Input2558 =
      (batchC02700MinusFourthP022Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP022Input2558,
        batchC02700MinusFourthP022Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP022Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP022Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP022Center2558))).trans
  norm_num [batchC02700MinusFourthP022Error2558, batchC02700MinusFourthP022ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP022Center2558]

theorem batchC02700MinusFourthP022Bound2558 : batchC02700MinusFourthCell2558 ⟨22, by omega⟩ ≤
    batchC02700MinusFourthP022Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      batchC02700MinusFourthP022Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP022Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP022Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP022ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP022Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP022ExpUpper2558, batchC02700MinusFourthP022Frequency2558,
        batchC02700MinusFourthP022Upper2558]

def batchC02700MinusFourthP023Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP023Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP023Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP023ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP023Frequency2558 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def batchC02700MinusFourthP023Upper2558 : ℝ := ((1513222212969713444427698005981 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP023Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP023ExpBound2558 :
    Real.exp batchC02700MinusFourthP023Exponent2558 ≤ batchC02700MinusFourthP023ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP023Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP023Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP023Input2558 16).1 =
      batchC02700MinusFourthP023Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP023Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP023Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP023Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP023Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP023Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP023Input2558 =
      (batchC02700MinusFourthP023Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP023Input2558,
        batchC02700MinusFourthP023Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP023Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP023Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP023Center2558))).trans
  norm_num [batchC02700MinusFourthP023Error2558, batchC02700MinusFourthP023ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP023Center2558]

theorem batchC02700MinusFourthP023Bound2558 : batchC02700MinusFourthCell2558 ⟨23, by omega⟩ ≤
    batchC02700MinusFourthP023Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      batchC02700MinusFourthP023Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP023Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP023Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP023ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP023Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP023ExpUpper2558, batchC02700MinusFourthP023Frequency2558,
        batchC02700MinusFourthP023Upper2558]

def batchC02700MinusFourthP024Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP024Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP024Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP024ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP024Frequency2558 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def batchC02700MinusFourthP024Upper2558 : ℝ := ((1513222605995255298282635227107 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP024Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP024ExpBound2558 :
    Real.exp batchC02700MinusFourthP024Exponent2558 ≤ batchC02700MinusFourthP024ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP024Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP024Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP024Input2558 16).1 =
      batchC02700MinusFourthP024Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP024Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP024Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP024Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP024Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP024Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP024Input2558 =
      (batchC02700MinusFourthP024Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP024Input2558,
        batchC02700MinusFourthP024Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP024Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP024Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP024Center2558))).trans
  norm_num [batchC02700MinusFourthP024Error2558, batchC02700MinusFourthP024ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP024Center2558]

theorem batchC02700MinusFourthP024Bound2558 : batchC02700MinusFourthCell2558 ⟨24, by omega⟩ ≤
    batchC02700MinusFourthP024Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      batchC02700MinusFourthP024Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP024Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP024Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP024ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP024Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP024ExpUpper2558, batchC02700MinusFourthP024Frequency2558,
        batchC02700MinusFourthP024Upper2558]

def batchC02700MinusFourthP025Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP025Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP025Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP025ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP025Frequency2558 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def batchC02700MinusFourthP025Upper2558 : ℝ := ((1513223098778174306315115326937 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP025Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP025ExpBound2558 :
    Real.exp batchC02700MinusFourthP025Exponent2558 ≤ batchC02700MinusFourthP025ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP025Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP025Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP025Input2558 16).1 =
      batchC02700MinusFourthP025Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP025Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP025Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP025Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP025Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP025Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP025Input2558 =
      (batchC02700MinusFourthP025Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP025Input2558,
        batchC02700MinusFourthP025Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP025Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP025Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP025Center2558))).trans
  norm_num [batchC02700MinusFourthP025Error2558, batchC02700MinusFourthP025ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP025Center2558]

theorem batchC02700MinusFourthP025Bound2558 : batchC02700MinusFourthCell2558 ⟨25, by omega⟩ ≤
    batchC02700MinusFourthP025Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      batchC02700MinusFourthP025Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP025Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP025Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP025ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP025Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP025ExpUpper2558, batchC02700MinusFourthP025Frequency2558,
        batchC02700MinusFourthP025Upper2558]

def batchC02700MinusFourthP026Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP026Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP026Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP026ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP026Frequency2558 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def batchC02700MinusFourthP026Upper2558 : ℝ := ((94576475148959604957330419529 : ℝ)
    /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC02700MinusFourthP026Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP026ExpBound2558 :
    Real.exp batchC02700MinusFourthP026Exponent2558 ≤ batchC02700MinusFourthP026ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP026Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP026Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP026Input2558 16).1 =
      batchC02700MinusFourthP026Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP026Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP026Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP026Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP026Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP026Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP026Input2558 =
      (batchC02700MinusFourthP026Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP026Input2558,
        batchC02700MinusFourthP026Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP026Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP026Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP026Center2558))).trans
  norm_num [batchC02700MinusFourthP026Error2558, batchC02700MinusFourthP026ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP026Center2558]

theorem batchC02700MinusFourthP026Bound2558 : batchC02700MinusFourthCell2558 ⟨26, by omega⟩ ≤
    batchC02700MinusFourthP026Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      batchC02700MinusFourthP026Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP026Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP026Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP026ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP026Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP026ExpUpper2558, batchC02700MinusFourthP026Frequency2558,
        batchC02700MinusFourthP026Upper2558]

def batchC02700MinusFourthP027Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP027Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP027Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP027ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP027Frequency2558 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def batchC02700MinusFourthP027Upper2558 : ℝ := ((756612164551870758986594776787 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02700MinusFourthP027Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP027ExpBound2558 :
    Real.exp batchC02700MinusFourthP027Exponent2558 ≤ batchC02700MinusFourthP027ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP027Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP027Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP027Input2558 16).1 =
      batchC02700MinusFourthP027Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP027Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP027Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP027Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP027Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP027Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP027Input2558 =
      (batchC02700MinusFourthP027Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP027Input2558,
        batchC02700MinusFourthP027Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP027Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP027Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP027Center2558))).trans
  norm_num [batchC02700MinusFourthP027Error2558, batchC02700MinusFourthP027ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP027Center2558]

theorem batchC02700MinusFourthP027Bound2558 : batchC02700MinusFourthCell2558 ⟨27, by omega⟩ ≤
    batchC02700MinusFourthP027Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      batchC02700MinusFourthP027Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP027Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP027Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP027ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP027Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP027ExpUpper2558, batchC02700MinusFourthP027Frequency2558,
        batchC02700MinusFourthP027Upper2558]

def batchC02700MinusFourthP028Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP028Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP028Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP028ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP028Frequency2558 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def batchC02700MinusFourthP028Upper2558 : ℝ := ((1513224616822848179541214867455 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700MinusFourthP028Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP028ExpBound2558 :
    Real.exp batchC02700MinusFourthP028Exponent2558 ≤ batchC02700MinusFourthP028ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP028Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP028Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP028Input2558 16).1 =
      batchC02700MinusFourthP028Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP028Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP028Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP028Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP028Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP028Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP028Input2558 =
      (batchC02700MinusFourthP028Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP028Input2558,
        batchC02700MinusFourthP028Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP028Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP028Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP028Center2558))).trans
  norm_num [batchC02700MinusFourthP028Error2558, batchC02700MinusFourthP028ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP028Center2558]

theorem batchC02700MinusFourthP028Bound2558 : batchC02700MinusFourthCell2558 ⟨28, by omega⟩ ≤
    batchC02700MinusFourthP028Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      batchC02700MinusFourthP028Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP028Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP028Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP028ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP028Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP028ExpUpper2558, batchC02700MinusFourthP028Frequency2558,
        batchC02700MinusFourthP028Upper2558]

def batchC02700MinusFourthP029Input2558 : RatPair2542 := ((((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℚ) /
        ((34787 * 10^40
        + 8313432644289368360009462987544252906893) * 10^40
        + 6146716648575573468056825720995840000000)),
    ((0 : ℚ) /
        1))

def batchC02700MinusFourthP029Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusFourthP029Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP029ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700MinusFourthP029Frequency2558 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def batchC02700MinusFourthP029Upper2558 : ℝ := ((756612527428611981465617900939 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02700MinusFourthP029Exponent2558 : ℝ := (((-((19272 * 10^40
        + 6436446838704807160565844990241783749103) * 10^40
        + 7976423772701329204662571085639537962973)) : ℝ) /
        (5308201804086979513067016745956230838819 * 10^40
        + 9904421184030892571616639050685440000000))

theorem batchC02700MinusFourthP029ExpBound2558 :
    Real.exp batchC02700MinusFourthP029Exponent2558 ≤ batchC02700MinusFourthP029ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700MinusFourthP029Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700MinusFourthP029Input2558]
  have hc : (compactExp2547 batchC02700MinusFourthP029Input2558 16).1 =
      batchC02700MinusFourthP029Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700MinusFourthP029Input2558 16).2 : ℝ) =
      batchC02700MinusFourthP029Error2558 := by
    have hq : (compactExp2547 batchC02700MinusFourthP029Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700MinusFourthP029Error2558]
  have h := compactExp_error2547 batchC02700MinusFourthP029Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700MinusFourthP029Input2558 =
      (batchC02700MinusFourthP029Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700MinusFourthP029Input2558,
        batchC02700MinusFourthP029Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700MinusFourthP029Exponent2558 : ℂ)) (embedPair2542
        batchC02700MinusFourthP029Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700MinusFourthP029Center2558))).trans
  norm_num [batchC02700MinusFourthP029Error2558, batchC02700MinusFourthP029ExpUpper2558,
      pairMagnitude2542,
      batchC02700MinusFourthP029Center2558]

theorem batchC02700MinusFourthP029Bound2558 : batchC02700MinusFourthCell2558 ⟨29, by omega⟩ ≤
    batchC02700MinusFourthP029Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      batchC02700MinusFourthP029Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700MinusFourthP029Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700MinusFourthP029Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700MinusFourthP029ExpBound2558 using 1; norm_num
        [batchC02700MinusFourthP029Exponent2558])
  have hid : batchC02700MinusFourthCell2558 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700MinusFourthCell2558, cellNearAbs2538, kernelN02700MinusPosition2555,
      kernelN02701MinusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700MinusFourthP029ExpUpper2558, batchC02700MinusFourthP029Frequency2558,
        batchC02700MinusFourthP029Upper2558]

noncomputable def batchC02700MinusFourthP000Upper2558 : ℝ := 0

theorem batchC02700MinusFourthP000Bound2558 :
    batchC02700MinusFourthCell2558 ⟨0, by omega⟩ ≤ batchC02700MinusFourthP000Upper2558 := by
  norm_num [batchC02700MinusFourthCell2558, batchC02700MinusFourthP000Upper2558, cellNearAbs2538,
    kernelN02700MinusPosition2555, kernelN02701MinusPosition2555, storedWidth]

noncomputable def batchC02700MinusFourthP005Upper2558 : ℝ := 0

theorem batchC02700MinusFourthP005Bound2558 :
    batchC02700MinusFourthCell2558 ⟨5, by omega⟩ ≤ batchC02700MinusFourthP005Upper2558 := by
  norm_num [batchC02700MinusFourthCell2558, batchC02700MinusFourthP005Upper2558, cellNearAbs2538,
    kernelN02700MinusPosition2555, kernelN02701MinusPosition2555, storedWidth]

noncomputable def batchC02700MinusFourthUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02700MinusFourthP000Upper2558
  | 1 => batchC02700MinusFourthP001Upper2558
  | 2 => batchC02700MinusFourthP002Upper2558
  | 3 => batchC02700MinusFourthP003Upper2558
  | 4 => batchC02700MinusFourthP004Upper2558
  | 5 => batchC02700MinusFourthP005Upper2558
  | 6 => batchC02700MinusFourthP006Upper2558
  | 7 => batchC02700MinusFourthP007Upper2558
  | 8 => batchC02700MinusFourthP008Upper2558
  | 9 => batchC02700MinusFourthP009Upper2558
  | 10 => batchC02700MinusFourthP010Upper2558
  | 11 => batchC02700MinusFourthP011Upper2558
  | 12 => batchC02700MinusFourthP012Upper2558
  | 13 => batchC02700MinusFourthP013Upper2558
  | 14 => batchC02700MinusFourthP014Upper2558
  | 15 => batchC02700MinusFourthP015Upper2558
  | 16 => batchC02700MinusFourthP016Upper2558
  | 17 => batchC02700MinusFourthP017Upper2558
  | 18 => batchC02700MinusFourthP018Upper2558
  | 19 => batchC02700MinusFourthP019Upper2558
  | 20 => batchC02700MinusFourthP020Upper2558
  | 21 => batchC02700MinusFourthP021Upper2558
  | 22 => batchC02700MinusFourthP022Upper2558
  | 23 => batchC02700MinusFourthP023Upper2558
  | 24 => batchC02700MinusFourthP024Upper2558
  | 25 => batchC02700MinusFourthP025Upper2558
  | 26 => batchC02700MinusFourthP026Upper2558
  | 27 => batchC02700MinusFourthP027Upper2558
  | 28 => batchC02700MinusFourthP028Upper2558
  | 29 => batchC02700MinusFourthP029Upper2558
  | _ => 0

theorem batchC02700MinusFourthBound2558 (i : Fin 30) :
    batchC02700MinusFourthCell2558 i ≤ batchC02700MinusFourthUpper2558 i := by
  fin_cases i
  · exact batchC02700MinusFourthP000Bound2558
  · exact batchC02700MinusFourthP001Bound2558
  · exact batchC02700MinusFourthP002Bound2558
  · exact batchC02700MinusFourthP003Bound2558
  · exact batchC02700MinusFourthP004Bound2558
  · exact batchC02700MinusFourthP005Bound2558
  · exact batchC02700MinusFourthP006Bound2558
  · exact batchC02700MinusFourthP007Bound2558
  · exact batchC02700MinusFourthP008Bound2558
  · exact batchC02700MinusFourthP009Bound2558
  · exact batchC02700MinusFourthP010Bound2558
  · exact batchC02700MinusFourthP011Bound2558
  · exact batchC02700MinusFourthP012Bound2558
  · exact batchC02700MinusFourthP013Bound2558
  · exact batchC02700MinusFourthP014Bound2558
  · exact batchC02700MinusFourthP015Bound2558
  · exact batchC02700MinusFourthP016Bound2558
  · exact batchC02700MinusFourthP017Bound2558
  · exact batchC02700MinusFourthP018Bound2558
  · exact batchC02700MinusFourthP019Bound2558
  · exact batchC02700MinusFourthP020Bound2558
  · exact batchC02700MinusFourthP021Bound2558
  · exact batchC02700MinusFourthP022Bound2558
  · exact batchC02700MinusFourthP023Bound2558
  · exact batchC02700MinusFourthP024Bound2558
  · exact batchC02700MinusFourthP025Bound2558
  · exact batchC02700MinusFourthP026Bound2558
  · exact batchC02700MinusFourthP027Bound2558
  · exact batchC02700MinusFourthP028Bound2558
  · exact batchC02700MinusFourthP029Bound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP001Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP002Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP003Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP004Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP006Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP007Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP008Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP009Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP010Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP011Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP012Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP013Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP014Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP015Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP016Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP017Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP018Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP019Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP020Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP021Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP022Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP023Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP024Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP025Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP026Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP027Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP028Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP029Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthBound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP000Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusFourthP005Bound2558
