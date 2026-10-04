import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteAKernelN02700Plus2555
import ConnesWeilRH.Dev.C1RouteAKernelN02701Plus2555

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC02700PlusFourthCell2558 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 kernelN02700PlusPosition2555 kernelN02701PlusPosition2555 < storedWidth i ^ 2
      then
    weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 kernelN02700PlusPosition2555 kernelN02701PlusPosition2555 / (storedWidth i
          ^ 2))
      (min (max |kernelN02700PlusPosition2555| |kernelN02701PlusPosition2555|) (storedWidth i ^ 2)
          /
        (storedWidth i ^ 2)) kernelN02700PlusPosition2555 kernelN02701PlusPosition2555
  else 0


def batchC02700PlusFourthP001Input2558 : RatPair2542 := ((((-((340 * 10^40
        + 1125558694715412604882605546165965236561) * 10^40
        + 9325600687173468560131001925406640200979)) : ℚ) /
        ((470 * 10^40
        + 8051084608253227424517128621179049377342) * 10^40
        + 2000184230903991220710833940070400000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP001Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP001Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP001ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP001Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02700PlusFourthP001Upper2558 : ℝ := ((387918402585 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP001Exponent2558 : ℝ := (((-((340 * 10^40
        + 1125558694715412604882605546165965236561) * 10^40
        + 9325600687173468560131001925406640200979)) : ℝ) /
        ((1 * 10^40
        + 8390824549250989169627020033676480661630) * 10^40
        + 2429688219651968715705901695078400000000))

theorem batchC02700PlusFourthP001ExpBound2558 :
    Real.exp batchC02700PlusFourthP001Exponent2558 ≤ batchC02700PlusFourthP001ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP001Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP001Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP001Input2558 8).1 =
      batchC02700PlusFourthP001Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP001Input2558 8).2 : ℝ) =
      batchC02700PlusFourthP001Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP001Input2558 8).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP001Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP001Input2558 hz 8
  rw [hc, he] at h
  have ha : (2 : ℂ)^8 * embedPair2542 batchC02700PlusFourthP001Input2558 =
      (batchC02700PlusFourthP001Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP001Input2558,
        batchC02700PlusFourthP001Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP001Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP001Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP001Center2558))).trans
  norm_num [batchC02700PlusFourthP001Error2558, batchC02700PlusFourthP001ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP001Center2558]

theorem batchC02700PlusFourthP001Bound2558 : batchC02700PlusFourthCell2558 ⟨1, by omega⟩ ≤
    batchC02700PlusFourthP001Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      batchC02700PlusFourthP001Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP001Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP001Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((95826464023198495143285394738511872 : ℝ) /
        104779244925114570282650713456640625) ((19173215621012018044377896260206592 : ℝ) /
        20955848985022914056530142691328125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP001ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP001Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((95826464023198495143285394738511872 : ℝ) /
        104779244925114570282650713456640625) ((19173215621012018044377896260206592 : ℝ) /
        20955848985022914056530142691328125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP001ExpUpper2558, batchC02700PlusFourthP001Frequency2558,
        batchC02700PlusFourthP001Upper2558]

def batchC02700PlusFourthP002Input2558 : RatPair2542 := ((((-((9033 * 10^40
        + 8109252320354666245907324545684805984286) * 10^40
        + 2898018879638657721153554737628069387539)) : ℚ) /
        ((9170 * 10^40
        + 1316778706032230511805590697284698666328) * 10^40
        + 5225687954632429882843335760281600000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP002Center2558 : RatPair2542 := (((606936572380043288435 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP002Error2558 : ℝ := ((57192599555477919 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02700PlusFourthP002ExpUpper2558 : ℝ := ((333666909327183776474854918263199
    : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02700PlusFourthP002Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02700PlusFourthP002Upper2558 : ℝ := ((1685847560821978649209278511 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC02700PlusFourthP002Exponent2558 : ℝ := (((-((9033 * 10^40
        + 8109252320354666245907324545684805984286) * 10^40
        + 2898018879638657721153554737628069387539)) : ℝ) /
        ((143 * 10^40
        + 2833074667281753601746962354645073416661) * 10^40
        + 3831651374291131716919427121254400000000))

theorem batchC02700PlusFourthP002ExpBound2558 :
    Real.exp batchC02700PlusFourthP002Exponent2558 ≤ batchC02700PlusFourthP002ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP002Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP002Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP002Input2558 6).1 =
      batchC02700PlusFourthP002Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP002Input2558 6).2 : ℝ) =
      batchC02700PlusFourthP002Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP002Input2558 6).2 =
        ((57192599555477919 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP002Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP002Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02700PlusFourthP002Input2558 =
      (batchC02700PlusFourthP002Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP002Input2558,
        batchC02700PlusFourthP002Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP002Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP002Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP002Center2558))).trans
  norm_num [batchC02700PlusFourthP002Error2558, batchC02700PlusFourthP002ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP002Center2558]

theorem batchC02700PlusFourthP002Bound2558 : batchC02700PlusFourthCell2558 ⟨2, by omega⟩ ≤
    batchC02700PlusFourthP002Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      batchC02700PlusFourthP002Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP002Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP002Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((383305856092793980573141578954047488 : ℝ) /
        535582378596426958724104076656640625) ((76692862484048072177511585040826368 : ℝ) /
        107116475719285391744820815331328125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP002ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP002Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((383305856092793980573141578954047488 : ℝ) /
        535582378596426958724104076656640625) ((76692862484048072177511585040826368 : ℝ) /
        107116475719285391744820815331328125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP002ExpUpper2558, batchC02700PlusFourthP002Frequency2558,
        batchC02700PlusFourthP002Upper2558]

def batchC02700PlusFourthP003Input2558 : RatPair2542 := ((((-((1204018 * 10^40
        + 3199206753711006565389390034201102437777) * 10^40
        + 7349271424128768512973515705970498543953)) : ℚ) /
        ((1661191 * 10^40
        + 87148974586734181907637641423553326161) * 10^40
        + 2589241144003979669297984877363200000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP003Center2558 : RatPair2542 := (((163354299886446954699714643 : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP003Error2558 : ℝ := ((759335337735088749674751 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02700PlusFourthP003ExpUpper2558 : ℝ :=
    ((5747518469515397339270101908132996841727 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02700PlusFourthP003Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02700PlusFourthP003Upper2558 : ℝ := ((21838323687308956104556534204092651
    : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02700PlusFourthP003Exponent2558 : ℝ := (((-((1204018 * 10^40
        + 3199206753711006565389390034201102437777) * 10^40
        + 7349271424128768512973515705970498543953)) : ℝ) /
        ((25956 * 10^40
        + 1095111702727917721592306838147243020721) * 10^40
        + 2696706892875062182332781013708800000000))

theorem batchC02700PlusFourthP003ExpBound2558 :
    Real.exp batchC02700PlusFourthP003Exponent2558 ≤ batchC02700PlusFourthP003ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP003Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP003Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP003Input2558 6).1 =
      batchC02700PlusFourthP003Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP003Input2558 6).2 : ℝ) =
      batchC02700PlusFourthP003Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP003Input2558 6).2 =
        ((759335337735088749674751 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP003Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP003Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02700PlusFourthP003Input2558 =
      (batchC02700PlusFourthP003Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP003Input2558,
        batchC02700PlusFourthP003Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP003Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP003Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP003Center2558))).trans
  norm_num [batchC02700PlusFourthP003Error2558, batchC02700PlusFourthP003ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP003Center2558]

theorem batchC02700PlusFourthP003Bound2558 : batchC02700PlusFourthCell2558 ⟨3, by omega⟩ ≤
    batchC02700PlusFourthP003Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      batchC02700PlusFourthP003Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP003Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP003Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) ((1227085799744769154840185360653221888 : ℝ) /
        2132188309583881559457579105517578125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP003ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP003Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) ((1227085799744769154840185360653221888 : ℝ) /
        2132188309583881559457579105517578125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP003ExpUpper2558, batchC02700PlusFourthP003Frequency2558,
        batchC02700PlusFourthP003Upper2558]

def batchC02700PlusFourthP004Input2558 : RatPair2542 := ((((-((21030 * 10^40
        + 4978280417753696551825490501735319367009) * 10^40
        + 9100087780138783714176925758135881887539)) : ℚ) /
        ((33507 * 10^40
        + 1440806512715411278534376263881936497085) * 10^40
        + 1089979081925709882843335760281600000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP004Center2558 : RatPair2542 := (((5243005563983089941503791278595 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP004Error2558 : ℝ := ((345550614926699585689874555 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02700PlusFourthP004ExpUpper2558 : ℝ := (((288 * 10^40
        + 2372791046836415411138011701256068001915) : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02700PlusFourthP004Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02700PlusFourthP004Upper2558 : ℝ :=
    ((24535932828028298201929589790441057037 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP004Exponent2558 : ℝ := (((-((21030 * 10^40
        + 4978280417753696551825490501735319367009) * 10^40
        + 9100087780138783714176925758135881887539)) : ℝ) /
        ((523 * 10^40
        + 5491262601761178301227099629123155257766) * 10^40
        + 9548280923155089216919427121254400000000))

theorem batchC02700PlusFourthP004ExpBound2558 :
    Real.exp batchC02700PlusFourthP004Exponent2558 ≤ batchC02700PlusFourthP004ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP004Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP004Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP004Input2558 6).1 =
      batchC02700PlusFourthP004Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP004Input2558 6).2 : ℝ) =
      batchC02700PlusFourthP004Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP004Input2558 6).2 =
        ((345550614926699585689874555 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP004Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP004Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02700PlusFourthP004Input2558 =
      (batchC02700PlusFourthP004Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP004Input2558,
        batchC02700PlusFourthP004Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP004Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP004Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP004Center2558))).trans
  norm_num [batchC02700PlusFourthP004Error2558, batchC02700PlusFourthP004ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP004Center2558]

theorem batchC02700PlusFourthP004Bound2558 : batchC02700PlusFourthCell2558 ⟨4, by omega⟩ ≤
    batchC02700PlusFourthP004Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      batchC02700PlusFourthP004Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP004Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP004Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((383305856092793980573141578954047488 : ℝ) /
        811296384146067132209863967375390625) ((76692862484048072177511585040826368 : ℝ) /
        162259276829213426441972793475078125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP004ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP004Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((383305856092793980573141578954047488 : ℝ) /
        811296384146067132209863967375390625) ((76692862484048072177511585040826368 : ℝ) /
        162259276829213426441972793475078125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP004ExpUpper2558, batchC02700PlusFourthP004Frequency2558,
        batchC02700PlusFourthP004Upper2558]

def batchC02700PlusFourthP006Input2558 : RatPair2542 := ((((-43838019295084218252511359948400647)
    : ℚ) /
        73447401531966028759865753600000000),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP006Center2558 : RatPair2542 := (((483449294895075 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP006Error2558 : ℝ := ((2446198475405 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP006ExpUpper2558 : ℝ := ((1063116242354489166949681805 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP006Frequency2558 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02700PlusFourthP006Upper2558 : ℝ := ((7471997262223778628361 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02700PlusFourthP006Exponent2558 : ℝ :=
    (((-43838019295084218252511359948400647) : ℝ)
    /
        573807824468484599686451200000000)

theorem batchC02700PlusFourthP006ExpBound2558 :
    Real.exp batchC02700PlusFourthP006Exponent2558 ≤ batchC02700PlusFourthP006ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP006Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP006Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP006Input2558 7).1 =
      batchC02700PlusFourthP006Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP006Input2558 7).2 : ℝ) =
      batchC02700PlusFourthP006Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP006Input2558 7).2 =
        ((2446198475405 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP006Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP006Input2558 hz 7
  rw [hc, he] at h
  have ha : (2 : ℂ)^7 * embedPair2542 batchC02700PlusFourthP006Input2558 =
      (batchC02700PlusFourthP006Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP006Input2558,
        batchC02700PlusFourthP006Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP006Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP006Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP006Center2558))).trans
  norm_num [batchC02700PlusFourthP006Error2558, batchC02700PlusFourthP006ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP006Center2558]

theorem batchC02700PlusFourthP006Bound2558 : batchC02700PlusFourthCell2558 ⟨6, by omega⟩ ≤
    batchC02700PlusFourthP006Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      batchC02700PlusFourthP006Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP006Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP006Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) ((158531586419 : ℝ) /
        204800000000) ((7929856121 : ℝ) /
        10240000000) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP006ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP006Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) ((158531586419 : ℝ) /
        204800000000) ((7929856121 : ℝ) /
        10240000000) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP006ExpUpper2558, batchC02700PlusFourthP006Frequency2558,
        batchC02700PlusFourthP006Upper2558]

def batchC02700PlusFourthP007Input2558 : RatPair2542 := ((((-((1204018 * 10^40
        + 3199206753711006565389390034201102437777) * 10^40
        + 7349271424128768512973515705970498543953)) : ℚ) /
        ((1661191 * 10^40
        + 87148974586734181907637641423553326161) * 10^40
        + 2589241144003979669297984877363200000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP007Center2558 : RatPair2542 := (((163354299886446954699714643 : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP007Error2558 : ℝ := ((759335337735088749674751 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02700PlusFourthP007ExpUpper2558 : ℝ :=
    ((5747518469515397339270101908132996841727 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02700PlusFourthP007Frequency2558 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02700PlusFourthP007Upper2558 : ℝ := ((572910784089856726997890950156811 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP007Exponent2558 : ℝ := (((-((1204018 * 10^40
        + 3199206753711006565389390034201102437777) * 10^40
        + 7349271424128768512973515705970498543953)) : ℝ) /
        ((25956 * 10^40
        + 1095111702727917721592306838147243020721) * 10^40
        + 2696706892875062182332781013708800000000))

theorem batchC02700PlusFourthP007ExpBound2558 :
    Real.exp batchC02700PlusFourthP007Exponent2558 ≤ batchC02700PlusFourthP007ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP007Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP007Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP007Input2558 6).1 =
      batchC02700PlusFourthP007Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP007Input2558 6).2 : ℝ) =
      batchC02700PlusFourthP007Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP007Input2558 6).2 =
        ((759335337735088749674751 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP007Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP007Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02700PlusFourthP007Input2558 =
      (batchC02700PlusFourthP007Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP007Input2558,
        batchC02700PlusFourthP007Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP007Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP007Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP007Center2558))).trans
  norm_num [batchC02700PlusFourthP007Error2558, batchC02700PlusFourthP007ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP007Center2558]

theorem batchC02700PlusFourthP007Bound2558 : batchC02700PlusFourthCell2558 ⟨7, by omega⟩ ≤
    batchC02700PlusFourthP007Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      batchC02700PlusFourthP007Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP007Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP007Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) ((1227085799744769154840185360653221888 : ℝ) /
        2132188309583881559457579105517578125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP007ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP007Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) ((1227085799744769154840185360653221888 : ℝ) /
        2132188309583881559457579105517578125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP007ExpUpper2558, batchC02700PlusFourthP007Frequency2558,
        batchC02700PlusFourthP007Upper2558]

def batchC02700PlusFourthP008Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP008Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP008Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP008ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP008Frequency2558 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def batchC02700PlusFourthP008Upper2558 : ℝ := ((1513212029608543513716512408467 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP008Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP008ExpBound2558 :
    Real.exp batchC02700PlusFourthP008Exponent2558 ≤ batchC02700PlusFourthP008ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP008Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP008Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP008Input2558 16).1 =
      batchC02700PlusFourthP008Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP008Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP008Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP008Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP008Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP008Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP008Input2558 =
      (batchC02700PlusFourthP008Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP008Input2558,
        batchC02700PlusFourthP008Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP008Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP008Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP008Center2558))).trans
  norm_num [batchC02700PlusFourthP008Error2558, batchC02700PlusFourthP008ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP008Center2558]

theorem batchC02700PlusFourthP008Bound2558 : batchC02700PlusFourthCell2558 ⟨8, by omega⟩ ≤
    batchC02700PlusFourthP008Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      batchC02700PlusFourthP008Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP008Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP008Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP008ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP008Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP008ExpUpper2558, batchC02700PlusFourthP008Frequency2558,
        batchC02700PlusFourthP008Upper2558]

def batchC02700PlusFourthP009Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP009Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP009Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP009ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP009Frequency2558 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def batchC02700PlusFourthP009Upper2558 : ℝ := ((756606702514067810266035928231 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02700PlusFourthP009Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP009ExpBound2558 :
    Real.exp batchC02700PlusFourthP009Exponent2558 ≤ batchC02700PlusFourthP009ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP009Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP009Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP009Input2558 16).1 =
      batchC02700PlusFourthP009Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP009Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP009Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP009Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP009Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP009Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP009Input2558 =
      (batchC02700PlusFourthP009Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP009Input2558,
        batchC02700PlusFourthP009Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP009Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP009Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP009Center2558))).trans
  norm_num [batchC02700PlusFourthP009Error2558, batchC02700PlusFourthP009ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP009Center2558]

theorem batchC02700PlusFourthP009Bound2558 : batchC02700PlusFourthCell2558 ⟨9, by omega⟩ ≤
    batchC02700PlusFourthP009Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      batchC02700PlusFourthP009Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP009Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP009Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP009ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP009Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP009ExpUpper2558, batchC02700PlusFourthP009Frequency2558,
        batchC02700PlusFourthP009Upper2558]

def batchC02700PlusFourthP010Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP010Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP010Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP010ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP010Frequency2558 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def batchC02700PlusFourthP010Upper2558 : ℝ := ((1513214201754394692916962659401 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP010Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP010ExpBound2558 :
    Real.exp batchC02700PlusFourthP010Exponent2558 ≤ batchC02700PlusFourthP010ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP010Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP010Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP010Input2558 16).1 =
      batchC02700PlusFourthP010Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP010Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP010Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP010Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP010Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP010Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP010Input2558 =
      (batchC02700PlusFourthP010Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP010Input2558,
        batchC02700PlusFourthP010Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP010Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP010Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP010Center2558))).trans
  norm_num [batchC02700PlusFourthP010Error2558, batchC02700PlusFourthP010ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP010Center2558]

theorem batchC02700PlusFourthP010Bound2558 : batchC02700PlusFourthCell2558 ⟨10, by omega⟩ ≤
    batchC02700PlusFourthP010Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      batchC02700PlusFourthP010Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP010Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP010Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP010ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP010Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP010ExpUpper2558, batchC02700PlusFourthP010Frequency2558,
        batchC02700PlusFourthP010Upper2558]

def batchC02700PlusFourthP011Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP011Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP011Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP011ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP011Frequency2558 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def batchC02700PlusFourthP011Upper2558 : ℝ := ((189151841623269213146709186821 : ℝ)
    /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC02700PlusFourthP011Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP011ExpBound2558 :
    Real.exp batchC02700PlusFourthP011Exponent2558 ≤ batchC02700PlusFourthP011ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP011Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP011Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP011Input2558 16).1 =
      batchC02700PlusFourthP011Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP011Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP011Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP011Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP011Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP011Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP011Input2558 =
      (batchC02700PlusFourthP011Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP011Input2558,
        batchC02700PlusFourthP011Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP011Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP011Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP011Center2558))).trans
  norm_num [batchC02700PlusFourthP011Error2558, batchC02700PlusFourthP011ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP011Center2558]

theorem batchC02700PlusFourthP011Bound2558 : batchC02700PlusFourthCell2558 ⟨11, by omega⟩ ≤
    batchC02700PlusFourthP011Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      batchC02700PlusFourthP011Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP011Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP011Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP011ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP011Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP011ExpUpper2558, batchC02700PlusFourthP011Frequency2558,
        batchC02700PlusFourthP011Upper2558]

def batchC02700PlusFourthP012Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP012Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP012Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP012ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP012Frequency2558 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def batchC02700PlusFourthP012Upper2558 : ℝ := ((1513215283230071596715993367975 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP012Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP012ExpBound2558 :
    Real.exp batchC02700PlusFourthP012Exponent2558 ≤ batchC02700PlusFourthP012ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP012Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP012Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP012Input2558 16).1 =
      batchC02700PlusFourthP012Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP012Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP012Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP012Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP012Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP012Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP012Input2558 =
      (batchC02700PlusFourthP012Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP012Input2558,
        batchC02700PlusFourthP012Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP012Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP012Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP012Center2558))).trans
  norm_num [batchC02700PlusFourthP012Error2558, batchC02700PlusFourthP012ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP012Center2558]

theorem batchC02700PlusFourthP012Bound2558 : batchC02700PlusFourthCell2558 ⟨12, by omega⟩ ≤
    batchC02700PlusFourthP012Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      batchC02700PlusFourthP012Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP012Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP012Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP012ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP012Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP012ExpUpper2558, batchC02700PlusFourthP012Frequency2558,
        batchC02700PlusFourthP012Upper2558]

def batchC02700PlusFourthP013Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP013Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP013Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP013ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP013Frequency2558 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def batchC02700PlusFourthP013Upper2558 : ℝ := ((1513215784671438379443123399037 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP013Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP013ExpBound2558 :
    Real.exp batchC02700PlusFourthP013Exponent2558 ≤ batchC02700PlusFourthP013ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP013Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP013Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP013Input2558 16).1 =
      batchC02700PlusFourthP013Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP013Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP013Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP013Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP013Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP013Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP013Input2558 =
      (batchC02700PlusFourthP013Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP013Input2558,
        batchC02700PlusFourthP013Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP013Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP013Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP013Center2558))).trans
  norm_num [batchC02700PlusFourthP013Error2558, batchC02700PlusFourthP013ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP013Center2558]

theorem batchC02700PlusFourthP013Bound2558 : batchC02700PlusFourthCell2558 ⟨13, by omega⟩ ≤
    batchC02700PlusFourthP013Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      batchC02700PlusFourthP013Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP013Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP013Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP013ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP013Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP013ExpUpper2558, batchC02700PlusFourthP013Frequency2558,
        batchC02700PlusFourthP013Upper2558]

def batchC02700PlusFourthP014Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP014Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP014Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP014ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP014Frequency2558 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def batchC02700PlusFourthP014Upper2558 : ℝ := ((378304178453336207927296424261 : ℝ)
    /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02700PlusFourthP014Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP014ExpBound2558 :
    Real.exp batchC02700PlusFourthP014Exponent2558 ≤ batchC02700PlusFourthP014ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP014Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP014Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP014Input2558 16).1 =
      batchC02700PlusFourthP014Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP014Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP014Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP014Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP014Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP014Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP014Input2558 =
      (batchC02700PlusFourthP014Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP014Input2558,
        batchC02700PlusFourthP014Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP014Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP014Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP014Center2558))).trans
  norm_num [batchC02700PlusFourthP014Error2558, batchC02700PlusFourthP014ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP014Center2558]

theorem batchC02700PlusFourthP014Bound2558 : batchC02700PlusFourthCell2558 ⟨14, by omega⟩ ≤
    batchC02700PlusFourthP014Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      batchC02700PlusFourthP014Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP014Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP014Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP014ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP014Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP014ExpUpper2558, batchC02700PlusFourthP014Frequency2558,
        batchC02700PlusFourthP014Upper2558]

def batchC02700PlusFourthP015Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP015Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP015Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP015ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP015Frequency2558 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def batchC02700PlusFourthP015Upper2558 : ℝ := ((94576086222503903653034159775 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC02700PlusFourthP015Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP015ExpBound2558 :
    Real.exp batchC02700PlusFourthP015Exponent2558 ≤ batchC02700PlusFourthP015ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP015Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP015Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP015Input2558 16).1 =
      batchC02700PlusFourthP015Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP015Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP015Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP015Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP015Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP015Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP015Input2558 =
      (batchC02700PlusFourthP015Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP015Input2558,
        batchC02700PlusFourthP015Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP015Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP015Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP015Center2558))).trans
  norm_num [batchC02700PlusFourthP015Error2558, batchC02700PlusFourthP015ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP015Center2558]

theorem batchC02700PlusFourthP015Bound2558 : batchC02700PlusFourthCell2558 ⟨15, by omega⟩ ≤
    batchC02700PlusFourthP015Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      batchC02700PlusFourthP015Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP015Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP015Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP015ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP015Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP015ExpUpper2558, batchC02700PlusFourthP015Frequency2558,
        batchC02700PlusFourthP015Upper2558]

def batchC02700PlusFourthP016Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP016Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP016Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP016ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP016Frequency2558 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def batchC02700PlusFourthP016Upper2558 : ℝ := ((756608930342974629604475951035 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02700PlusFourthP016Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP016ExpBound2558 :
    Real.exp batchC02700PlusFourthP016Exponent2558 ≤ batchC02700PlusFourthP016ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP016Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP016Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP016Input2558 16).1 =
      batchC02700PlusFourthP016Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP016Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP016Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP016Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP016Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP016Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP016Input2558 =
      (batchC02700PlusFourthP016Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP016Input2558,
        batchC02700PlusFourthP016Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP016Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP016Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP016Center2558))).trans
  norm_num [batchC02700PlusFourthP016Error2558, batchC02700PlusFourthP016ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP016Center2558]

theorem batchC02700PlusFourthP016Bound2558 : batchC02700PlusFourthCell2558 ⟨16, by omega⟩ ≤
    batchC02700PlusFourthP016Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      batchC02700PlusFourthP016Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP016Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP016Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP016ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP016Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP016ExpUpper2558, batchC02700PlusFourthP016Frequency2558,
        batchC02700PlusFourthP016Upper2558]

def batchC02700PlusFourthP017Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP017Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP017Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP017ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP017Frequency2558 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def batchC02700PlusFourthP017Upper2558 : ℝ := ((1513218795252961646618336077019 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP017Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP017ExpBound2558 :
    Real.exp batchC02700PlusFourthP017Exponent2558 ≤ batchC02700PlusFourthP017ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP017Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP017Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP017Input2558 16).1 =
      batchC02700PlusFourthP017Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP017Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP017Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP017Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP017Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP017Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP017Input2558 =
      (batchC02700PlusFourthP017Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP017Input2558,
        batchC02700PlusFourthP017Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP017Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP017Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP017Center2558))).trans
  norm_num [batchC02700PlusFourthP017Error2558, batchC02700PlusFourthP017ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP017Center2558]

theorem batchC02700PlusFourthP017Bound2558 : batchC02700PlusFourthCell2558 ⟨17, by omega⟩ ≤
    batchC02700PlusFourthP017Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      batchC02700PlusFourthP017Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP017Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP017Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP017ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP017Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP017ExpUpper2558, batchC02700PlusFourthP017Frequency2558,
        batchC02700PlusFourthP017Upper2558]

def batchC02700PlusFourthP018Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP018Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP018Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP018ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP018Frequency2558 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def batchC02700PlusFourthP018Upper2558 : ℝ := ((1513219148595726417363633881407 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP018Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP018ExpBound2558 :
    Real.exp batchC02700PlusFourthP018Exponent2558 ≤ batchC02700PlusFourthP018ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP018Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP018Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP018Input2558 16).1 =
      batchC02700PlusFourthP018Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP018Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP018Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP018Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP018Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP018Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP018Input2558 =
      (batchC02700PlusFourthP018Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP018Input2558,
        batchC02700PlusFourthP018Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP018Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP018Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP018Center2558))).trans
  norm_num [batchC02700PlusFourthP018Error2558, batchC02700PlusFourthP018ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP018Center2558]

theorem batchC02700PlusFourthP018Bound2558 : batchC02700PlusFourthCell2558 ⟨18, by omega⟩ ≤
    batchC02700PlusFourthP018Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      batchC02700PlusFourthP018Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP018Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP018Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP018ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP018Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP018ExpUpper2558, batchC02700PlusFourthP018Frequency2558,
        batchC02700PlusFourthP018Upper2558]

def batchC02700PlusFourthP019Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP019Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP019Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP019ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP019Frequency2558 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def batchC02700PlusFourthP019Upper2558 : ℝ := ((1513219787185555825140071648211 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP019Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP019ExpBound2558 :
    Real.exp batchC02700PlusFourthP019Exponent2558 ≤ batchC02700PlusFourthP019ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP019Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP019Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP019Input2558 16).1 =
      batchC02700PlusFourthP019Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP019Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP019Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP019Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP019Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP019Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP019Input2558 =
      (batchC02700PlusFourthP019Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP019Input2558,
        batchC02700PlusFourthP019Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP019Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP019Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP019Center2558))).trans
  norm_num [batchC02700PlusFourthP019Error2558, batchC02700PlusFourthP019ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP019Center2558]

theorem batchC02700PlusFourthP019Bound2558 : batchC02700PlusFourthCell2558 ⟨19, by omega⟩ ≤
    batchC02700PlusFourthP019Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      batchC02700PlusFourthP019Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP019Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP019Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP019ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP019Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP019ExpUpper2558, batchC02700PlusFourthP019Frequency2558,
        batchC02700PlusFourthP019Upper2558]

def batchC02700PlusFourthP020Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP020Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP020Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP020ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP020Frequency2558 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def batchC02700PlusFourthP020Upper2558 : ℝ := ((1513220481605061174870213665839 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP020Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP020ExpBound2558 :
    Real.exp batchC02700PlusFourthP020Exponent2558 ≤ batchC02700PlusFourthP020ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP020Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP020Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP020Input2558 16).1 =
      batchC02700PlusFourthP020Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP020Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP020Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP020Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP020Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP020Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP020Input2558 =
      (batchC02700PlusFourthP020Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP020Input2558,
        batchC02700PlusFourthP020Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP020Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP020Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP020Center2558))).trans
  norm_num [batchC02700PlusFourthP020Error2558, batchC02700PlusFourthP020ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP020Center2558]

theorem batchC02700PlusFourthP020Bound2558 : batchC02700PlusFourthCell2558 ⟨20, by omega⟩ ≤
    batchC02700PlusFourthP020Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      batchC02700PlusFourthP020Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP020Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP020Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP020ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP020Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP020ExpUpper2558, batchC02700PlusFourthP020Frequency2558,
        batchC02700PlusFourthP020Upper2558]

def batchC02700PlusFourthP021Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP021Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP021Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP021ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP021Frequency2558 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def batchC02700PlusFourthP021Upper2558 : ℝ := ((1513221061128071202416242363039 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP021Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP021ExpBound2558 :
    Real.exp batchC02700PlusFourthP021Exponent2558 ≤ batchC02700PlusFourthP021ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP021Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP021Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP021Input2558 16).1 =
      batchC02700PlusFourthP021Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP021Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP021Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP021Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP021Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP021Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP021Input2558 =
      (batchC02700PlusFourthP021Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP021Input2558,
        batchC02700PlusFourthP021Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP021Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP021Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP021Center2558))).trans
  norm_num [batchC02700PlusFourthP021Error2558, batchC02700PlusFourthP021ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP021Center2558]

theorem batchC02700PlusFourthP021Bound2558 : batchC02700PlusFourthCell2558 ⟨21, by omega⟩ ≤
    batchC02700PlusFourthP021Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      batchC02700PlusFourthP021Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP021Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP021Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP021ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP021Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP021ExpUpper2558, batchC02700PlusFourthP021Frequency2558,
        batchC02700PlusFourthP021Upper2558]

def batchC02700PlusFourthP022Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP022Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP022Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP022ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP022Frequency2558 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def batchC02700PlusFourthP022Upper2558 : ℝ := ((1513221357750181715440148886747 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP022Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP022ExpBound2558 :
    Real.exp batchC02700PlusFourthP022Exponent2558 ≤ batchC02700PlusFourthP022ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP022Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP022Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP022Input2558 16).1 =
      batchC02700PlusFourthP022Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP022Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP022Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP022Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP022Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP022Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP022Input2558 =
      (batchC02700PlusFourthP022Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP022Input2558,
        batchC02700PlusFourthP022Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP022Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP022Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP022Center2558))).trans
  norm_num [batchC02700PlusFourthP022Error2558, batchC02700PlusFourthP022ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP022Center2558]

theorem batchC02700PlusFourthP022Bound2558 : batchC02700PlusFourthCell2558 ⟨22, by omega⟩ ≤
    batchC02700PlusFourthP022Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      batchC02700PlusFourthP022Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP022Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP022Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP022ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP022Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP022ExpUpper2558, batchC02700PlusFourthP022Frequency2558,
        batchC02700PlusFourthP022Upper2558]

def batchC02700PlusFourthP023Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP023Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP023Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP023ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP023Frequency2558 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def batchC02700PlusFourthP023Upper2558 : ℝ := ((1513222212969713444427698005981 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP023Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP023ExpBound2558 :
    Real.exp batchC02700PlusFourthP023Exponent2558 ≤ batchC02700PlusFourthP023ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP023Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP023Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP023Input2558 16).1 =
      batchC02700PlusFourthP023Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP023Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP023Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP023Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP023Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP023Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP023Input2558 =
      (batchC02700PlusFourthP023Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP023Input2558,
        batchC02700PlusFourthP023Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP023Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP023Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP023Center2558))).trans
  norm_num [batchC02700PlusFourthP023Error2558, batchC02700PlusFourthP023ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP023Center2558]

theorem batchC02700PlusFourthP023Bound2558 : batchC02700PlusFourthCell2558 ⟨23, by omega⟩ ≤
    batchC02700PlusFourthP023Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      batchC02700PlusFourthP023Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP023Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP023Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP023ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP023Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP023ExpUpper2558, batchC02700PlusFourthP023Frequency2558,
        batchC02700PlusFourthP023Upper2558]

def batchC02700PlusFourthP024Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP024Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP024Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP024ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP024Frequency2558 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def batchC02700PlusFourthP024Upper2558 : ℝ := ((1513222605995255298282635227107 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP024Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP024ExpBound2558 :
    Real.exp batchC02700PlusFourthP024Exponent2558 ≤ batchC02700PlusFourthP024ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP024Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP024Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP024Input2558 16).1 =
      batchC02700PlusFourthP024Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP024Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP024Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP024Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP024Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP024Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP024Input2558 =
      (batchC02700PlusFourthP024Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP024Input2558,
        batchC02700PlusFourthP024Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP024Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP024Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP024Center2558))).trans
  norm_num [batchC02700PlusFourthP024Error2558, batchC02700PlusFourthP024ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP024Center2558]

theorem batchC02700PlusFourthP024Bound2558 : batchC02700PlusFourthCell2558 ⟨24, by omega⟩ ≤
    batchC02700PlusFourthP024Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      batchC02700PlusFourthP024Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP024Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP024Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP024ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP024Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP024ExpUpper2558, batchC02700PlusFourthP024Frequency2558,
        batchC02700PlusFourthP024Upper2558]

def batchC02700PlusFourthP025Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP025Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP025Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP025ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP025Frequency2558 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def batchC02700PlusFourthP025Upper2558 : ℝ := ((1513223098778174306315115326937 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP025Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP025ExpBound2558 :
    Real.exp batchC02700PlusFourthP025Exponent2558 ≤ batchC02700PlusFourthP025ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP025Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP025Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP025Input2558 16).1 =
      batchC02700PlusFourthP025Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP025Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP025Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP025Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP025Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP025Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP025Input2558 =
      (batchC02700PlusFourthP025Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP025Input2558,
        batchC02700PlusFourthP025Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP025Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP025Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP025Center2558))).trans
  norm_num [batchC02700PlusFourthP025Error2558, batchC02700PlusFourthP025ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP025Center2558]

theorem batchC02700PlusFourthP025Bound2558 : batchC02700PlusFourthCell2558 ⟨25, by omega⟩ ≤
    batchC02700PlusFourthP025Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      batchC02700PlusFourthP025Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP025Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP025Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP025ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP025Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP025ExpUpper2558, batchC02700PlusFourthP025Frequency2558,
        batchC02700PlusFourthP025Upper2558]

def batchC02700PlusFourthP026Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP026Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP026Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP026ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP026Frequency2558 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def batchC02700PlusFourthP026Upper2558 : ℝ := ((94576475148959604957330419529 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC02700PlusFourthP026Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP026ExpBound2558 :
    Real.exp batchC02700PlusFourthP026Exponent2558 ≤ batchC02700PlusFourthP026ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP026Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP026Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP026Input2558 16).1 =
      batchC02700PlusFourthP026Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP026Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP026Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP026Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP026Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP026Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP026Input2558 =
      (batchC02700PlusFourthP026Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP026Input2558,
        batchC02700PlusFourthP026Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP026Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP026Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP026Center2558))).trans
  norm_num [batchC02700PlusFourthP026Error2558, batchC02700PlusFourthP026ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP026Center2558]

theorem batchC02700PlusFourthP026Bound2558 : batchC02700PlusFourthCell2558 ⟨26, by omega⟩ ≤
    batchC02700PlusFourthP026Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      batchC02700PlusFourthP026Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP026Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP026Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP026ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP026Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP026ExpUpper2558, batchC02700PlusFourthP026Frequency2558,
        batchC02700PlusFourthP026Upper2558]

def batchC02700PlusFourthP027Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP027Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP027Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP027ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP027Frequency2558 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def batchC02700PlusFourthP027Upper2558 : ℝ := ((756612164551870758986594776787 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02700PlusFourthP027Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP027ExpBound2558 :
    Real.exp batchC02700PlusFourthP027Exponent2558 ≤ batchC02700PlusFourthP027ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP027Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP027Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP027Input2558 16).1 =
      batchC02700PlusFourthP027Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP027Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP027Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP027Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP027Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP027Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP027Input2558 =
      (batchC02700PlusFourthP027Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP027Input2558,
        batchC02700PlusFourthP027Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP027Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP027Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP027Center2558))).trans
  norm_num [batchC02700PlusFourthP027Error2558, batchC02700PlusFourthP027ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP027Center2558]

theorem batchC02700PlusFourthP027Bound2558 : batchC02700PlusFourthCell2558 ⟨27, by omega⟩ ≤
    batchC02700PlusFourthP027Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      batchC02700PlusFourthP027Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP027Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP027Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP027ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP027Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP027ExpUpper2558, batchC02700PlusFourthP027Frequency2558,
        batchC02700PlusFourthP027Upper2558]

def batchC02700PlusFourthP028Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP028Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP028Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP028ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP028Frequency2558 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def batchC02700PlusFourthP028Upper2558 : ℝ := ((1513224616822848179541214867455 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02700PlusFourthP028Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP028ExpBound2558 :
    Real.exp batchC02700PlusFourthP028Exponent2558 ≤ batchC02700PlusFourthP028ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP028Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP028Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP028Input2558 16).1 =
      batchC02700PlusFourthP028Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP028Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP028Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP028Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP028Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP028Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP028Input2558 =
      (batchC02700PlusFourthP028Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP028Input2558,
        batchC02700PlusFourthP028Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP028Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP028Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP028Center2558))).trans
  norm_num [batchC02700PlusFourthP028Error2558, batchC02700PlusFourthP028ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP028Center2558]

theorem batchC02700PlusFourthP028Bound2558 : batchC02700PlusFourthCell2558 ⟨28, by omega⟩ ≤
    batchC02700PlusFourthP028Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      batchC02700PlusFourthP028Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP028Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP028Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP028ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP028Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP028ExpUpper2558, batchC02700PlusFourthP028Frequency2558,
        batchC02700PlusFourthP028Upper2558]

def batchC02700PlusFourthP029Input2558 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusFourthP029Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusFourthP029Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP029ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02700PlusFourthP029Frequency2558 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def batchC02700PlusFourthP029Upper2558 : ℝ := ((756612527428611981465617900939 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02700PlusFourthP029Exponent2558 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem batchC02700PlusFourthP029ExpBound2558 :
    Real.exp batchC02700PlusFourthP029Exponent2558 ≤ batchC02700PlusFourthP029ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02700PlusFourthP029Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusFourthP029Input2558]
  have hc : (compactExp2547 batchC02700PlusFourthP029Input2558 16).1 =
      batchC02700PlusFourthP029Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02700PlusFourthP029Input2558 16).2 : ℝ) =
      batchC02700PlusFourthP029Error2558 := by
    have hq : (compactExp2547 batchC02700PlusFourthP029Input2558 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02700PlusFourthP029Error2558]
  have h := compactExp_error2547 batchC02700PlusFourthP029Input2558 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 batchC02700PlusFourthP029Input2558 =
      (batchC02700PlusFourthP029Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02700PlusFourthP029Input2558,
        batchC02700PlusFourthP029Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02700PlusFourthP029Exponent2558 : ℂ)) (embedPair2542
        batchC02700PlusFourthP029Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02700PlusFourthP029Center2558))).trans
  norm_num [batchC02700PlusFourthP029Error2558, batchC02700PlusFourthP029ExpUpper2558,
      pairMagnitude2542,
      batchC02700PlusFourthP029Center2558]

theorem batchC02700PlusFourthP029Bound2558 : batchC02700PlusFourthCell2558 ⟨29, by omega⟩ ≤
    batchC02700PlusFourthP029Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      batchC02700PlusFourthP029Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02700PlusFourthP029Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02700PlusFourthP029Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02700PlusFourthP029ExpBound2558 using 1; norm_num
        [batchC02700PlusFourthP029Exponent2558])
  have hid : batchC02700PlusFourthCell2558 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [batchC02700PlusFourthCell2558, cellNearAbs2538, kernelN02700PlusPosition2555,
      kernelN02701PlusPosition2555, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02700PlusFourthP029ExpUpper2558, batchC02700PlusFourthP029Frequency2558,
        batchC02700PlusFourthP029Upper2558]

noncomputable def batchC02700PlusFourthP000Upper2558 : ℝ := 0

theorem batchC02700PlusFourthP000Bound2558 :
    batchC02700PlusFourthCell2558 ⟨0, by omega⟩ ≤ batchC02700PlusFourthP000Upper2558 := by
  norm_num [batchC02700PlusFourthCell2558, batchC02700PlusFourthP000Upper2558, cellNearAbs2538,
    kernelN02700PlusPosition2555, kernelN02701PlusPosition2555, storedWidth]

noncomputable def batchC02700PlusFourthP005Upper2558 : ℝ := 0

theorem batchC02700PlusFourthP005Bound2558 :
    batchC02700PlusFourthCell2558 ⟨5, by omega⟩ ≤ batchC02700PlusFourthP005Upper2558 := by
  norm_num [batchC02700PlusFourthCell2558, batchC02700PlusFourthP005Upper2558, cellNearAbs2538,
    kernelN02700PlusPosition2555, kernelN02701PlusPosition2555, storedWidth]

noncomputable def batchC02700PlusFourthUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02700PlusFourthP000Upper2558
  | 1 => batchC02700PlusFourthP001Upper2558
  | 2 => batchC02700PlusFourthP002Upper2558
  | 3 => batchC02700PlusFourthP003Upper2558
  | 4 => batchC02700PlusFourthP004Upper2558
  | 5 => batchC02700PlusFourthP005Upper2558
  | 6 => batchC02700PlusFourthP006Upper2558
  | 7 => batchC02700PlusFourthP007Upper2558
  | 8 => batchC02700PlusFourthP008Upper2558
  | 9 => batchC02700PlusFourthP009Upper2558
  | 10 => batchC02700PlusFourthP010Upper2558
  | 11 => batchC02700PlusFourthP011Upper2558
  | 12 => batchC02700PlusFourthP012Upper2558
  | 13 => batchC02700PlusFourthP013Upper2558
  | 14 => batchC02700PlusFourthP014Upper2558
  | 15 => batchC02700PlusFourthP015Upper2558
  | 16 => batchC02700PlusFourthP016Upper2558
  | 17 => batchC02700PlusFourthP017Upper2558
  | 18 => batchC02700PlusFourthP018Upper2558
  | 19 => batchC02700PlusFourthP019Upper2558
  | 20 => batchC02700PlusFourthP020Upper2558
  | 21 => batchC02700PlusFourthP021Upper2558
  | 22 => batchC02700PlusFourthP022Upper2558
  | 23 => batchC02700PlusFourthP023Upper2558
  | 24 => batchC02700PlusFourthP024Upper2558
  | 25 => batchC02700PlusFourthP025Upper2558
  | 26 => batchC02700PlusFourthP026Upper2558
  | 27 => batchC02700PlusFourthP027Upper2558
  | 28 => batchC02700PlusFourthP028Upper2558
  | 29 => batchC02700PlusFourthP029Upper2558
  | _ => 0

theorem batchC02700PlusFourthBound2558 (i : Fin 30) :
    batchC02700PlusFourthCell2558 i ≤ batchC02700PlusFourthUpper2558 i := by
  fin_cases i
  · exact batchC02700PlusFourthP000Bound2558
  · exact batchC02700PlusFourthP001Bound2558
  · exact batchC02700PlusFourthP002Bound2558
  · exact batchC02700PlusFourthP003Bound2558
  · exact batchC02700PlusFourthP004Bound2558
  · exact batchC02700PlusFourthP005Bound2558
  · exact batchC02700PlusFourthP006Bound2558
  · exact batchC02700PlusFourthP007Bound2558
  · exact batchC02700PlusFourthP008Bound2558
  · exact batchC02700PlusFourthP009Bound2558
  · exact batchC02700PlusFourthP010Bound2558
  · exact batchC02700PlusFourthP011Bound2558
  · exact batchC02700PlusFourthP012Bound2558
  · exact batchC02700PlusFourthP013Bound2558
  · exact batchC02700PlusFourthP014Bound2558
  · exact batchC02700PlusFourthP015Bound2558
  · exact batchC02700PlusFourthP016Bound2558
  · exact batchC02700PlusFourthP017Bound2558
  · exact batchC02700PlusFourthP018Bound2558
  · exact batchC02700PlusFourthP019Bound2558
  · exact batchC02700PlusFourthP020Bound2558
  · exact batchC02700PlusFourthP021Bound2558
  · exact batchC02700PlusFourthP022Bound2558
  · exact batchC02700PlusFourthP023Bound2558
  · exact batchC02700PlusFourthP024Bound2558
  · exact batchC02700PlusFourthP025Bound2558
  · exact batchC02700PlusFourthP026Bound2558
  · exact batchC02700PlusFourthP027Bound2558
  · exact batchC02700PlusFourthP028Bound2558
  · exact batchC02700PlusFourthP029Bound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP001Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP002Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP003Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP004Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP006Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP007Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP008Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP009Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP010Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP011Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP012Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP013Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP014Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP015Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP016Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP017Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP018Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP019Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP020Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP021Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP022Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP023Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP024Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP025Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP026Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP027Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP028Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP029Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthBound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP000Bound2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusFourthP005Bound2558
