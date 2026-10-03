import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteABoundaryLeft2548
import ConnesWeilRH.Dev.C1RouteABoundaryRight2548

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def edgeFourthCell2550 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 edgeLeftPosition2548 edgeRightPosition2548 < storedWidth i ^ 2 then
    weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 edgeLeftPosition2548 edgeRightPosition2548 / (storedWidth i ^ 2))
      (min (max |edgeLeftPosition2548| |edgeRightPosition2548|) (storedWidth i ^ 2) /
        (storedWidth i ^ 2)) edgeLeftPosition2548 edgeRightPosition2548
  else 0


def edgeFourthP001Input2550 : RatPair2542 := ((((-((340 * 10^40
        + 1125558694715412604882605546165965236561) * 10^40
        + 9325600687173468560131001925406640200979)) : ℚ) /
        ((470 * 10^40
        + 8051084608253227424517128621179049377342) * 10^40
        + 2000184230903991220710833940070400000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP001Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP001Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP001ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP001Frequency2550 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def edgeFourthP001Upper2550 : ℝ := ((387918402585 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP001Exponent2550 : ℝ := (((-((340 * 10^40
        + 1125558694715412604882605546165965236561) * 10^40
        + 9325600687173468560131001925406640200979)) : ℝ) /
        ((1 * 10^40
        + 8390824549250989169627020033676480661630) * 10^40
        + 2429688219651968715705901695078400000000))

theorem edgeFourthP001ExpBound2550 :
    Real.exp edgeFourthP001Exponent2550 ≤ edgeFourthP001ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP001Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP001Input2550]
  have hc : (compactExp2547 edgeFourthP001Input2550 8).1 = edgeFourthP001Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP001Input2550 8).2 : ℝ) = edgeFourthP001Error2550 := by
    have hq : (compactExp2547 edgeFourthP001Input2550 8).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP001Error2550]
  have h := compactExp_error2547 edgeFourthP001Input2550 hz 8
  rw [hc, he] at h
  have ha : (2 : ℂ)^8 * embedPair2542 edgeFourthP001Input2550 =
      (edgeFourthP001Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP001Input2550,
        edgeFourthP001Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP001Exponent2550 : ℂ)) (embedPair2542 edgeFourthP001Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP001Center2550))).trans
  norm_num [edgeFourthP001Error2550, edgeFourthP001ExpUpper2550, pairMagnitude2542,
      edgeFourthP001Center2550]

theorem edgeFourthP001Bound2550 : edgeFourthCell2550 ⟨1, by omega⟩ ≤ edgeFourthP001Upper2550 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      edgeFourthP001Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP001Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP001Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((95826464023198495143285394738511872 : ℝ) /
        104779244925114570282650713456640625) ((19173215621012018044377896260206592 : ℝ) /
        20955848985022914056530142691328125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP001ExpBound2550 using 1; norm_num [edgeFourthP001Exponent2550])
  have hid : edgeFourthCell2550 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((95826464023198495143285394738511872 : ℝ) /
        104779244925114570282650713456640625) ((19173215621012018044377896260206592 : ℝ) /
        20955848985022914056530142691328125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP001ExpUpper2550, edgeFourthP001Frequency2550, edgeFourthP001Upper2550]

def edgeFourthP002Input2550 : RatPair2542 := ((((-((9033 * 10^40
        + 8109252320354666245907324545684805984286) * 10^40
        + 2898018879638657721153554737628069387539)) : ℚ) /
        ((9170 * 10^40
        + 1316778706032230511805590697284698666328) * 10^40
        + 5225687954632429882843335760281600000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP002Center2550 : RatPair2542 := (((606936572380043288435 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP002Error2550 : ℝ := ((57192599555477919 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def edgeFourthP002ExpUpper2550 : ℝ := ((333666909327183776474854918263199 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def edgeFourthP002Frequency2550 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def edgeFourthP002Upper2550 : ℝ := ((1685847560821978649209278511 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def edgeFourthP002Exponent2550 : ℝ := (((-((9033 * 10^40
        + 8109252320354666245907324545684805984286) * 10^40
        + 2898018879638657721153554737628069387539)) : ℝ) /
        ((143 * 10^40
        + 2833074667281753601746962354645073416661) * 10^40
        + 3831651374291131716919427121254400000000))

theorem edgeFourthP002ExpBound2550 :
    Real.exp edgeFourthP002Exponent2550 ≤ edgeFourthP002ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP002Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP002Input2550]
  have hc : (compactExp2547 edgeFourthP002Input2550 6).1 = edgeFourthP002Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP002Input2550 6).2 : ℝ) = edgeFourthP002Error2550 := by
    have hq : (compactExp2547 edgeFourthP002Input2550 6).2 =
        ((57192599555477919 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by cbv
    rw [hq]
    norm_num [edgeFourthP002Error2550]
  have h := compactExp_error2547 edgeFourthP002Input2550 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 edgeFourthP002Input2550 =
      (edgeFourthP002Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP002Input2550,
        edgeFourthP002Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP002Exponent2550 : ℂ)) (embedPair2542 edgeFourthP002Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP002Center2550))).trans
  norm_num [edgeFourthP002Error2550, edgeFourthP002ExpUpper2550, pairMagnitude2542,
      edgeFourthP002Center2550]

theorem edgeFourthP002Bound2550 : edgeFourthCell2550 ⟨2, by omega⟩ ≤ edgeFourthP002Upper2550 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      edgeFourthP002Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP002Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP002Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((383305856092793980573141578954047488 : ℝ) /
        535582378596426958724104076656640625) ((76692862484048072177511585040826368 : ℝ) /
        107116475719285391744820815331328125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP002ExpBound2550 using 1; norm_num [edgeFourthP002Exponent2550])
  have hid : edgeFourthCell2550 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((383305856092793980573141578954047488 : ℝ) /
        535582378596426958724104076656640625) ((76692862484048072177511585040826368 : ℝ) /
        107116475719285391744820815331328125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP002ExpUpper2550, edgeFourthP002Frequency2550, edgeFourthP002Upper2550]

def edgeFourthP003Input2550 : RatPair2542 := ((((-((1204018 * 10^40
        + 3199206753711006565389390034201102437777) * 10^40
        + 7349271424128768512973515705970498543953)) : ℚ) /
        ((1661191 * 10^40
        + 87148974586734181907637641423553326161) * 10^40
        + 2589241144003979669297984877363200000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP003Center2550 : RatPair2542 := (((163354299886446954699714643 : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP003Error2550 : ℝ := ((759335337735088749674751 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def edgeFourthP003ExpUpper2550 : ℝ := ((5747518469515397339270101908132996841727 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def edgeFourthP003Frequency2550 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def edgeFourthP003Upper2550 : ℝ := ((21838323687308956104556534204092651 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def edgeFourthP003Exponent2550 : ℝ := (((-((1204018 * 10^40
        + 3199206753711006565389390034201102437777) * 10^40
        + 7349271424128768512973515705970498543953)) : ℝ) /
        ((25956 * 10^40
        + 1095111702727917721592306838147243020721) * 10^40
        + 2696706892875062182332781013708800000000))

theorem edgeFourthP003ExpBound2550 :
    Real.exp edgeFourthP003Exponent2550 ≤ edgeFourthP003ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP003Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP003Input2550]
  have hc : (compactExp2547 edgeFourthP003Input2550 6).1 = edgeFourthP003Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP003Input2550 6).2 : ℝ) = edgeFourthP003Error2550 := by
    have hq : (compactExp2547 edgeFourthP003Input2550 6).2 =
        ((759335337735088749674751 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by cbv
    rw [hq]
    norm_num [edgeFourthP003Error2550]
  have h := compactExp_error2547 edgeFourthP003Input2550 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 edgeFourthP003Input2550 =
      (edgeFourthP003Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP003Input2550,
        edgeFourthP003Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP003Exponent2550 : ℂ)) (embedPair2542 edgeFourthP003Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP003Center2550))).trans
  norm_num [edgeFourthP003Error2550, edgeFourthP003ExpUpper2550, pairMagnitude2542,
      edgeFourthP003Center2550]

theorem edgeFourthP003Bound2550 : edgeFourthCell2550 ⟨3, by omega⟩ ≤ edgeFourthP003Upper2550 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      edgeFourthP003Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP003Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP003Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) ((1227085799744769154840185360653221888 : ℝ) /
        2132188309583881559457579105517578125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP003ExpBound2550 using 1; norm_num [edgeFourthP003Exponent2550])
  have hid : edgeFourthCell2550 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) ((1227085799744769154840185360653221888 : ℝ) /
        2132188309583881559457579105517578125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP003ExpUpper2550, edgeFourthP003Frequency2550, edgeFourthP003Upper2550]

def edgeFourthP004Input2550 : RatPair2542 := ((((-((21030 * 10^40
        + 4978280417753696551825490501735319367009) * 10^40
        + 9100087780138783714176925758135881887539)) : ℚ) /
        ((33507 * 10^40
        + 1440806512715411278534376263881936497085) * 10^40
        + 1089979081925709882843335760281600000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP004Center2550 : RatPair2542 := (((5243005563983089941503791278595 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP004Error2550 : ℝ := ((345550614926699585689874555 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def edgeFourthP004ExpUpper2550 : ℝ := (((288 * 10^40
        + 2372791046836415411138011701256068001915) : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def edgeFourthP004Frequency2550 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def edgeFourthP004Upper2550 : ℝ := ((24535932828028298201929589790441057037 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP004Exponent2550 : ℝ := (((-((21030 * 10^40
        + 4978280417753696551825490501735319367009) * 10^40
        + 9100087780138783714176925758135881887539)) : ℝ) /
        ((523 * 10^40
        + 5491262601761178301227099629123155257766) * 10^40
        + 9548280923155089216919427121254400000000))

theorem edgeFourthP004ExpBound2550 :
    Real.exp edgeFourthP004Exponent2550 ≤ edgeFourthP004ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP004Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP004Input2550]
  have hc : (compactExp2547 edgeFourthP004Input2550 6).1 = edgeFourthP004Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP004Input2550 6).2 : ℝ) = edgeFourthP004Error2550 := by
    have hq : (compactExp2547 edgeFourthP004Input2550 6).2 =
        ((345550614926699585689874555 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by cbv
    rw [hq]
    norm_num [edgeFourthP004Error2550]
  have h := compactExp_error2547 edgeFourthP004Input2550 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 edgeFourthP004Input2550 =
      (edgeFourthP004Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP004Input2550,
        edgeFourthP004Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP004Exponent2550 : ℂ)) (embedPair2542 edgeFourthP004Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP004Center2550))).trans
  norm_num [edgeFourthP004Error2550, edgeFourthP004ExpUpper2550, pairMagnitude2542,
      edgeFourthP004Center2550]

theorem edgeFourthP004Bound2550 : edgeFourthCell2550 ⟨4, by omega⟩ ≤ edgeFourthP004Upper2550 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      edgeFourthP004Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP004Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP004Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((383305856092793980573141578954047488 : ℝ) /
        811296384146067132209863967375390625) ((76692862484048072177511585040826368 : ℝ) /
        162259276829213426441972793475078125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP004ExpBound2550 using 1; norm_num [edgeFourthP004Exponent2550])
  have hid : edgeFourthCell2550 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((383305856092793980573141578954047488 : ℝ) /
        811296384146067132209863967375390625) ((76692862484048072177511585040826368 : ℝ) /
        162259276829213426441972793475078125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP004ExpUpper2550, edgeFourthP004Frequency2550, edgeFourthP004Upper2550]

def edgeFourthP006Input2550 : RatPair2542 := ((((-43838019295084218252511359948400647) : ℚ) /
        73447401531966028759865753600000000),
    ((0 : ℚ) /
        1))

def edgeFourthP006Center2550 : RatPair2542 := (((483449294895075 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP006Error2550 : ℝ := ((2446198475405 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP006ExpUpper2550 : ℝ := ((1063116242354489166949681805 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP006Frequency2550 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def edgeFourthP006Upper2550 : ℝ := ((7471997262223778628361 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def edgeFourthP006Exponent2550 : ℝ := (((-43838019295084218252511359948400647) : ℝ)
    /
        573807824468484599686451200000000)

theorem edgeFourthP006ExpBound2550 :
    Real.exp edgeFourthP006Exponent2550 ≤ edgeFourthP006ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP006Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP006Input2550]
  have hc : (compactExp2547 edgeFourthP006Input2550 7).1 = edgeFourthP006Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP006Input2550 7).2 : ℝ) = edgeFourthP006Error2550 := by
    have hq : (compactExp2547 edgeFourthP006Input2550 7).2 =
        ((2446198475405 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP006Error2550]
  have h := compactExp_error2547 edgeFourthP006Input2550 hz 7
  rw [hc, he] at h
  have ha : (2 : ℂ)^7 * embedPair2542 edgeFourthP006Input2550 =
      (edgeFourthP006Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP006Input2550,
        edgeFourthP006Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP006Exponent2550 : ℂ)) (embedPair2542 edgeFourthP006Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP006Center2550))).trans
  norm_num [edgeFourthP006Error2550, edgeFourthP006ExpUpper2550, pairMagnitude2542,
      edgeFourthP006Center2550]

theorem edgeFourthP006Bound2550 : edgeFourthCell2550 ⟨6, by omega⟩ ≤ edgeFourthP006Upper2550 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      edgeFourthP006Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP006Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP006Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) ((158531586419 : ℝ) /
        204800000000) ((7929856121 : ℝ) /
        10240000000) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP006ExpBound2550 using 1; norm_num [edgeFourthP006Exponent2550])
  have hid : edgeFourthCell2550 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) ((158531586419 : ℝ) /
        204800000000) ((7929856121 : ℝ) /
        10240000000) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP006ExpUpper2550, edgeFourthP006Frequency2550, edgeFourthP006Upper2550]

def edgeFourthP007Input2550 : RatPair2542 := ((((-((1204018 * 10^40
        + 3199206753711006565389390034201102437777) * 10^40
        + 7349271424128768512973515705970498543953)) : ℚ) /
        ((1661191 * 10^40
        + 87148974586734181907637641423553326161) * 10^40
        + 2589241144003979669297984877363200000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP007Center2550 : RatPair2542 := (((163354299886446954699714643 : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP007Error2550 : ℝ := ((759335337735088749674751 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def edgeFourthP007ExpUpper2550 : ℝ := ((5747518469515397339270101908132996841727 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def edgeFourthP007Frequency2550 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def edgeFourthP007Upper2550 : ℝ := ((572910784089856726997890950156811 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP007Exponent2550 : ℝ := (((-((1204018 * 10^40
        + 3199206753711006565389390034201102437777) * 10^40
        + 7349271424128768512973515705970498543953)) : ℝ) /
        ((25956 * 10^40
        + 1095111702727917721592306838147243020721) * 10^40
        + 2696706892875062182332781013708800000000))

theorem edgeFourthP007ExpBound2550 :
    Real.exp edgeFourthP007Exponent2550 ≤ edgeFourthP007ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP007Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP007Input2550]
  have hc : (compactExp2547 edgeFourthP007Input2550 6).1 = edgeFourthP007Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP007Input2550 6).2 : ℝ) = edgeFourthP007Error2550 := by
    have hq : (compactExp2547 edgeFourthP007Input2550 6).2 =
        ((759335337735088749674751 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by cbv
    rw [hq]
    norm_num [edgeFourthP007Error2550]
  have h := compactExp_error2547 edgeFourthP007Input2550 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 edgeFourthP007Input2550 =
      (edgeFourthP007Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP007Input2550,
        edgeFourthP007Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP007Exponent2550 : ℂ)) (embedPair2542 edgeFourthP007Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP007Center2550))).trans
  norm_num [edgeFourthP007Error2550, edgeFourthP007ExpUpper2550, pairMagnitude2542,
      edgeFourthP007Center2550]

theorem edgeFourthP007Bound2550 : edgeFourthCell2550 ⟨7, by omega⟩ ≤ edgeFourthP007Upper2550 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      edgeFourthP007Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP007Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP007Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) ((1227085799744769154840185360653221888 : ℝ) /
        2132188309583881559457579105517578125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP007ExpBound2550 using 1; norm_num [edgeFourthP007Exponent2550])
  have hid : edgeFourthCell2550 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) ((1227085799744769154840185360653221888 : ℝ) /
        2132188309583881559457579105517578125) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP007ExpUpper2550, edgeFourthP007Frequency2550, edgeFourthP007Upper2550]

def edgeFourthP008Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP008Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP008Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP008ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP008Frequency2550 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def edgeFourthP008Upper2550 : ℝ := ((1513212029608543513716512408467 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP008Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP008ExpBound2550 :
    Real.exp edgeFourthP008Exponent2550 ≤ edgeFourthP008ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP008Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP008Input2550]
  have hc : (compactExp2547 edgeFourthP008Input2550 16).1 = edgeFourthP008Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP008Input2550 16).2 : ℝ) = edgeFourthP008Error2550 := by
    have hq : (compactExp2547 edgeFourthP008Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP008Error2550]
  have h := compactExp_error2547 edgeFourthP008Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP008Input2550 =
      (edgeFourthP008Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP008Input2550,
        edgeFourthP008Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP008Exponent2550 : ℂ)) (embedPair2542 edgeFourthP008Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP008Center2550))).trans
  norm_num [edgeFourthP008Error2550, edgeFourthP008ExpUpper2550, pairMagnitude2542,
      edgeFourthP008Center2550]

theorem edgeFourthP008Bound2550 : edgeFourthCell2550 ⟨8, by omega⟩ ≤ edgeFourthP008Upper2550 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      edgeFourthP008Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP008Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP008Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP008ExpBound2550 using 1; norm_num [edgeFourthP008Exponent2550])
  have hid : edgeFourthCell2550 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP008ExpUpper2550, edgeFourthP008Frequency2550, edgeFourthP008Upper2550]

def edgeFourthP009Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP009Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP009Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP009ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP009Frequency2550 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def edgeFourthP009Upper2550 : ℝ := ((756606702514067810266035928231 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def edgeFourthP009Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP009ExpBound2550 :
    Real.exp edgeFourthP009Exponent2550 ≤ edgeFourthP009ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP009Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP009Input2550]
  have hc : (compactExp2547 edgeFourthP009Input2550 16).1 = edgeFourthP009Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP009Input2550 16).2 : ℝ) = edgeFourthP009Error2550 := by
    have hq : (compactExp2547 edgeFourthP009Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP009Error2550]
  have h := compactExp_error2547 edgeFourthP009Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP009Input2550 =
      (edgeFourthP009Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP009Input2550,
        edgeFourthP009Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP009Exponent2550 : ℂ)) (embedPair2542 edgeFourthP009Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP009Center2550))).trans
  norm_num [edgeFourthP009Error2550, edgeFourthP009ExpUpper2550, pairMagnitude2542,
      edgeFourthP009Center2550]

theorem edgeFourthP009Bound2550 : edgeFourthCell2550 ⟨9, by omega⟩ ≤ edgeFourthP009Upper2550 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      edgeFourthP009Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP009Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP009Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP009ExpBound2550 using 1; norm_num [edgeFourthP009Exponent2550])
  have hid : edgeFourthCell2550 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP009ExpUpper2550, edgeFourthP009Frequency2550, edgeFourthP009Upper2550]

def edgeFourthP010Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP010Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP010Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP010ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP010Frequency2550 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def edgeFourthP010Upper2550 : ℝ := ((1513214201754394692916962659401 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP010Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP010ExpBound2550 :
    Real.exp edgeFourthP010Exponent2550 ≤ edgeFourthP010ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP010Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP010Input2550]
  have hc : (compactExp2547 edgeFourthP010Input2550 16).1 = edgeFourthP010Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP010Input2550 16).2 : ℝ) = edgeFourthP010Error2550 := by
    have hq : (compactExp2547 edgeFourthP010Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP010Error2550]
  have h := compactExp_error2547 edgeFourthP010Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP010Input2550 =
      (edgeFourthP010Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP010Input2550,
        edgeFourthP010Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP010Exponent2550 : ℂ)) (embedPair2542 edgeFourthP010Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP010Center2550))).trans
  norm_num [edgeFourthP010Error2550, edgeFourthP010ExpUpper2550, pairMagnitude2542,
      edgeFourthP010Center2550]

theorem edgeFourthP010Bound2550 : edgeFourthCell2550 ⟨10, by omega⟩ ≤ edgeFourthP010Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      edgeFourthP010Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP010Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP010Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP010ExpBound2550 using 1; norm_num [edgeFourthP010Exponent2550])
  have hid : edgeFourthCell2550 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP010ExpUpper2550, edgeFourthP010Frequency2550, edgeFourthP010Upper2550]

def edgeFourthP011Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP011Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP011Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP011ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP011Frequency2550 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def edgeFourthP011Upper2550 : ℝ := ((189151841623269213146709186821 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def edgeFourthP011Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP011ExpBound2550 :
    Real.exp edgeFourthP011Exponent2550 ≤ edgeFourthP011ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP011Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP011Input2550]
  have hc : (compactExp2547 edgeFourthP011Input2550 16).1 = edgeFourthP011Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP011Input2550 16).2 : ℝ) = edgeFourthP011Error2550 := by
    have hq : (compactExp2547 edgeFourthP011Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP011Error2550]
  have h := compactExp_error2547 edgeFourthP011Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP011Input2550 =
      (edgeFourthP011Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP011Input2550,
        edgeFourthP011Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP011Exponent2550 : ℂ)) (embedPair2542 edgeFourthP011Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP011Center2550))).trans
  norm_num [edgeFourthP011Error2550, edgeFourthP011ExpUpper2550, pairMagnitude2542,
      edgeFourthP011Center2550]

theorem edgeFourthP011Bound2550 : edgeFourthCell2550 ⟨11, by omega⟩ ≤ edgeFourthP011Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      edgeFourthP011Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP011Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP011Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP011ExpBound2550 using 1; norm_num [edgeFourthP011Exponent2550])
  have hid : edgeFourthCell2550 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP011ExpUpper2550, edgeFourthP011Frequency2550, edgeFourthP011Upper2550]

def edgeFourthP012Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP012Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP012Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP012ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP012Frequency2550 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def edgeFourthP012Upper2550 : ℝ := ((1513215283230071596715993367975 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP012Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP012ExpBound2550 :
    Real.exp edgeFourthP012Exponent2550 ≤ edgeFourthP012ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP012Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP012Input2550]
  have hc : (compactExp2547 edgeFourthP012Input2550 16).1 = edgeFourthP012Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP012Input2550 16).2 : ℝ) = edgeFourthP012Error2550 := by
    have hq : (compactExp2547 edgeFourthP012Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP012Error2550]
  have h := compactExp_error2547 edgeFourthP012Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP012Input2550 =
      (edgeFourthP012Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP012Input2550,
        edgeFourthP012Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP012Exponent2550 : ℂ)) (embedPair2542 edgeFourthP012Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP012Center2550))).trans
  norm_num [edgeFourthP012Error2550, edgeFourthP012ExpUpper2550, pairMagnitude2542,
      edgeFourthP012Center2550]

theorem edgeFourthP012Bound2550 : edgeFourthCell2550 ⟨12, by omega⟩ ≤ edgeFourthP012Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      edgeFourthP012Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP012Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP012Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP012ExpBound2550 using 1; norm_num [edgeFourthP012Exponent2550])
  have hid : edgeFourthCell2550 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP012ExpUpper2550, edgeFourthP012Frequency2550, edgeFourthP012Upper2550]

def edgeFourthP013Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP013Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP013Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP013ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP013Frequency2550 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def edgeFourthP013Upper2550 : ℝ := ((1513215784671438379443123399037 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP013Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP013ExpBound2550 :
    Real.exp edgeFourthP013Exponent2550 ≤ edgeFourthP013ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP013Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP013Input2550]
  have hc : (compactExp2547 edgeFourthP013Input2550 16).1 = edgeFourthP013Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP013Input2550 16).2 : ℝ) = edgeFourthP013Error2550 := by
    have hq : (compactExp2547 edgeFourthP013Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP013Error2550]
  have h := compactExp_error2547 edgeFourthP013Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP013Input2550 =
      (edgeFourthP013Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP013Input2550,
        edgeFourthP013Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP013Exponent2550 : ℂ)) (embedPair2542 edgeFourthP013Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP013Center2550))).trans
  norm_num [edgeFourthP013Error2550, edgeFourthP013ExpUpper2550, pairMagnitude2542,
      edgeFourthP013Center2550]

theorem edgeFourthP013Bound2550 : edgeFourthCell2550 ⟨13, by omega⟩ ≤ edgeFourthP013Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      edgeFourthP013Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP013Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP013Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP013ExpBound2550 using 1; norm_num [edgeFourthP013Exponent2550])
  have hid : edgeFourthCell2550 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP013ExpUpper2550, edgeFourthP013Frequency2550, edgeFourthP013Upper2550]

def edgeFourthP014Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP014Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP014Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP014ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP014Frequency2550 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def edgeFourthP014Upper2550 : ℝ := ((378304178453336207927296424261 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def edgeFourthP014Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP014ExpBound2550 :
    Real.exp edgeFourthP014Exponent2550 ≤ edgeFourthP014ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP014Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP014Input2550]
  have hc : (compactExp2547 edgeFourthP014Input2550 16).1 = edgeFourthP014Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP014Input2550 16).2 : ℝ) = edgeFourthP014Error2550 := by
    have hq : (compactExp2547 edgeFourthP014Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP014Error2550]
  have h := compactExp_error2547 edgeFourthP014Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP014Input2550 =
      (edgeFourthP014Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP014Input2550,
        edgeFourthP014Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP014Exponent2550 : ℂ)) (embedPair2542 edgeFourthP014Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP014Center2550))).trans
  norm_num [edgeFourthP014Error2550, edgeFourthP014ExpUpper2550, pairMagnitude2542,
      edgeFourthP014Center2550]

theorem edgeFourthP014Bound2550 : edgeFourthCell2550 ⟨14, by omega⟩ ≤ edgeFourthP014Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      edgeFourthP014Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP014Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP014Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP014ExpBound2550 using 1; norm_num [edgeFourthP014Exponent2550])
  have hid : edgeFourthCell2550 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP014ExpUpper2550, edgeFourthP014Frequency2550, edgeFourthP014Upper2550]

def edgeFourthP015Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP015Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP015Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP015ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP015Frequency2550 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def edgeFourthP015Upper2550 : ℝ := ((94576086222503903653034159775 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def edgeFourthP015Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP015ExpBound2550 :
    Real.exp edgeFourthP015Exponent2550 ≤ edgeFourthP015ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP015Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP015Input2550]
  have hc : (compactExp2547 edgeFourthP015Input2550 16).1 = edgeFourthP015Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP015Input2550 16).2 : ℝ) = edgeFourthP015Error2550 := by
    have hq : (compactExp2547 edgeFourthP015Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP015Error2550]
  have h := compactExp_error2547 edgeFourthP015Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP015Input2550 =
      (edgeFourthP015Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP015Input2550,
        edgeFourthP015Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP015Exponent2550 : ℂ)) (embedPair2542 edgeFourthP015Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP015Center2550))).trans
  norm_num [edgeFourthP015Error2550, edgeFourthP015ExpUpper2550, pairMagnitude2542,
      edgeFourthP015Center2550]

theorem edgeFourthP015Bound2550 : edgeFourthCell2550 ⟨15, by omega⟩ ≤ edgeFourthP015Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      edgeFourthP015Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP015Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP015Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP015ExpBound2550 using 1; norm_num [edgeFourthP015Exponent2550])
  have hid : edgeFourthCell2550 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP015ExpUpper2550, edgeFourthP015Frequency2550, edgeFourthP015Upper2550]

def edgeFourthP016Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP016Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP016Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP016ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP016Frequency2550 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def edgeFourthP016Upper2550 : ℝ := ((756608930342974629604475951035 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def edgeFourthP016Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP016ExpBound2550 :
    Real.exp edgeFourthP016Exponent2550 ≤ edgeFourthP016ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP016Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP016Input2550]
  have hc : (compactExp2547 edgeFourthP016Input2550 16).1 = edgeFourthP016Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP016Input2550 16).2 : ℝ) = edgeFourthP016Error2550 := by
    have hq : (compactExp2547 edgeFourthP016Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP016Error2550]
  have h := compactExp_error2547 edgeFourthP016Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP016Input2550 =
      (edgeFourthP016Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP016Input2550,
        edgeFourthP016Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP016Exponent2550 : ℂ)) (embedPair2542 edgeFourthP016Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP016Center2550))).trans
  norm_num [edgeFourthP016Error2550, edgeFourthP016ExpUpper2550, pairMagnitude2542,
      edgeFourthP016Center2550]

theorem edgeFourthP016Bound2550 : edgeFourthCell2550 ⟨16, by omega⟩ ≤ edgeFourthP016Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      edgeFourthP016Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP016Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP016Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP016ExpBound2550 using 1; norm_num [edgeFourthP016Exponent2550])
  have hid : edgeFourthCell2550 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP016ExpUpper2550, edgeFourthP016Frequency2550, edgeFourthP016Upper2550]

def edgeFourthP017Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP017Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP017Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP017ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP017Frequency2550 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def edgeFourthP017Upper2550 : ℝ := ((1513218795252961646618336077019 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP017Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP017ExpBound2550 :
    Real.exp edgeFourthP017Exponent2550 ≤ edgeFourthP017ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP017Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP017Input2550]
  have hc : (compactExp2547 edgeFourthP017Input2550 16).1 = edgeFourthP017Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP017Input2550 16).2 : ℝ) = edgeFourthP017Error2550 := by
    have hq : (compactExp2547 edgeFourthP017Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP017Error2550]
  have h := compactExp_error2547 edgeFourthP017Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP017Input2550 =
      (edgeFourthP017Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP017Input2550,
        edgeFourthP017Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP017Exponent2550 : ℂ)) (embedPair2542 edgeFourthP017Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP017Center2550))).trans
  norm_num [edgeFourthP017Error2550, edgeFourthP017ExpUpper2550, pairMagnitude2542,
      edgeFourthP017Center2550]

theorem edgeFourthP017Bound2550 : edgeFourthCell2550 ⟨17, by omega⟩ ≤ edgeFourthP017Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      edgeFourthP017Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP017Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP017Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP017ExpBound2550 using 1; norm_num [edgeFourthP017Exponent2550])
  have hid : edgeFourthCell2550 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP017ExpUpper2550, edgeFourthP017Frequency2550, edgeFourthP017Upper2550]

def edgeFourthP018Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP018Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP018Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP018ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP018Frequency2550 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def edgeFourthP018Upper2550 : ℝ := ((1513219148595726417363633881407 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP018Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP018ExpBound2550 :
    Real.exp edgeFourthP018Exponent2550 ≤ edgeFourthP018ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP018Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP018Input2550]
  have hc : (compactExp2547 edgeFourthP018Input2550 16).1 = edgeFourthP018Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP018Input2550 16).2 : ℝ) = edgeFourthP018Error2550 := by
    have hq : (compactExp2547 edgeFourthP018Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP018Error2550]
  have h := compactExp_error2547 edgeFourthP018Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP018Input2550 =
      (edgeFourthP018Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP018Input2550,
        edgeFourthP018Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP018Exponent2550 : ℂ)) (embedPair2542 edgeFourthP018Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP018Center2550))).trans
  norm_num [edgeFourthP018Error2550, edgeFourthP018ExpUpper2550, pairMagnitude2542,
      edgeFourthP018Center2550]

theorem edgeFourthP018Bound2550 : edgeFourthCell2550 ⟨18, by omega⟩ ≤ edgeFourthP018Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      edgeFourthP018Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP018Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP018Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP018ExpBound2550 using 1; norm_num [edgeFourthP018Exponent2550])
  have hid : edgeFourthCell2550 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP018ExpUpper2550, edgeFourthP018Frequency2550, edgeFourthP018Upper2550]

def edgeFourthP019Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP019Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP019Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP019ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP019Frequency2550 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def edgeFourthP019Upper2550 : ℝ := ((1513219787185555825140071648211 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP019Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP019ExpBound2550 :
    Real.exp edgeFourthP019Exponent2550 ≤ edgeFourthP019ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP019Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP019Input2550]
  have hc : (compactExp2547 edgeFourthP019Input2550 16).1 = edgeFourthP019Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP019Input2550 16).2 : ℝ) = edgeFourthP019Error2550 := by
    have hq : (compactExp2547 edgeFourthP019Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP019Error2550]
  have h := compactExp_error2547 edgeFourthP019Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP019Input2550 =
      (edgeFourthP019Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP019Input2550,
        edgeFourthP019Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP019Exponent2550 : ℂ)) (embedPair2542 edgeFourthP019Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP019Center2550))).trans
  norm_num [edgeFourthP019Error2550, edgeFourthP019ExpUpper2550, pairMagnitude2542,
      edgeFourthP019Center2550]

theorem edgeFourthP019Bound2550 : edgeFourthCell2550 ⟨19, by omega⟩ ≤ edgeFourthP019Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      edgeFourthP019Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP019Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP019Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP019ExpBound2550 using 1; norm_num [edgeFourthP019Exponent2550])
  have hid : edgeFourthCell2550 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP019ExpUpper2550, edgeFourthP019Frequency2550, edgeFourthP019Upper2550]

def edgeFourthP020Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP020Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP020Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP020ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP020Frequency2550 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def edgeFourthP020Upper2550 : ℝ := ((1513220481605061174870213665839 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP020Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP020ExpBound2550 :
    Real.exp edgeFourthP020Exponent2550 ≤ edgeFourthP020ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP020Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP020Input2550]
  have hc : (compactExp2547 edgeFourthP020Input2550 16).1 = edgeFourthP020Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP020Input2550 16).2 : ℝ) = edgeFourthP020Error2550 := by
    have hq : (compactExp2547 edgeFourthP020Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP020Error2550]
  have h := compactExp_error2547 edgeFourthP020Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP020Input2550 =
      (edgeFourthP020Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP020Input2550,
        edgeFourthP020Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP020Exponent2550 : ℂ)) (embedPair2542 edgeFourthP020Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP020Center2550))).trans
  norm_num [edgeFourthP020Error2550, edgeFourthP020ExpUpper2550, pairMagnitude2542,
      edgeFourthP020Center2550]

theorem edgeFourthP020Bound2550 : edgeFourthCell2550 ⟨20, by omega⟩ ≤ edgeFourthP020Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      edgeFourthP020Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP020Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP020Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP020ExpBound2550 using 1; norm_num [edgeFourthP020Exponent2550])
  have hid : edgeFourthCell2550 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP020ExpUpper2550, edgeFourthP020Frequency2550, edgeFourthP020Upper2550]

def edgeFourthP021Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP021Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP021Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP021ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP021Frequency2550 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def edgeFourthP021Upper2550 : ℝ := ((1513221061128071202416242363039 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP021Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP021ExpBound2550 :
    Real.exp edgeFourthP021Exponent2550 ≤ edgeFourthP021ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP021Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP021Input2550]
  have hc : (compactExp2547 edgeFourthP021Input2550 16).1 = edgeFourthP021Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP021Input2550 16).2 : ℝ) = edgeFourthP021Error2550 := by
    have hq : (compactExp2547 edgeFourthP021Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP021Error2550]
  have h := compactExp_error2547 edgeFourthP021Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP021Input2550 =
      (edgeFourthP021Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP021Input2550,
        edgeFourthP021Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP021Exponent2550 : ℂ)) (embedPair2542 edgeFourthP021Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP021Center2550))).trans
  norm_num [edgeFourthP021Error2550, edgeFourthP021ExpUpper2550, pairMagnitude2542,
      edgeFourthP021Center2550]

theorem edgeFourthP021Bound2550 : edgeFourthCell2550 ⟨21, by omega⟩ ≤ edgeFourthP021Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      edgeFourthP021Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP021Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP021Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP021ExpBound2550 using 1; norm_num [edgeFourthP021Exponent2550])
  have hid : edgeFourthCell2550 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP021ExpUpper2550, edgeFourthP021Frequency2550, edgeFourthP021Upper2550]

def edgeFourthP022Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP022Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP022Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP022ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP022Frequency2550 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def edgeFourthP022Upper2550 : ℝ := ((1513221357750181715440148886747 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP022Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP022ExpBound2550 :
    Real.exp edgeFourthP022Exponent2550 ≤ edgeFourthP022ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP022Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP022Input2550]
  have hc : (compactExp2547 edgeFourthP022Input2550 16).1 = edgeFourthP022Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP022Input2550 16).2 : ℝ) = edgeFourthP022Error2550 := by
    have hq : (compactExp2547 edgeFourthP022Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP022Error2550]
  have h := compactExp_error2547 edgeFourthP022Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP022Input2550 =
      (edgeFourthP022Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP022Input2550,
        edgeFourthP022Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP022Exponent2550 : ℂ)) (embedPair2542 edgeFourthP022Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP022Center2550))).trans
  norm_num [edgeFourthP022Error2550, edgeFourthP022ExpUpper2550, pairMagnitude2542,
      edgeFourthP022Center2550]

theorem edgeFourthP022Bound2550 : edgeFourthCell2550 ⟨22, by omega⟩ ≤ edgeFourthP022Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      edgeFourthP022Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP022Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP022Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP022ExpBound2550 using 1; norm_num [edgeFourthP022Exponent2550])
  have hid : edgeFourthCell2550 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP022ExpUpper2550, edgeFourthP022Frequency2550, edgeFourthP022Upper2550]

def edgeFourthP023Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP023Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP023Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP023ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP023Frequency2550 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def edgeFourthP023Upper2550 : ℝ := ((1513222212969713444427698005981 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP023Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP023ExpBound2550 :
    Real.exp edgeFourthP023Exponent2550 ≤ edgeFourthP023ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP023Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP023Input2550]
  have hc : (compactExp2547 edgeFourthP023Input2550 16).1 = edgeFourthP023Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP023Input2550 16).2 : ℝ) = edgeFourthP023Error2550 := by
    have hq : (compactExp2547 edgeFourthP023Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP023Error2550]
  have h := compactExp_error2547 edgeFourthP023Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP023Input2550 =
      (edgeFourthP023Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP023Input2550,
        edgeFourthP023Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP023Exponent2550 : ℂ)) (embedPair2542 edgeFourthP023Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP023Center2550))).trans
  norm_num [edgeFourthP023Error2550, edgeFourthP023ExpUpper2550, pairMagnitude2542,
      edgeFourthP023Center2550]

theorem edgeFourthP023Bound2550 : edgeFourthCell2550 ⟨23, by omega⟩ ≤ edgeFourthP023Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      edgeFourthP023Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP023Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP023Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP023ExpBound2550 using 1; norm_num [edgeFourthP023Exponent2550])
  have hid : edgeFourthCell2550 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP023ExpUpper2550, edgeFourthP023Frequency2550, edgeFourthP023Upper2550]

def edgeFourthP024Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP024Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP024Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP024ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP024Frequency2550 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def edgeFourthP024Upper2550 : ℝ := ((1513222605995255298282635227107 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP024Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP024ExpBound2550 :
    Real.exp edgeFourthP024Exponent2550 ≤ edgeFourthP024ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP024Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP024Input2550]
  have hc : (compactExp2547 edgeFourthP024Input2550 16).1 = edgeFourthP024Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP024Input2550 16).2 : ℝ) = edgeFourthP024Error2550 := by
    have hq : (compactExp2547 edgeFourthP024Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP024Error2550]
  have h := compactExp_error2547 edgeFourthP024Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP024Input2550 =
      (edgeFourthP024Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP024Input2550,
        edgeFourthP024Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP024Exponent2550 : ℂ)) (embedPair2542 edgeFourthP024Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP024Center2550))).trans
  norm_num [edgeFourthP024Error2550, edgeFourthP024ExpUpper2550, pairMagnitude2542,
      edgeFourthP024Center2550]

theorem edgeFourthP024Bound2550 : edgeFourthCell2550 ⟨24, by omega⟩ ≤ edgeFourthP024Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      edgeFourthP024Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP024Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP024Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP024ExpBound2550 using 1; norm_num [edgeFourthP024Exponent2550])
  have hid : edgeFourthCell2550 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP024ExpUpper2550, edgeFourthP024Frequency2550, edgeFourthP024Upper2550]

def edgeFourthP025Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP025Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP025Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP025ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP025Frequency2550 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def edgeFourthP025Upper2550 : ℝ := ((1513223098778174306315115326937 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP025Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP025ExpBound2550 :
    Real.exp edgeFourthP025Exponent2550 ≤ edgeFourthP025ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP025Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP025Input2550]
  have hc : (compactExp2547 edgeFourthP025Input2550 16).1 = edgeFourthP025Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP025Input2550 16).2 : ℝ) = edgeFourthP025Error2550 := by
    have hq : (compactExp2547 edgeFourthP025Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP025Error2550]
  have h := compactExp_error2547 edgeFourthP025Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP025Input2550 =
      (edgeFourthP025Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP025Input2550,
        edgeFourthP025Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP025Exponent2550 : ℂ)) (embedPair2542 edgeFourthP025Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP025Center2550))).trans
  norm_num [edgeFourthP025Error2550, edgeFourthP025ExpUpper2550, pairMagnitude2542,
      edgeFourthP025Center2550]

theorem edgeFourthP025Bound2550 : edgeFourthCell2550 ⟨25, by omega⟩ ≤ edgeFourthP025Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      edgeFourthP025Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP025Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP025Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP025ExpBound2550 using 1; norm_num [edgeFourthP025Exponent2550])
  have hid : edgeFourthCell2550 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP025ExpUpper2550, edgeFourthP025Frequency2550, edgeFourthP025Upper2550]

def edgeFourthP026Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP026Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP026Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP026ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP026Frequency2550 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def edgeFourthP026Upper2550 : ℝ := ((94576475148959604957330419529 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def edgeFourthP026Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP026ExpBound2550 :
    Real.exp edgeFourthP026Exponent2550 ≤ edgeFourthP026ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP026Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP026Input2550]
  have hc : (compactExp2547 edgeFourthP026Input2550 16).1 = edgeFourthP026Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP026Input2550 16).2 : ℝ) = edgeFourthP026Error2550 := by
    have hq : (compactExp2547 edgeFourthP026Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP026Error2550]
  have h := compactExp_error2547 edgeFourthP026Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP026Input2550 =
      (edgeFourthP026Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP026Input2550,
        edgeFourthP026Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP026Exponent2550 : ℂ)) (embedPair2542 edgeFourthP026Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP026Center2550))).trans
  norm_num [edgeFourthP026Error2550, edgeFourthP026ExpUpper2550, pairMagnitude2542,
      edgeFourthP026Center2550]

theorem edgeFourthP026Bound2550 : edgeFourthCell2550 ⟨26, by omega⟩ ≤ edgeFourthP026Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      edgeFourthP026Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP026Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP026Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP026ExpBound2550 using 1; norm_num [edgeFourthP026Exponent2550])
  have hid : edgeFourthCell2550 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP026ExpUpper2550, edgeFourthP026Frequency2550, edgeFourthP026Upper2550]

def edgeFourthP027Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP027Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP027Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP027ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP027Frequency2550 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def edgeFourthP027Upper2550 : ℝ := ((756612164551870758986594776787 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def edgeFourthP027Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP027ExpBound2550 :
    Real.exp edgeFourthP027Exponent2550 ≤ edgeFourthP027ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP027Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP027Input2550]
  have hc : (compactExp2547 edgeFourthP027Input2550 16).1 = edgeFourthP027Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP027Input2550 16).2 : ℝ) = edgeFourthP027Error2550 := by
    have hq : (compactExp2547 edgeFourthP027Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP027Error2550]
  have h := compactExp_error2547 edgeFourthP027Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP027Input2550 =
      (edgeFourthP027Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP027Input2550,
        edgeFourthP027Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP027Exponent2550 : ℂ)) (embedPair2542 edgeFourthP027Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP027Center2550))).trans
  norm_num [edgeFourthP027Error2550, edgeFourthP027ExpUpper2550, pairMagnitude2542,
      edgeFourthP027Center2550]

theorem edgeFourthP027Bound2550 : edgeFourthCell2550 ⟨27, by omega⟩ ≤ edgeFourthP027Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      edgeFourthP027Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP027Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP027Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP027ExpBound2550 using 1; norm_num [edgeFourthP027Exponent2550])
  have hid : edgeFourthCell2550 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP027ExpUpper2550, edgeFourthP027Frequency2550, edgeFourthP027Upper2550]

def edgeFourthP028Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP028Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP028Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP028ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP028Frequency2550 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def edgeFourthP028Upper2550 : ℝ := ((1513224616822848179541214867455 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def edgeFourthP028Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP028ExpBound2550 :
    Real.exp edgeFourthP028Exponent2550 ≤ edgeFourthP028ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP028Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP028Input2550]
  have hc : (compactExp2547 edgeFourthP028Input2550 16).1 = edgeFourthP028Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP028Input2550 16).2 : ℝ) = edgeFourthP028Error2550 := by
    have hq : (compactExp2547 edgeFourthP028Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP028Error2550]
  have h := compactExp_error2547 edgeFourthP028Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP028Input2550 =
      (edgeFourthP028Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP028Input2550,
        edgeFourthP028Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP028Exponent2550 : ℂ)) (embedPair2542 edgeFourthP028Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP028Center2550))).trans
  norm_num [edgeFourthP028Error2550, edgeFourthP028ExpUpper2550, pairMagnitude2542,
      edgeFourthP028Center2550]

theorem edgeFourthP028Bound2550 : edgeFourthCell2550 ⟨28, by omega⟩ ≤ edgeFourthP028Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      edgeFourthP028Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP028Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP028Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP028ExpBound2550 using 1; norm_num [edgeFourthP028Exponent2550])
  have hid : edgeFourthCell2550 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP028ExpUpper2550, edgeFourthP028Frequency2550, edgeFourthP028Upper2550]

def edgeFourthP029Input2550 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((0 : ℚ) /
        1))

def edgeFourthP029Center2550 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeFourthP029Error2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP029ExpUpper2550 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def edgeFourthP029Frequency2550 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def edgeFourthP029Upper2550 : ℝ := ((756612527428611981465617900939 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def edgeFourthP029Exponent2550 : ℝ := (((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℝ) /
        ((10 * 10^40
        + 6164036081739590261340334919124616776399) * 10^40
        + 8088423680617851432332781013708800000000))

theorem edgeFourthP029ExpBound2550 :
    Real.exp edgeFourthP029Exponent2550 ≤ edgeFourthP029ExpUpper2550 := by
  have hz : ‖embedPair2542 edgeFourthP029Input2550‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, edgeFourthP029Input2550]
  have hc : (compactExp2547 edgeFourthP029Input2550 16).1 = edgeFourthP029Center2550 := by cbv
  have he : ((compactExp2547 edgeFourthP029Input2550 16).2 : ℝ) = edgeFourthP029Error2550 := by
    have hq : (compactExp2547 edgeFourthP029Input2550 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [edgeFourthP029Error2550]
  have h := compactExp_error2547 edgeFourthP029Input2550 hz 16
  rw [hc, he] at h
  have ha : (2 : ℂ)^16 * embedPair2542 edgeFourthP029Input2550 =
      (edgeFourthP029Exponent2550 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, edgeFourthP029Input2550,
        edgeFourthP029Exponent2550,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (edgeFourthP029Exponent2550 : ℂ)) (embedPair2542 edgeFourthP029Center2550) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 edgeFourthP029Center2550))).trans
  norm_num [edgeFourthP029Error2550, edgeFourthP029ExpUpper2550, pairMagnitude2542,
      edgeFourthP029Center2550]

theorem edgeFourthP029Bound2550 : edgeFourthCell2550 ⟨29, by omega⟩ ≤ edgeFourthP029Upper2550 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      edgeFourthP029Frequency2550 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [edgeFourthP029Frequency2550])
    norm_num [weightedLambda2537, nodeModulation2541, edgeFourthP029Frequency2550,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert edgeFourthP029ExpBound2550 using 1; norm_num [edgeFourthP029Exponent2550])
  have hid : edgeFourthCell2550 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (1 : ℝ) (((-7929856121) : ℝ) /
        2560000000) (((-158531586419) : ℝ) /
        51200000000) := by
    norm_num [edgeFourthCell2550, cellNearAbs2538, edgeLeftPosition2548,
      edgeRightPosition2548, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    edgeFourthP029ExpUpper2550, edgeFourthP029Frequency2550, edgeFourthP029Upper2550]

noncomputable def edgeFourthP000Upper2550 : ℝ := 0

theorem edgeFourthP000Bound2550 :
    edgeFourthCell2550 ⟨0, by omega⟩ ≤ edgeFourthP000Upper2550 := by
  norm_num [edgeFourthCell2550, edgeFourthP000Upper2550, cellNearAbs2538,
    edgeLeftPosition2548, edgeRightPosition2548, storedWidth]

noncomputable def edgeFourthP005Upper2550 : ℝ := 0

theorem edgeFourthP005Bound2550 :
    edgeFourthCell2550 ⟨5, by omega⟩ ≤ edgeFourthP005Upper2550 := by
  norm_num [edgeFourthCell2550, edgeFourthP005Upper2550, cellNearAbs2538,
    edgeLeftPosition2548, edgeRightPosition2548, storedWidth]

noncomputable def edgeFourthUpper2550 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => edgeFourthP000Upper2550
  | 1 => edgeFourthP001Upper2550
  | 2 => edgeFourthP002Upper2550
  | 3 => edgeFourthP003Upper2550
  | 4 => edgeFourthP004Upper2550
  | 5 => edgeFourthP005Upper2550
  | 6 => edgeFourthP006Upper2550
  | 7 => edgeFourthP007Upper2550
  | 8 => edgeFourthP008Upper2550
  | 9 => edgeFourthP009Upper2550
  | 10 => edgeFourthP010Upper2550
  | 11 => edgeFourthP011Upper2550
  | 12 => edgeFourthP012Upper2550
  | 13 => edgeFourthP013Upper2550
  | 14 => edgeFourthP014Upper2550
  | 15 => edgeFourthP015Upper2550
  | 16 => edgeFourthP016Upper2550
  | 17 => edgeFourthP017Upper2550
  | 18 => edgeFourthP018Upper2550
  | 19 => edgeFourthP019Upper2550
  | 20 => edgeFourthP020Upper2550
  | 21 => edgeFourthP021Upper2550
  | 22 => edgeFourthP022Upper2550
  | 23 => edgeFourthP023Upper2550
  | 24 => edgeFourthP024Upper2550
  | 25 => edgeFourthP025Upper2550
  | 26 => edgeFourthP026Upper2550
  | 27 => edgeFourthP027Upper2550
  | 28 => edgeFourthP028Upper2550
  | 29 => edgeFourthP029Upper2550
  | _ => 0

theorem edgeFourthBound2550 (i : Fin 30) :
    edgeFourthCell2550 i ≤ edgeFourthUpper2550 i := by
  fin_cases i
  · exact edgeFourthP000Bound2550
  · exact edgeFourthP001Bound2550
  · exact edgeFourthP002Bound2550
  · exact edgeFourthP003Bound2550
  · exact edgeFourthP004Bound2550
  · exact edgeFourthP005Bound2550
  · exact edgeFourthP006Bound2550
  · exact edgeFourthP007Bound2550
  · exact edgeFourthP008Bound2550
  · exact edgeFourthP009Bound2550
  · exact edgeFourthP010Bound2550
  · exact edgeFourthP011Bound2550
  · exact edgeFourthP012Bound2550
  · exact edgeFourthP013Bound2550
  · exact edgeFourthP014Bound2550
  · exact edgeFourthP015Bound2550
  · exact edgeFourthP016Bound2550
  · exact edgeFourthP017Bound2550
  · exact edgeFourthP018Bound2550
  · exact edgeFourthP019Bound2550
  · exact edgeFourthP020Bound2550
  · exact edgeFourthP021Bound2550
  · exact edgeFourthP022Bound2550
  · exact edgeFourthP023Bound2550
  · exact edgeFourthP024Bound2550
  · exact edgeFourthP025Bound2550
  · exact edgeFourthP026Bound2550
  · exact edgeFourthP027Bound2550
  · exact edgeFourthP028Bound2550
  · exact edgeFourthP029Bound2550

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.edgeFourthP001Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP002Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP003Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP004Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP006Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP007Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP008Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP009Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP010Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP011Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP012Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP013Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP014Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP015Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP016Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP017Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP018Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP019Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP020Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP021Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP022Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP023Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP024Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP025Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP026Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP027Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP028Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP029Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthBound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP000Bound2550
#print axioms ConnesWeilRH.Dev.edgeFourthP005Bound2550
