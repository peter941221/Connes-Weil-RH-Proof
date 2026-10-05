import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteANodeExpN02704Minus2577
import ConnesWeilRH.Dev.C1RouteANodeExpN02705Minus2577

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC02704MinusFourthCell2558 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 nodeExpN02704MinusPointPosition2577 nodeExpN02705MinusPointPosition2577 <
      storedWidth i ^ 2
      then
    weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 nodeExpN02704MinusPointPosition2577 nodeExpN02705MinusPointPosition2577 /
          (storedWidth i
          ^ 2))
      (min (max |nodeExpN02704MinusPointPosition2577| |nodeExpN02705MinusPointPosition2577|)
          (storedWidth i ^ 2)
          /
        (storedWidth i ^ 2)) nodeExpN02704MinusPointPosition2577
            nodeExpN02705MinusPointPosition2577
  else 0


def batchC02704MinusFourthP001Input2558 : RatPair2542 :=
    ((((-(928815707341596352638227857496644026675 * 10^40
        + 1800763338675956100428944370391199161449)) : ℚ) /
        (1329887438149066980314231704239123531053 * 10^40
        + 2500642527054784747187638109798400000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP001Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP001Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP001ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP001Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02704MinusFourthP001Upper2558 : ℝ := ((42461873411 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC02704MinusFourthP001Exponent2558 : ℝ :=
    (((-(928815707341596352638227857496644026675 *
    10^40
        + 1800763338675956100428944370391199161449)) : ℝ) /
        (5194872805269792891852467594684076293 * 10^40
        + 1767580634871307752918701711366400000000))

theorem batchC02704MinusFourthP001ExpBound2558 :
    Real.exp batchC02704MinusFourthP001Exponent2558 ≤ batchC02704MinusFourthP001ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP001Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP001Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP001Input2558 8).1 =
      batchC02704MinusFourthP001Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP001Input2558 8).2 : ℝ) =
      batchC02704MinusFourthP001Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP001Input2558 8).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP001Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP001Input2558 hz 8
  rw [hc, he] at h
  have ha : (2 : ℂ)^8 * embedPair2542 batchC02704MinusFourthP001Input2558 =
      (batchC02704MinusFourthP001Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP001Input2558,
        batchC02704MinusFourthP001Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP001Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP001Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP001Center2558))).trans
  norm_num [batchC02704MinusFourthP001Error2558, batchC02704MinusFourthP001ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP001Center2558]

theorem batchC02704MinusFourthP001Bound2558 : batchC02704MinusFourthCell2558 ⟨1, by omega⟩ ≤
    batchC02704MinusFourthP001Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      batchC02704MinusFourthP001Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP001Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP001Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((6377867179716807655257936565895168 : ℝ) /
        6985282995007638018843380897109375) ((95707621777613709907473135050948608 : ℝ) /
        104779244925114570282650713456640625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP001ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP001Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((6377867179716807655257936565895168 : ℝ) /
        6985282995007638018843380897109375) ((95707621777613709907473135050948608 : ℝ) /
        104779244925114570282650713456640625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP001ExpUpper2558, batchC02704MinusFourthP001Frequency2558,
        batchC02704MinusFourthP001Upper2558]

def batchC02704MinusFourthP002Input2558 : RatPair2542 :=
    ((((-(486942536370938562832843387165606714490 * 10^40
        + 2364476683442948230006734594873956813241)) : ℚ) /
        (521652446426414874361330349304172037122 * 10^40
        + 167837173132765968392868417126400000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP002Center2558 : RatPair2542 := (((4143016148568414498637 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP002Error2558 : ℝ := ((2965882691063918401 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP002ExpUpper2558 : ℝ :=
    ((18221177717658849675866078277283649 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP002Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02704MinusFourthP002Upper2558 : ℝ := ((723456619307114479587611917949 : ℝ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704MinusFourthP002Exponent2558 : ℝ :=
    (((-(486942536370938562832843387165606714490 *
    10^40
        + 2364476683442948230006734594873956813241)) : ℝ) /
        (8150819475412732411895786707877688080 * 10^40
        + 315122455830199468256138569017600000000))

theorem batchC02704MinusFourthP002ExpBound2558 :
    Real.exp batchC02704MinusFourthP002Exponent2558 ≤ batchC02704MinusFourthP002ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP002Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP002Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP002Input2558 6).1 =
      batchC02704MinusFourthP002Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP002Input2558 6).2 : ℝ) =
      batchC02704MinusFourthP002Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP002Input2558 6).2 =
        ((2965882691063918401 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP002Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP002Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02704MinusFourthP002Input2558 =
      (batchC02704MinusFourthP002Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP002Input2558,
        batchC02704MinusFourthP002Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP002Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP002Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP002Center2558))).trans
  norm_num [batchC02704MinusFourthP002Error2558, batchC02704MinusFourthP002ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP002Center2558]

theorem batchC02704MinusFourthP002Bound2558 : batchC02704MinusFourthCell2558 ⟨2, by omega⟩ ≤
    batchC02704MinusFourthP002Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      batchC02704MinusFourthP002Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP002Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP002Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((3644495531266747231575963751940096 : ℝ) /
        5100784558061209130705753111015625) ((382830487110454839629892540203794432 : ℝ) /
        535582378596426958724104076656640625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP002ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP002Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((3644495531266747231575963751940096 : ℝ) /
        5100784558061209130705753111015625) ((382830487110454839629892540203794432 : ℝ) /
        535582378596426958724104076656640625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP002ExpUpper2558, batchC02704MinusFourthP002Frequency2558,
        batchC02704MinusFourthP002Upper2558]

def batchC02704MinusFourthP003Input2558 : RatPair2542 := ((((-((171 * 10^40
        + 9848168594450746501903434973473284102662) * 10^40
        + 5479046296014258441205671516897523097889)) : ℚ) /
        ((254 * 10^40
        + 6795051163305763854603262128160301478177) * 10^40
        + 6075417898252286579668833059225600000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP003Center2558 : RatPair2542 := (((248294351367705127183051726895 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP003Error2558 : ℝ := ((17163081973635823312218473 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02704MinusFourthP003ExpUpper2558 : ℝ := (((13 * 10^40
        + 6501263219945795316391128514587936336233) : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02704MinusFourthP003Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02704MinusFourthP003Upper2558 : ℝ :=
    ((2063640191649490554011579307389706961 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704MinusFourthP003Exponent2558 : ℝ := (((-((171 * 10^40
        + 9848168594450746501903434973473284102662) * 10^40
        + 5479046296014258441205671516897523097889)) : ℝ) /
        ((3 * 10^40
        + 9793672674426652560228175970752504710596) * 10^40
        + 5251178404660191977807325516550400000000))

theorem batchC02704MinusFourthP003ExpBound2558 :
    Real.exp batchC02704MinusFourthP003Exponent2558 ≤ batchC02704MinusFourthP003ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP003Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP003Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP003Input2558 6).1 =
      batchC02704MinusFourthP003Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP003Input2558 6).2 : ℝ) =
      batchC02704MinusFourthP003Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP003Input2558 6).2 =
        ((17163081973635823312218473 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP003Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP003Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02704MinusFourthP003Input2558 =
      (batchC02704MinusFourthP003Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP003Input2558,
        batchC02704MinusFourthP003Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP003Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP003Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP003Center2558))).trans
  norm_num [batchC02704MinusFourthP003Error2558, batchC02704MinusFourthP003ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP003Center2558]

theorem batchC02704MinusFourthP003Bound2558 : batchC02704MinusFourthCell2558 ⟨3, by omega⟩ ≤
    batchC02704MinusFourthP003Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      batchC02704MinusFourthP003Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP003Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP003Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((174935785500803867115646260093124608 : ℝ) /
        304598329940554508493939872216796875) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP003ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP003Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((174935785500803867115646260093124608 : ℝ) /
        304598329940554508493939872216796875) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP003ExpUpper2558, batchC02704MinusFourthP003Frequency2558,
        batchC02704MinusFourthP003Upper2558]

def batchC02704MinusFourthP004Input2558 : RatPair2542 := ((((-((5 * 10^40
        + 3915718546565880315964313755634644003673) * 10^40
        + 6578322271856260240034631538472321348809)) : ℚ) /
        ((9 * 10^40
        + 3163782104840629727251500667450706829487) * 10^40
        + 3658983786596447251250552439193600000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP004Center2558 : RatPair2542 := (((120053031146437690522314770970415 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP004Error2558 : ℝ := ((15069113858758863325157394985 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP004ExpUpper2558 : ℝ := (((13199 * 10^40
        + 9703695262547599062300239992952945642025) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP004Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02704MinusFourthP004Upper2558 : ℝ :=
    ((560580290701294177234311079258368851263 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704MinusFourthP004Exponent2558 : ℝ := (((-((5 * 10^40
        + 3915718546565880315964313755634644003673) * 10^40
        + 6578322271856260240034631538472321348809)) : ℝ) /
        (1455684095388134839488304697928917294210 * 10^40
        + 7400921621665569488300789881862400000000))

theorem batchC02704MinusFourthP004ExpBound2558 :
    Real.exp batchC02704MinusFourthP004Exponent2558 ≤ batchC02704MinusFourthP004ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP004Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP004Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP004Input2558 6).1 =
      batchC02704MinusFourthP004Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP004Input2558 6).2 : ℝ) =
      batchC02704MinusFourthP004Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP004Input2558 6).2 =
        ((15069113858758863325157394985 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP004Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP004Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02704MinusFourthP004Input2558 =
      (batchC02704MinusFourthP004Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP004Input2558,
        batchC02704MinusFourthP004Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP004Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP004Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP004Center2558))).trans
  norm_num [batchC02704MinusFourthP004Error2558, batchC02704MinusFourthP004ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP004Center2558]

theorem batchC02704MinusFourthP004Bound2558 : batchC02704MinusFourthCell2558 ⟨4, by omega⟩ ≤
    batchC02704MinusFourthP004Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      batchC02704MinusFourthP004Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP004Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP004Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((25511468718867230621031746263580672 : ℝ) /
        54086425609737808813990931158359375) ((382830487110454839629892540203794432 : ℝ) /
        811296384146067132209863967375390625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP004ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP004Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((25511468718867230621031746263580672 : ℝ) /
        54086425609737808813990931158359375) ((382830487110454839629892540203794432 : ℝ) /
        811296384146067132209863967375390625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP004ExpUpper2558, batchC02704MinusFourthP004Frequency2558,
        batchC02704MinusFourthP004Upper2558]

def batchC02704MinusFourthP006Input2558 : RatPair2542 := ((((-315435339213257919050017507738639) :
    ℚ) /
        553576811647631326176051200000000),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP006Center2558 : RatPair2542 := (((30836253259177183 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP006Error2558 : ℝ := ((2467886130617 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

noncomputable def batchC02704MinusFourthP006ExpUpper2558 : ℝ := ((8476204753877724890568189369 :
    ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

noncomputable def batchC02704MinusFourthP006Frequency2558 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02704MinusFourthP006Upper2558 : ℝ := ((455239028875360603024561 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02704MinusFourthP006Exponent2558 : ℝ :=
    (((-315435339213257919050017507738639) : ℝ) /
        4324818840997119735750400000000)

theorem batchC02704MinusFourthP006ExpBound2558 :
    Real.exp batchC02704MinusFourthP006Exponent2558 ≤ batchC02704MinusFourthP006ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP006Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP006Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP006Input2558 7).1 =
      batchC02704MinusFourthP006Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP006Input2558 7).2 : ℝ) =
      batchC02704MinusFourthP006Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP006Input2558 7).2 =
        ((2467886130617 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP006Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP006Input2558 hz 7
  rw [hc, he] at h
  have ha : (2 : ℂ)^7 * embedPair2542 batchC02704MinusFourthP006Input2558 =
      (batchC02704MinusFourthP006Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP006Input2558,
        batchC02704MinusFourthP006Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP006Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP006Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP006Center2558))).trans
  norm_num [batchC02704MinusFourthP006Error2558, batchC02704MinusFourthP006ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP006Center2558]

theorem batchC02704MinusFourthP006Bound2558 : batchC02704MinusFourthCell2558 ⟨6, by omega⟩ ≤
    batchC02704MinusFourthP006Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      batchC02704MinusFourthP006Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP006Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP006Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) ((31653888483 : ℝ) /
        40960000000) ((9895936151 : ℝ) /
        12800000000) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP006ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP006Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) ((31653888483 : ℝ) /
        40960000000) ((9895936151 : ℝ) /
        12800000000) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP006ExpUpper2558, batchC02704MinusFourthP006Frequency2558,
        batchC02704MinusFourthP006Upper2558]

def batchC02704MinusFourthP007Input2558 : RatPair2542 := ((((-((171 * 10^40
        + 9848168594450746501903434973473284102662) * 10^40
        + 5479046296014258441205671516897523097889)) : ℚ) /
        ((254 * 10^40
        + 6795051163305763854603262128160301478177) * 10^40
        + 6075417898252286579668833059225600000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP007Center2558 : RatPair2542 := (((248294351367705127183051726895 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP007Error2558 : ℝ := ((17163081973635823312218473 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02704MinusFourthP007ExpUpper2558 : ℝ := (((13 * 10^40
        + 6501263219945795316391128514587936336233) : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02704MinusFourthP007Frequency2558 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02704MinusFourthP007Upper2558 : ℝ := ((13355975308440147839433449917903433
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704MinusFourthP007Exponent2558 : ℝ := (((-((171 * 10^40
        + 9848168594450746501903434973473284102662) * 10^40
        + 5479046296014258441205671516897523097889)) : ℝ) /
        ((3 * 10^40
        + 9793672674426652560228175970752504710596) * 10^40
        + 5251178404660191977807325516550400000000))

theorem batchC02704MinusFourthP007ExpBound2558 :
    Real.exp batchC02704MinusFourthP007Exponent2558 ≤ batchC02704MinusFourthP007ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP007Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP007Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP007Input2558 6).1 =
      batchC02704MinusFourthP007Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP007Input2558 6).2 : ℝ) =
      batchC02704MinusFourthP007Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP007Input2558 6).2 =
        ((17163081973635823312218473 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP007Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP007Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02704MinusFourthP007Input2558 =
      (batchC02704MinusFourthP007Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP007Input2558,
        batchC02704MinusFourthP007Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP007Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP007Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP007Center2558))).trans
  norm_num [batchC02704MinusFourthP007Error2558, batchC02704MinusFourthP007ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP007Center2558]

theorem batchC02704MinusFourthP007Bound2558 : batchC02704MinusFourthCell2558 ⟨7, by omega⟩ ≤
    batchC02704MinusFourthP007Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      batchC02704MinusFourthP007Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP007Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP007Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((174935785500803867115646260093124608 : ℝ) /
        304598329940554508493939872216796875) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP007ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP007Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((174935785500803867115646260093124608 : ℝ) /
        304598329940554508493939872216796875) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP007ExpUpper2558, batchC02704MinusFourthP007Frequency2558,
        batchC02704MinusFourthP007Upper2558]

def batchC02704MinusFourthP008Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP008Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP008Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP008ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP008Frequency2558 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def batchC02704MinusFourthP008Upper2558 : ℝ := ((120954110126371055347769 : ℝ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968))

noncomputable def batchC02704MinusFourthP008Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP008ExpBound2558 :
    Real.exp batchC02704MinusFourthP008Exponent2558 ≤ batchC02704MinusFourthP008ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP008Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP008Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP008Input2558 13).1 =
      batchC02704MinusFourthP008Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP008Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP008Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP008Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP008Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP008Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP008Input2558 =
      (batchC02704MinusFourthP008Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP008Input2558,
        batchC02704MinusFourthP008Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP008Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP008Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP008Center2558))).trans
  norm_num [batchC02704MinusFourthP008Error2558, batchC02704MinusFourthP008ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP008Center2558]

theorem batchC02704MinusFourthP008Bound2558 : batchC02704MinusFourthCell2558 ⟨8, by omega⟩ ≤
    batchC02704MinusFourthP008Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      batchC02704MinusFourthP008Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP008Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP008Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP008ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP008Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP008ExpUpper2558, batchC02704MinusFourthP008Frequency2558,
        batchC02704MinusFourthP008Upper2558]

def batchC02704MinusFourthP009Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP009Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP009Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP009ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP009Frequency2558 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def batchC02704MinusFourthP009Upper2558 : ℝ := ((3870619510604789013838761 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704MinusFourthP009Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP009ExpBound2558 :
    Real.exp batchC02704MinusFourthP009Exponent2558 ≤ batchC02704MinusFourthP009ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP009Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP009Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP009Input2558 13).1 =
      batchC02704MinusFourthP009Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP009Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP009Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP009Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP009Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP009Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP009Input2558 =
      (batchC02704MinusFourthP009Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP009Input2558,
        batchC02704MinusFourthP009Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP009Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP009Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP009Center2558))).trans
  norm_num [batchC02704MinusFourthP009Error2558, batchC02704MinusFourthP009ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP009Center2558]

theorem batchC02704MinusFourthP009Bound2558 : batchC02704MinusFourthCell2558 ⟨9, by omega⟩ ≤
    batchC02704MinusFourthP009Upper2558 := by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      batchC02704MinusFourthP009Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP009Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP009Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP009ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP009Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP009ExpUpper2558, batchC02704MinusFourthP009Frequency2558,
        batchC02704MinusFourthP009Upper2558]

def batchC02704MinusFourthP010Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP010Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP010Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP010ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP010Frequency2558 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def batchC02704MinusFourthP010Upper2558 : ℝ := ((1935335239204959190269203 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02704MinusFourthP010Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP010ExpBound2558 :
    Real.exp batchC02704MinusFourthP010Exponent2558 ≤ batchC02704MinusFourthP010ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP010Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP010Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP010Input2558 13).1 =
      batchC02704MinusFourthP010Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP010Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP010Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP010Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP010Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP010Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP010Input2558 =
      (batchC02704MinusFourthP010Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP010Input2558,
        batchC02704MinusFourthP010Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP010Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP010Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP010Center2558))).trans
  norm_num [batchC02704MinusFourthP010Error2558, batchC02704MinusFourthP010ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP010Center2558]

theorem batchC02704MinusFourthP010Bound2558 : batchC02704MinusFourthCell2558 ⟨10, by omega⟩ ≤
    batchC02704MinusFourthP010Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      batchC02704MinusFourthP010Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP010Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP010Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP010ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP010Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP010ExpUpper2558, batchC02704MinusFourthP010Frequency2558,
        batchC02704MinusFourthP010Upper2558]

def batchC02704MinusFourthP011Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP011Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP011Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP011ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP011Frequency2558 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def batchC02704MinusFourthP011Upper2558 : ℝ := ((967676115598543204657381 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02704MinusFourthP011Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP011ExpBound2558 :
    Real.exp batchC02704MinusFourthP011Exponent2558 ≤ batchC02704MinusFourthP011ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP011Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP011Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP011Input2558 13).1 =
      batchC02704MinusFourthP011Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP011Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP011Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP011Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP011Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP011Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP011Input2558 =
      (batchC02704MinusFourthP011Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP011Input2558,
        batchC02704MinusFourthP011Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP011Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP011Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP011Center2558))).trans
  norm_num [batchC02704MinusFourthP011Error2558, batchC02704MinusFourthP011ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP011Center2558]

theorem batchC02704MinusFourthP011Bound2558 : batchC02704MinusFourthCell2558 ⟨11, by omega⟩ ≤
    batchC02704MinusFourthP011Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      batchC02704MinusFourthP011Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP011Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP011Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP011ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP011Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP011ExpUpper2558, batchC02704MinusFourthP011Frequency2558,
        batchC02704MinusFourthP011Upper2558]

def batchC02704MinusFourthP012Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP012Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP012Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP012ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP012Frequency2558 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def batchC02704MinusFourthP012Upper2558 : ℝ := ((3870739662853747186434707 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704MinusFourthP012Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP012ExpBound2558 :
    Real.exp batchC02704MinusFourthP012Exponent2558 ≤ batchC02704MinusFourthP012ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP012Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP012Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP012Input2558 13).1 =
      batchC02704MinusFourthP012Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP012Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP012Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP012Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP012Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP012Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP012Input2558 =
      (batchC02704MinusFourthP012Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP012Input2558,
        batchC02704MinusFourthP012Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP012Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP012Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP012Center2558))).trans
  norm_num [batchC02704MinusFourthP012Error2558, batchC02704MinusFourthP012ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP012Center2558]

theorem batchC02704MinusFourthP012Bound2558 : batchC02704MinusFourthCell2558 ⟨12, by omega⟩ ≤
    batchC02704MinusFourthP012Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      batchC02704MinusFourthP012Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP012Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP012Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP012ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP012Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP012ExpUpper2558, batchC02704MinusFourthP012Frequency2558,
        batchC02704MinusFourthP012Upper2558]

def batchC02704MinusFourthP013Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP013Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP013Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP013ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP013Frequency2558 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def batchC02704MinusFourthP013Upper2558 : ℝ := ((1935385870748197386101557 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02704MinusFourthP013Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP013ExpBound2558 :
    Real.exp batchC02704MinusFourthP013Exponent2558 ≤ batchC02704MinusFourthP013ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP013Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP013Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP013Input2558 13).1 =
      batchC02704MinusFourthP013Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP013Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP013Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP013Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP013Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP013Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP013Input2558 =
      (batchC02704MinusFourthP013Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP013Input2558,
        batchC02704MinusFourthP013Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP013Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP013Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP013Center2558))).trans
  norm_num [batchC02704MinusFourthP013Error2558, batchC02704MinusFourthP013ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP013Center2558]

theorem batchC02704MinusFourthP013Bound2558 : batchC02704MinusFourthCell2558 ⟨13, by omega⟩ ≤
    batchC02704MinusFourthP013Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      batchC02704MinusFourthP013Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP013Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP013Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP013ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP013Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP013ExpUpper2558, batchC02704MinusFourthP013Frequency2558,
        batchC02704MinusFourthP013Upper2558]

def batchC02704MinusFourthP014Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP014Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP014Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP014ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP014Frequency2558 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def batchC02704MinusFourthP014Upper2558 : ℝ := ((967707795469994190649663 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02704MinusFourthP014Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP014ExpBound2558 :
    Real.exp batchC02704MinusFourthP014Exponent2558 ≤ batchC02704MinusFourthP014ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP014Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP014Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP014Input2558 13).1 =
      batchC02704MinusFourthP014Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP014Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP014Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP014Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP014Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP014Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP014Input2558 =
      (batchC02704MinusFourthP014Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP014Input2558,
        batchC02704MinusFourthP014Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP014Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP014Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP014Center2558))).trans
  norm_num [batchC02704MinusFourthP014Error2558, batchC02704MinusFourthP014ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP014Center2558]

theorem batchC02704MinusFourthP014Bound2558 : batchC02704MinusFourthCell2558 ⟨14, by omega⟩ ≤
    batchC02704MinusFourthP014Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      batchC02704MinusFourthP014Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP014Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP014Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP014ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP014Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP014ExpUpper2558, batchC02704MinusFourthP014Frequency2558,
        batchC02704MinusFourthP014Upper2558]

def batchC02704MinusFourthP015Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP015Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP015Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP015ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP015Frequency2558 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def batchC02704MinusFourthP015Upper2558 : ℝ := ((967718443095214099583807 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02704MinusFourthP015Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP015ExpBound2558 :
    Real.exp batchC02704MinusFourthP015Exponent2558 ≤ batchC02704MinusFourthP015ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP015Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP015Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP015Input2558 13).1 =
      batchC02704MinusFourthP015Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP015Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP015Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP015Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP015Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP015Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP015Input2558 =
      (batchC02704MinusFourthP015Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP015Input2558,
        batchC02704MinusFourthP015Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP015Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP015Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP015Center2558))).trans
  norm_num [batchC02704MinusFourthP015Error2558, batchC02704MinusFourthP015ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP015Center2558]

theorem batchC02704MinusFourthP015Bound2558 : batchC02704MinusFourthCell2558 ⟨15, by omega⟩ ≤
    batchC02704MinusFourthP015Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      batchC02704MinusFourthP015Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP015Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP015Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP015ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP015Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP015ExpUpper2558, batchC02704MinusFourthP015Frequency2558,
        batchC02704MinusFourthP015Upper2558]

def batchC02704MinusFourthP016Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP016Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP016Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP016ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP016Frequency2558 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def batchC02704MinusFourthP016Upper2558 : ℝ := ((3870904552154991645377839 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704MinusFourthP016Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP016ExpBound2558 :
    Real.exp batchC02704MinusFourthP016Exponent2558 ≤ batchC02704MinusFourthP016ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP016Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP016Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP016Input2558 13).1 =
      batchC02704MinusFourthP016Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP016Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP016Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP016Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP016Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP016Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP016Input2558 =
      (batchC02704MinusFourthP016Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP016Input2558,
        batchC02704MinusFourthP016Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP016Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP016Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP016Center2558))).trans
  norm_num [batchC02704MinusFourthP016Error2558, batchC02704MinusFourthP016ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP016Center2558]

theorem batchC02704MinusFourthP016Bound2558 : batchC02704MinusFourthCell2558 ⟨16, by omega⟩ ≤
    batchC02704MinusFourthP016Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      batchC02704MinusFourthP016Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP016Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP016Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP016ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP016Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP016ExpUpper2558, batchC02704MinusFourthP016Frequency2558,
        batchC02704MinusFourthP016Upper2558]

def batchC02704MinusFourthP017Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP017Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP017Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP017ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP017Frequency2558 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def batchC02704MinusFourthP017Upper2558 : ℝ := ((241935271318342328517689 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC02704MinusFourthP017Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP017ExpBound2558 :
    Real.exp batchC02704MinusFourthP017Exponent2558 ≤ batchC02704MinusFourthP017ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP017Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP017Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP017Input2558 13).1 =
      batchC02704MinusFourthP017Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP017Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP017Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP017Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP017Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP017Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP017Input2558 =
      (batchC02704MinusFourthP017Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP017Input2558,
        batchC02704MinusFourthP017Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP017Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP017Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP017Center2558))).trans
  norm_num [batchC02704MinusFourthP017Error2558, batchC02704MinusFourthP017ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP017Center2558]

theorem batchC02704MinusFourthP017Bound2558 : batchC02704MinusFourthCell2558 ⟨17, by omega⟩ ≤
    batchC02704MinusFourthP017Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      batchC02704MinusFourthP017Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP017Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP017Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP017ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP017Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP017ExpUpper2558, batchC02704MinusFourthP017Frequency2558,
        batchC02704MinusFourthP017Upper2558]

def batchC02704MinusFourthP018Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP018Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP018Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP018ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP018Frequency2558 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def batchC02704MinusFourthP018Upper2558 : ℝ := ((3870986946376885678543779 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704MinusFourthP018Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP018ExpBound2558 :
    Real.exp batchC02704MinusFourthP018Exponent2558 ≤ batchC02704MinusFourthP018ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP018Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP018Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP018Input2558 13).1 =
      batchC02704MinusFourthP018Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP018Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP018Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP018Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP018Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP018Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP018Input2558 =
      (batchC02704MinusFourthP018Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP018Input2558,
        batchC02704MinusFourthP018Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP018Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP018Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP018Center2558))).trans
  norm_num [batchC02704MinusFourthP018Error2558, batchC02704MinusFourthP018ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP018Center2558]

theorem batchC02704MinusFourthP018Bound2558 : batchC02704MinusFourthCell2558 ⟨18, by omega⟩ ≤
    batchC02704MinusFourthP018Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      batchC02704MinusFourthP018Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP018Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP018Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP018ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP018Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP018ExpUpper2558, batchC02704MinusFourthP018Frequency2558,
        batchC02704MinusFourthP018Upper2558]

def batchC02704MinusFourthP019Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP019Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP019Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP019ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP019Frequency2558 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def batchC02704MinusFourthP019Upper2558 : ℝ := ((1935513900364944448776163 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02704MinusFourthP019Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP019ExpBound2558 :
    Real.exp batchC02704MinusFourthP019Exponent2558 ≤ batchC02704MinusFourthP019ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP019Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP019Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP019Input2558 13).1 =
      batchC02704MinusFourthP019Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP019Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP019Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP019Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP019Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP019Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP019Input2558 =
      (batchC02704MinusFourthP019Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP019Input2558,
        batchC02704MinusFourthP019Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP019Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP019Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP019Center2558))).trans
  norm_num [batchC02704MinusFourthP019Error2558, batchC02704MinusFourthP019ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP019Center2558]

theorem batchC02704MinusFourthP019Bound2558 : batchC02704MinusFourthCell2558 ⟨19, by omega⟩ ≤
    batchC02704MinusFourthP019Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      batchC02704MinusFourthP019Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP019Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP019Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP019ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP019Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP019ExpUpper2558, batchC02704MinusFourthP019Frequency2558,
        batchC02704MinusFourthP019Upper2558]

def batchC02704MinusFourthP020Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP020Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP020Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP020ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP020Frequency2558 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def batchC02704MinusFourthP020Upper2558 : ℝ := ((3871072227191669323847077 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704MinusFourthP020Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP020ExpBound2558 :
    Real.exp batchC02704MinusFourthP020Exponent2558 ≤ batchC02704MinusFourthP020ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP020Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP020Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP020Input2558 13).1 =
      batchC02704MinusFourthP020Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP020Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP020Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP020Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP020Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP020Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP020Input2558 =
      (batchC02704MinusFourthP020Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP020Input2558,
        batchC02704MinusFourthP020Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP020Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP020Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP020Center2558))).trans
  norm_num [batchC02704MinusFourthP020Error2558, batchC02704MinusFourthP020ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP020Center2558]

theorem batchC02704MinusFourthP020Bound2558 : batchC02704MinusFourthCell2558 ⟨20, by omega⟩ ≤
    batchC02704MinusFourthP020Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      batchC02704MinusFourthP020Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP020Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP020Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP020ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP020Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP020ExpUpper2558, batchC02704MinusFourthP020Frequency2558,
        batchC02704MinusFourthP020Upper2558]

def batchC02704MinusFourthP021Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP021Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP021Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP021ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP021Frequency2558 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def batchC02704MinusFourthP021Upper2558 : ℝ := ((3871109303272587756184355 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704MinusFourthP021Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP021ExpBound2558 :
    Real.exp batchC02704MinusFourthP021Exponent2558 ≤ batchC02704MinusFourthP021ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP021Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP021Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP021Input2558 13).1 =
      batchC02704MinusFourthP021Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP021Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP021Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP021Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP021Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP021Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP021Input2558 =
      (batchC02704MinusFourthP021Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP021Input2558,
        batchC02704MinusFourthP021Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP021Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP021Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP021Center2558))).trans
  norm_num [batchC02704MinusFourthP021Error2558, batchC02704MinusFourthP021ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP021Center2558]

theorem batchC02704MinusFourthP021Bound2558 : batchC02704MinusFourthCell2558 ⟨21, by omega⟩ ≤
    batchC02704MinusFourthP021Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      batchC02704MinusFourthP021Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP021Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP021Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP021ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP021Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP021ExpUpper2558, batchC02704MinusFourthP021Frequency2558,
        batchC02704MinusFourthP021Upper2558]

def batchC02704MinusFourthP022Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP022Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP022Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP022ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP022Frequency2558 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def batchC02704MinusFourthP022Upper2558 : ℝ := ((3871128280333083228798205 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704MinusFourthP022Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP022ExpBound2558 :
    Real.exp batchC02704MinusFourthP022Exponent2558 ≤ batchC02704MinusFourthP022ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP022Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP022Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP022Input2558 13).1 =
      batchC02704MinusFourthP022Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP022Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP022Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP022Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP022Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP022Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP022Input2558 =
      (batchC02704MinusFourthP022Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP022Input2558,
        batchC02704MinusFourthP022Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP022Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP022Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP022Center2558))).trans
  norm_num [batchC02704MinusFourthP022Error2558, batchC02704MinusFourthP022ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP022Center2558]

theorem batchC02704MinusFourthP022Bound2558 : batchC02704MinusFourthCell2558 ⟨22, by omega⟩ ≤
    batchC02704MinusFourthP022Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      batchC02704MinusFourthP022Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP022Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP022Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP022ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP022Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP022ExpUpper2558, batchC02704MinusFourthP022Frequency2558,
        batchC02704MinusFourthP022Upper2558]

def batchC02704MinusFourthP023Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP023Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP023Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP023ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP023Frequency2558 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def batchC02704MinusFourthP023Upper2558 : ℝ := ((3871182995286712877289067 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704MinusFourthP023Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP023ExpBound2558 :
    Real.exp batchC02704MinusFourthP023Exponent2558 ≤ batchC02704MinusFourthP023ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP023Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP023Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP023Input2558 13).1 =
      batchC02704MinusFourthP023Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP023Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP023Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP023Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP023Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP023Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP023Input2558 =
      (batchC02704MinusFourthP023Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP023Input2558,
        batchC02704MinusFourthP023Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP023Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP023Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP023Center2558))).trans
  norm_num [batchC02704MinusFourthP023Error2558, batchC02704MinusFourthP023ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP023Center2558]

theorem batchC02704MinusFourthP023Bound2558 : batchC02704MinusFourthCell2558 ⟨23, by omega⟩ ≤
    batchC02704MinusFourthP023Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      batchC02704MinusFourthP023Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP023Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP023Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP023ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP023Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP023ExpUpper2558, batchC02704MinusFourthP023Frequency2558,
        batchC02704MinusFourthP023Upper2558]

def batchC02704MinusFourthP024Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP024Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP024Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP024ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP024Frequency2558 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def batchC02704MinusFourthP024Upper2558 : ℝ := ((483901017541733307533591 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC02704MinusFourthP024Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP024ExpBound2558 :
    Real.exp batchC02704MinusFourthP024Exponent2558 ≤ batchC02704MinusFourthP024ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP024Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP024Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP024Input2558 13).1 =
      batchC02704MinusFourthP024Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP024Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP024Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP024Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP024Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP024Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP024Input2558 =
      (batchC02704MinusFourthP024Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP024Input2558,
        batchC02704MinusFourthP024Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP024Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP024Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP024Center2558))).trans
  norm_num [batchC02704MinusFourthP024Error2558, batchC02704MinusFourthP024ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP024Center2558]

theorem batchC02704MinusFourthP024Bound2558 : batchC02704MinusFourthCell2558 ⟨24, by omega⟩ ≤
    batchC02704MinusFourthP024Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      batchC02704MinusFourthP024Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP024Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP024Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP024ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP024Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP024ExpUpper2558, batchC02704MinusFourthP024Frequency2558,
        batchC02704MinusFourthP024Upper2558]

def batchC02704MinusFourthP025Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP025Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP025Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP025ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP025Frequency2558 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def batchC02704MinusFourthP025Upper2558 : ℝ := ((967809916960286156306765 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02704MinusFourthP025Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP025ExpBound2558 :
    Real.exp batchC02704MinusFourthP025Exponent2558 ≤ batchC02704MinusFourthP025ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP025Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP025Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP025Input2558 13).1 =
      batchC02704MinusFourthP025Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP025Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP025Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP025Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP025Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP025Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP025Input2558 =
      (batchC02704MinusFourthP025Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP025Input2558,
        batchC02704MinusFourthP025Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP025Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP025Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP025Center2558))).trans
  norm_num [batchC02704MinusFourthP025Error2558, batchC02704MinusFourthP025ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP025Center2558]

theorem batchC02704MinusFourthP025Bound2558 : batchC02704MinusFourthCell2558 ⟨25, by omega⟩ ≤
    batchC02704MinusFourthP025Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      batchC02704MinusFourthP025Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP025Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP025Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP025ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP025Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP025ExpUpper2558, batchC02704MinusFourthP025Frequency2558,
        batchC02704MinusFourthP025Upper2558]

def batchC02704MinusFourthP026Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP026Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP026Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP026ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP026Frequency2558 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def batchC02704MinusFourthP026Upper2558 : ℝ := ((3871271887933041351091371 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704MinusFourthP026Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP026ExpBound2558 :
    Real.exp batchC02704MinusFourthP026Exponent2558 ≤ batchC02704MinusFourthP026ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP026Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP026Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP026Input2558 13).1 =
      batchC02704MinusFourthP026Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP026Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP026Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP026Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP026Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP026Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP026Input2558 =
      (batchC02704MinusFourthP026Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP026Input2558,
        batchC02704MinusFourthP026Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP026Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP026Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP026Center2558))).trans
  norm_num [batchC02704MinusFourthP026Error2558, batchC02704MinusFourthP026ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP026Center2558]

theorem batchC02704MinusFourthP026Bound2558 : batchC02704MinusFourthCell2558 ⟨26, by omega⟩ ≤
    batchC02704MinusFourthP026Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      batchC02704MinusFourthP026Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP026Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP026Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP026ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP026Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP026ExpUpper2558, batchC02704MinusFourthP026Frequency2558,
        batchC02704MinusFourthP026Upper2558]

def batchC02704MinusFourthP027Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP027Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP027Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP027ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP027Frequency2558 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def batchC02704MinusFourthP027Upper2558 : ℝ := ((1935659191513995017591871 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02704MinusFourthP027Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP027ExpBound2558 :
    Real.exp batchC02704MinusFourthP027Exponent2558 ≤ batchC02704MinusFourthP027ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP027Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP027Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP027Input2558 13).1 =
      batchC02704MinusFourthP027Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP027Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP027Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP027Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP027Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP027Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP027Input2558 =
      (batchC02704MinusFourthP027Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP027Input2558,
        batchC02704MinusFourthP027Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP027Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP027Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP027Center2558))).trans
  norm_num [batchC02704MinusFourthP027Error2558, batchC02704MinusFourthP027ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP027Center2558]

theorem batchC02704MinusFourthP027Bound2558 : batchC02704MinusFourthCell2558 ⟨27, by omega⟩ ≤
    batchC02704MinusFourthP027Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      batchC02704MinusFourthP027Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP027Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP027Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP027ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP027Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP027ExpUpper2558, batchC02704MinusFourthP027Frequency2558,
        batchC02704MinusFourthP027Upper2558]

def batchC02704MinusFourthP028Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP028Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP028Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP028ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP028Frequency2558 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def batchC02704MinusFourthP028Upper2558 : ℝ := ((483917098902537606659923 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC02704MinusFourthP028Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP028ExpBound2558 :
    Real.exp batchC02704MinusFourthP028Exponent2558 ≤ batchC02704MinusFourthP028ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP028Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP028Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP028Input2558 13).1 =
      batchC02704MinusFourthP028Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP028Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP028Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP028Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP028Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP028Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP028Input2558 =
      (batchC02704MinusFourthP028Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP028Input2558,
        batchC02704MinusFourthP028Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP028Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP028Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP028Center2558))).trans
  norm_num [batchC02704MinusFourthP028Error2558, batchC02704MinusFourthP028ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP028Center2558]

theorem batchC02704MinusFourthP028Bound2558 : batchC02704MinusFourthCell2558 ⟨28, by omega⟩ ≤
    batchC02704MinusFourthP028Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      batchC02704MinusFourthP028Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP028Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP028Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP028ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP028Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP028ExpUpper2558, batchC02704MinusFourthP028Frequency2558,
        batchC02704MinusFourthP028Upper2558]

def batchC02704MinusFourthP029Input2558 : RatPair2542 := ((((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℚ) /
        ((3258 * 10^40
        + 7595610100228056913778913116660714678843) * 10^40
        + 9488137277258399202920947462963200000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusFourthP029Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusFourthP029Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP029ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704MinusFourthP029Frequency2558 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def batchC02704MinusFourthP029Upper2558 : ℝ := ((1935682408332932262487215 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02704MinusFourthP029Exponent2558 : ℝ := (((-((2890 * 10^40
        + 4047759722486532841347870218976251436005) * 10^40
        + 9664170517656676987247456073974725546561)) : ℝ) /
        (3977977979748562995228732777480061122397 * 10^40
        + 3198179704257477831933950310969600000000))

theorem batchC02704MinusFourthP029ExpBound2558 :
    Real.exp batchC02704MinusFourthP029Exponent2558 ≤ batchC02704MinusFourthP029ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704MinusFourthP029Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusFourthP029Input2558]
  have hc : (compactExp2547 batchC02704MinusFourthP029Input2558 13).1 =
      batchC02704MinusFourthP029Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704MinusFourthP029Input2558 13).2 : ℝ) =
      batchC02704MinusFourthP029Error2558 := by
    have hq : (compactExp2547 batchC02704MinusFourthP029Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704MinusFourthP029Error2558]
  have h := compactExp_error2547 batchC02704MinusFourthP029Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704MinusFourthP029Input2558 =
      (batchC02704MinusFourthP029Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704MinusFourthP029Input2558,
        batchC02704MinusFourthP029Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704MinusFourthP029Exponent2558 : ℂ)) (embedPair2542
        batchC02704MinusFourthP029Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704MinusFourthP029Center2558))).trans
  norm_num [batchC02704MinusFourthP029Error2558, batchC02704MinusFourthP029ExpUpper2558,
      pairMagnitude2542,
      batchC02704MinusFourthP029Center2558]

theorem batchC02704MinusFourthP029Bound2558 : batchC02704MinusFourthCell2558 ⟨29, by omega⟩ ≤
    batchC02704MinusFourthP029Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      batchC02704MinusFourthP029Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704MinusFourthP029Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704MinusFourthP029Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704MinusFourthP029ExpBound2558 using 1; norm_num
        [batchC02704MinusFourthP029Exponent2558])
  have hid : batchC02704MinusFourthCell2558 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704MinusFourthCell2558, cellNearAbs2538,
        nodeExpN02704MinusPointPosition2577,
      nodeExpN02705MinusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704MinusFourthP029ExpUpper2558, batchC02704MinusFourthP029Frequency2558,
        batchC02704MinusFourthP029Upper2558]

noncomputable def batchC02704MinusFourthP000Upper2558 : ℝ := 0

theorem batchC02704MinusFourthP000Bound2558 :
    batchC02704MinusFourthCell2558 ⟨0, by omega⟩ ≤ batchC02704MinusFourthP000Upper2558 := by
  norm_num [batchC02704MinusFourthCell2558, batchC02704MinusFourthP000Upper2558, cellNearAbs2538,
    nodeExpN02704MinusPointPosition2577, nodeExpN02705MinusPointPosition2577, storedWidth]

noncomputable def batchC02704MinusFourthP005Upper2558 : ℝ := 0

theorem batchC02704MinusFourthP005Bound2558 :
    batchC02704MinusFourthCell2558 ⟨5, by omega⟩ ≤ batchC02704MinusFourthP005Upper2558 := by
  norm_num [batchC02704MinusFourthCell2558, batchC02704MinusFourthP005Upper2558, cellNearAbs2538,
    nodeExpN02704MinusPointPosition2577, nodeExpN02705MinusPointPosition2577, storedWidth]

noncomputable def batchC02704MinusFourthUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02704MinusFourthP000Upper2558
  | 1 => batchC02704MinusFourthP001Upper2558
  | 2 => batchC02704MinusFourthP002Upper2558
  | 3 => batchC02704MinusFourthP003Upper2558
  | 4 => batchC02704MinusFourthP004Upper2558
  | 5 => batchC02704MinusFourthP005Upper2558
  | 6 => batchC02704MinusFourthP006Upper2558
  | 7 => batchC02704MinusFourthP007Upper2558
  | 8 => batchC02704MinusFourthP008Upper2558
  | 9 => batchC02704MinusFourthP009Upper2558
  | 10 => batchC02704MinusFourthP010Upper2558
  | 11 => batchC02704MinusFourthP011Upper2558
  | 12 => batchC02704MinusFourthP012Upper2558
  | 13 => batchC02704MinusFourthP013Upper2558
  | 14 => batchC02704MinusFourthP014Upper2558
  | 15 => batchC02704MinusFourthP015Upper2558
  | 16 => batchC02704MinusFourthP016Upper2558
  | 17 => batchC02704MinusFourthP017Upper2558
  | 18 => batchC02704MinusFourthP018Upper2558
  | 19 => batchC02704MinusFourthP019Upper2558
  | 20 => batchC02704MinusFourthP020Upper2558
  | 21 => batchC02704MinusFourthP021Upper2558
  | 22 => batchC02704MinusFourthP022Upper2558
  | 23 => batchC02704MinusFourthP023Upper2558
  | 24 => batchC02704MinusFourthP024Upper2558
  | 25 => batchC02704MinusFourthP025Upper2558
  | 26 => batchC02704MinusFourthP026Upper2558
  | 27 => batchC02704MinusFourthP027Upper2558
  | 28 => batchC02704MinusFourthP028Upper2558
  | 29 => batchC02704MinusFourthP029Upper2558
  | _ => 0

theorem batchC02704MinusFourthBound2558 (i : Fin 30) :
    batchC02704MinusFourthCell2558 i ≤ batchC02704MinusFourthUpper2558 i := by
  fin_cases i
  · exact batchC02704MinusFourthP000Bound2558
  · exact batchC02704MinusFourthP001Bound2558
  · exact batchC02704MinusFourthP002Bound2558
  · exact batchC02704MinusFourthP003Bound2558
  · exact batchC02704MinusFourthP004Bound2558
  · exact batchC02704MinusFourthP005Bound2558
  · exact batchC02704MinusFourthP006Bound2558
  · exact batchC02704MinusFourthP007Bound2558
  · exact batchC02704MinusFourthP008Bound2558
  · exact batchC02704MinusFourthP009Bound2558
  · exact batchC02704MinusFourthP010Bound2558
  · exact batchC02704MinusFourthP011Bound2558
  · exact batchC02704MinusFourthP012Bound2558
  · exact batchC02704MinusFourthP013Bound2558
  · exact batchC02704MinusFourthP014Bound2558
  · exact batchC02704MinusFourthP015Bound2558
  · exact batchC02704MinusFourthP016Bound2558
  · exact batchC02704MinusFourthP017Bound2558
  · exact batchC02704MinusFourthP018Bound2558
  · exact batchC02704MinusFourthP019Bound2558
  · exact batchC02704MinusFourthP020Bound2558
  · exact batchC02704MinusFourthP021Bound2558
  · exact batchC02704MinusFourthP022Bound2558
  · exact batchC02704MinusFourthP023Bound2558
  · exact batchC02704MinusFourthP024Bound2558
  · exact batchC02704MinusFourthP025Bound2558
  · exact batchC02704MinusFourthP026Bound2558
  · exact batchC02704MinusFourthP027Bound2558
  · exact batchC02704MinusFourthP028Bound2558
  · exact batchC02704MinusFourthP029Bound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP001Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP002Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP003Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP004Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP006Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP007Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP008Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP009Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP010Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP011Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP012Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP013Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP014Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP015Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP016Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP017Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP018Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP019Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP020Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP021Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP022Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP023Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP024Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP025Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP026Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP027Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP028Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP029Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthBound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP000Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704MinusFourthP005Bound2558
