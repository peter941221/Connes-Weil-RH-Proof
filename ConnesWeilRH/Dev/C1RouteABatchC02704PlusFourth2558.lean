import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteANodeExpN02704Plus2577
import ConnesWeilRH.Dev.C1RouteANodeExpN02705Plus2577

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC02704PlusFourthCell2558 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 nodeExpN02704PlusPointPosition2577 nodeExpN02705PlusPointPosition2577 <
      storedWidth i ^ 2
      then
    weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 nodeExpN02704PlusPointPosition2577 nodeExpN02705PlusPointPosition2577 /
          (storedWidth i ^
          2))
      (min (max |nodeExpN02704PlusPointPosition2577| |nodeExpN02705PlusPointPosition2577|)
          (storedWidth i ^ 2) /
        (storedWidth i ^ 2)) nodeExpN02704PlusPointPosition2577 nodeExpN02705PlusPointPosition2577
  else 0


def batchC02704PlusFourthP001Input2558 : RatPair2542 :=
    ((((-(3023607753986956922918087616536546748773 *
    10^40
        + 6838956371435611813009672146364574867683)) : ℚ) /
        (4255639802077014337005541453565195299370 * 10^40
        + 4002056086575311191000441951354880000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP001Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP001Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP001ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP001Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02704PlusFourthP001Upper2558 : ℝ := ((42461873411 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC02704PlusFourthP001Exponent2558 : ℝ :=
    (((-(3023607753986956922918087616536546748773
    *
    10^40
        + 6838956371435611813009672146364574867683)) : ℝ) /
        (16623592976863337253927896302989044138 * 10^40
        + 1656258031588184809339845476372480000000))

theorem batchC02704PlusFourthP001ExpBound2558 :
    Real.exp batchC02704PlusFourthP001Exponent2558 ≤ batchC02704PlusFourthP001ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP001Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP001Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP001Input2558 8).1 =
      batchC02704PlusFourthP001Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP001Input2558 8).2 : ℝ) =
      batchC02704PlusFourthP001Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP001Input2558 8).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP001Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP001Input2558 hz 8
  rw [hc, he] at h
  have ha : (2 : ℂ)^8 * embedPair2542 batchC02704PlusFourthP001Input2558 =
      (batchC02704PlusFourthP001Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP001Input2558,
        batchC02704PlusFourthP001Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP001Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP001Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP001Center2558))).trans
  norm_num [batchC02704PlusFourthP001Error2558, batchC02704PlusFourthP001ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP001Center2558]

theorem batchC02704PlusFourthP001Bound2558 : batchC02704PlusFourthCell2558 ⟨1, by omega⟩ ≤
    batchC02704PlusFourthP001Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      batchC02704PlusFourthP001Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP001Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP001Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((6377867179716807655257936565895168 : ℝ) /
        6985282995007638018843380897109375) ((95707621777613709907473135050948608 : ℝ) /
        104779244925114570282650713456640625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP001ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP001Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((6377867179716807655257936565895168 : ℝ) /
        6985282995007638018843380897109375) ((95707621777613709907473135050948608 : ℝ) /
        104779244925114570282650713456640625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP001ExpUpper2558, batchC02704PlusFourthP001Frequency2558,
        batchC02704PlusFourthP001Upper2558]

def batchC02704PlusFourthP002Input2558 : RatPair2542 :=
    ((((-(1638859412615474757001081566597964099486 *
    10^40
        + 4331734993860018146222766991230985822547)) : ℚ) /
        (1669287828564527597956257117773350518790 * 10^40
        + 4537078954024851098857178934804480000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP002Center2558 : RatPair2542 := (((376337547449669359433 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP002Error2558 : ℝ := ((141374830781812619 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP002ExpUpper2558 : ℝ := ((827575018779227331021168882634635
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP002Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02704PlusFourthP002Upper2558 : ℝ := ((16429086928031112687007699375 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02704PlusFourthP002Exponent2558 : ℝ :=
    (((-(1638859412615474757001081566597964099486
    *
    10^40
        + 4331734993860018146222766991230985822547)) : ℝ) /
        (26082622321320743718066517465208601856 * 10^40
        + 1008391858656638298419643420856320000000))

theorem batchC02704PlusFourthP002ExpBound2558 :
    Real.exp batchC02704PlusFourthP002Exponent2558 ≤ batchC02704PlusFourthP002ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP002Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP002Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP002Input2558 6).1 =
      batchC02704PlusFourthP002Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP002Input2558 6).2 : ℝ) =
      batchC02704PlusFourthP002Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP002Input2558 6).2 =
        ((141374830781812619 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP002Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP002Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02704PlusFourthP002Input2558 =
      (batchC02704PlusFourthP002Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP002Input2558,
        batchC02704PlusFourthP002Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP002Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP002Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP002Center2558))).trans
  norm_num [batchC02704PlusFourthP002Error2558, batchC02704PlusFourthP002ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP002Center2558]

theorem batchC02704PlusFourthP002Bound2558 : batchC02704PlusFourthCell2558 ⟨2, by omega⟩ ≤
    batchC02704PlusFourthP002Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      batchC02704PlusFourthP002Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP002Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP002Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((3644495531266747231575963751940096 : ℝ) /
        5100784558061209130705753111015625) ((382830487110454839629892540203794432 : ℝ) /
        535582378596426958724104076656640625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP002ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP002Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((3644495531266747231575963751940096 : ℝ) /
        5100784558061209130705753111015625) ((382830487110454839629892540203794432 : ℝ) /
        535582378596426958724104076656640625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP002ExpUpper2558, batchC02704PlusFourthP002Frequency2558,
        batchC02704PlusFourthP002Upper2558]

def batchC02704PlusFourthP003Input2558 : RatPair2542 := ((((-((589 * 10^40
        + 7228286059281175019250523115978507539176) * 10^40
        + 7815277842486084277325670743963551945163)) : ℚ) /
        ((814 * 10^40
        + 9744163722578444334730438810112964730168) * 10^40
        + 3441337274407317054940265789521920000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP003Center2558 : RatPair2542 := (((11277108740164686308975014741 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP003Error2558 : ℝ := ((409050545734292758920081 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

noncomputable def batchC02704PlusFourthP003ExpUpper2558 : ℝ :=
    ((3099828046876358127523930668290385181585 :
    ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

noncomputable def batchC02704PlusFourthP003Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02704PlusFourthP003Upper2558 : ℝ := ((93727040964140520683963422736632257
    : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704PlusFourthP003Exponent2558 : ℝ := (((-((589 * 10^40
        + 7228286059281175019250523115978507539176) * 10^40
        + 7815277842486084277325670743963551945163)) : ℝ) /
        ((12 * 10^40
        + 7339752558165288192730163106408015073908) * 10^40
        + 8803770894912614328983441652961280000000))

theorem batchC02704PlusFourthP003ExpBound2558 :
    Real.exp batchC02704PlusFourthP003Exponent2558 ≤ batchC02704PlusFourthP003ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP003Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP003Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP003Input2558 6).1 =
      batchC02704PlusFourthP003Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP003Input2558 6).2 : ℝ) =
      batchC02704PlusFourthP003Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP003Input2558 6).2 =
        ((409050545734292758920081 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP003Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP003Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02704PlusFourthP003Input2558 =
      (batchC02704PlusFourthP003Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP003Input2558,
        batchC02704PlusFourthP003Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP003Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP003Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP003Center2558))).trans
  norm_num [batchC02704PlusFourthP003Error2558, batchC02704PlusFourthP003ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP003Center2558]

theorem batchC02704PlusFourthP003Bound2558 : batchC02704PlusFourthCell2558 ⟨3, by omega⟩ ≤
    batchC02704PlusFourthP003Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      batchC02704PlusFourthP003Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP003Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP003Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((174935785500803867115646260093124608 : ℝ) /
        304598329940554508493939872216796875) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP003ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP003Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((174935785500803867115646260093124608 : ℝ) /
        304598329940554508493939872216796875) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP003ExpUpper2558, batchC02704PlusFourthP003Frequency2558,
        batchC02704PlusFourthP003Upper2558]

def batchC02704PlusFourthP004Input2558 : RatPair2542 := ((((-((18 * 10^40
        + 6932674971925147917508549558213400347396) * 10^40
        + 486924668160436812400090012701117804803)) : ℚ) /
        ((29 * 10^40
        + 8124102735490015127204802135842261854359) * 10^40
        + 5708748117108631204001767805419520000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP004Center2558 : RatPair2542 := (((5452605262130208024441889398043 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP004Error2558 : ℝ := ((179572330223621522694958201 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

noncomputable def batchC02704PlusFourthP004ExpUpper2558 : ℝ := (((149 * 10^40
        + 8800721846192228126229975112326624668793) : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

noncomputable def batchC02704PlusFourthP004Frequency2558 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def batchC02704PlusFourthP004Upper2558 : ℝ :=
    ((6365151745306550995858033732895247095 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02704PlusFourthP004Exponent2558 : ℝ := (((-((18 * 10^40
        + 6932674971925147917508549558213400347396) * 10^40
        + 486924668160436812400090012701117804803)) : ℝ) /
        (4658189105242031486362575033372535341474 * 10^40
        + 3682949189329822362562527621959680000000))

theorem batchC02704PlusFourthP004ExpBound2558 :
    Real.exp batchC02704PlusFourthP004Exponent2558 ≤ batchC02704PlusFourthP004ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP004Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP004Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP004Input2558 6).1 =
      batchC02704PlusFourthP004Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP004Input2558 6).2 : ℝ) =
      batchC02704PlusFourthP004Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP004Input2558 6).2 =
        ((179572330223621522694958201 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP004Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP004Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02704PlusFourthP004Input2558 =
      (batchC02704PlusFourthP004Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP004Input2558,
        batchC02704PlusFourthP004Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP004Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP004Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP004Center2558))).trans
  norm_num [batchC02704PlusFourthP004Error2558, batchC02704PlusFourthP004ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP004Center2558]

theorem batchC02704PlusFourthP004Bound2558 : batchC02704PlusFourthCell2558 ⟨4, by omega⟩ ≤
    batchC02704PlusFourthP004Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      batchC02704PlusFourthP004Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP004Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP004Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((25511468718867230621031746263580672 : ℝ) /
        54086425609737808813990931158359375) ((382830487110454839629892540203794432 : ℝ) /
        811296384146067132209863967375390625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP004ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP004Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((25511468718867230621031746263580672 : ℝ) /
        54086425609737808813990931158359375) ((382830487110454839629892540203794432 : ℝ) /
        811296384146067132209863967375390625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP004ExpUpper2558, batchC02704PlusFourthP004Frequency2558,
        batchC02704PlusFourthP004Upper2558]

def batchC02704PlusFourthP006Input2558 : RatPair2542 := ((((-1052182359368453146349943998425413) :
    ℚ) /
        1771445797272420243763363840000000),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP006Center2558 : RatPair2542 := (((700265187724743 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP006Error2558 : ℝ := ((1278008009571 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02704PlusFourthP006ExpUpper2558 : ℝ := ((769949716430099667769271139 : ℝ)
    /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

noncomputable def batchC02704PlusFourthP006Frequency2558 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02704PlusFourthP006Upper2558 : ℝ := ((41352370709325389241889 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704PlusFourthP006Exponent2558 : ℝ :=
    (((-1052182359368453146349943998425413) : ℝ) /
        13839420291190783154401280000000)

theorem batchC02704PlusFourthP006ExpBound2558 :
    Real.exp batchC02704PlusFourthP006Exponent2558 ≤ batchC02704PlusFourthP006ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP006Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP006Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP006Input2558 7).1 =
      batchC02704PlusFourthP006Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP006Input2558 7).2 : ℝ) =
      batchC02704PlusFourthP006Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP006Input2558 7).2 =
        ((1278008009571 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP006Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP006Input2558 hz 7
  rw [hc, he] at h
  have ha : (2 : ℂ)^7 * embedPair2542 batchC02704PlusFourthP006Input2558 =
      (batchC02704PlusFourthP006Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP006Input2558,
        batchC02704PlusFourthP006Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP006Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP006Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP006Center2558))).trans
  norm_num [batchC02704PlusFourthP006Error2558, batchC02704PlusFourthP006ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP006Center2558]

theorem batchC02704PlusFourthP006Bound2558 : batchC02704PlusFourthCell2558 ⟨6, by omega⟩ ≤
    batchC02704PlusFourthP006Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      batchC02704PlusFourthP006Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP006Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP006Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) ((31653888483 : ℝ) /
        40960000000) ((9895936151 : ℝ) /
        12800000000) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP006ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP006Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) ((31653888483 : ℝ) /
        40960000000) ((9895936151 : ℝ) /
        12800000000) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP006ExpUpper2558, batchC02704PlusFourthP006Frequency2558,
        batchC02704PlusFourthP006Upper2558]

def batchC02704PlusFourthP007Input2558 : RatPair2542 := ((((-((589 * 10^40
        + 7228286059281175019250523115978507539176) * 10^40
        + 7815277842486084277325670743963551945163)) : ℚ) /
        ((814 * 10^40
        + 9744163722578444334730438810112964730168) * 10^40
        + 3441337274407317054940265789521920000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP007Center2558 : RatPair2542 := (((11277108740164686308975014741 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP007Error2558 : ℝ := ((409050545734292758920081 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

noncomputable def batchC02704PlusFourthP007ExpUpper2558 : ℝ :=
    ((3099828046876358127523930668290385181585 :
    ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

noncomputable def batchC02704PlusFourthP007Frequency2558 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def batchC02704PlusFourthP007Upper2558 : ℝ := ((606605768736084063537758679778481 :
    ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704PlusFourthP007Exponent2558 : ℝ := (((-((589 * 10^40
        + 7228286059281175019250523115978507539176) * 10^40
        + 7815277842486084277325670743963551945163)) : ℝ) /
        ((12 * 10^40
        + 7339752558165288192730163106408015073908) * 10^40
        + 8803770894912614328983441652961280000000))

theorem batchC02704PlusFourthP007ExpBound2558 :
    Real.exp batchC02704PlusFourthP007Exponent2558 ≤ batchC02704PlusFourthP007ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP007Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP007Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP007Input2558 6).1 =
      batchC02704PlusFourthP007Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP007Input2558 6).2 : ℝ) =
      batchC02704PlusFourthP007Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP007Input2558 6).2 =
        ((409050545734292758920081 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP007Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP007Input2558 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 batchC02704PlusFourthP007Input2558 =
      (batchC02704PlusFourthP007Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP007Input2558,
        batchC02704PlusFourthP007Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP007Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP007Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP007Center2558))).trans
  norm_num [batchC02704PlusFourthP007Error2558, batchC02704PlusFourthP007ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP007Center2558]

theorem batchC02704PlusFourthP007Bound2558 : batchC02704PlusFourthCell2558 ⟨7, by omega⟩ ≤
    batchC02704PlusFourthP007Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      batchC02704PlusFourthP007Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP007Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP007Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((174935785500803867115646260093124608 : ℝ) /
        304598329940554508493939872216796875) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP007ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP007Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((174935785500803867115646260093124608 : ℝ) /
        304598329940554508493939872216796875) ((6125287793767277434078280643260710912 : ℝ) /
        10660941547919407797287895527587890625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP007ExpUpper2558, batchC02704PlusFourthP007Frequency2558,
        batchC02704PlusFourthP007Upper2558]

def batchC02704PlusFourthP008Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP008Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP008Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP008ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP008Frequency2558 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def batchC02704PlusFourthP008Upper2558 : ℝ := ((120954110126371055347769 : ℝ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968))

noncomputable def batchC02704PlusFourthP008Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP008ExpBound2558 :
    Real.exp batchC02704PlusFourthP008Exponent2558 ≤ batchC02704PlusFourthP008ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP008Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP008Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP008Input2558 13).1 =
      batchC02704PlusFourthP008Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP008Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP008Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP008Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP008Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP008Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP008Input2558 =
      (batchC02704PlusFourthP008Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP008Input2558,
        batchC02704PlusFourthP008Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP008Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP008Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP008Center2558))).trans
  norm_num [batchC02704PlusFourthP008Error2558, batchC02704PlusFourthP008ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP008Center2558]

theorem batchC02704PlusFourthP008Bound2558 : batchC02704PlusFourthCell2558 ⟨8, by omega⟩ ≤
    batchC02704PlusFourthP008Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      batchC02704PlusFourthP008Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP008Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP008Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP008ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP008Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP008ExpUpper2558, batchC02704PlusFourthP008Frequency2558,
        batchC02704PlusFourthP008Upper2558]

def batchC02704PlusFourthP009Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP009Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP009Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP009ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP009Frequency2558 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def batchC02704PlusFourthP009Upper2558 : ℝ := ((3870619510604789013838761 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704PlusFourthP009Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP009ExpBound2558 :
    Real.exp batchC02704PlusFourthP009Exponent2558 ≤ batchC02704PlusFourthP009ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP009Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP009Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP009Input2558 13).1 =
      batchC02704PlusFourthP009Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP009Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP009Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP009Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP009Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP009Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP009Input2558 =
      (batchC02704PlusFourthP009Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP009Input2558,
        batchC02704PlusFourthP009Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP009Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP009Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP009Center2558))).trans
  norm_num [batchC02704PlusFourthP009Error2558, batchC02704PlusFourthP009ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP009Center2558]

theorem batchC02704PlusFourthP009Bound2558 : batchC02704PlusFourthCell2558 ⟨9, by omega⟩ ≤
    batchC02704PlusFourthP009Upper2558 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      batchC02704PlusFourthP009Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP009Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP009Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP009ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP009Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP009ExpUpper2558, batchC02704PlusFourthP009Frequency2558,
        batchC02704PlusFourthP009Upper2558]

def batchC02704PlusFourthP010Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP010Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP010Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP010ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP010Frequency2558 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def batchC02704PlusFourthP010Upper2558 : ℝ := ((1935335239204959190269203 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02704PlusFourthP010Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP010ExpBound2558 :
    Real.exp batchC02704PlusFourthP010Exponent2558 ≤ batchC02704PlusFourthP010ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP010Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP010Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP010Input2558 13).1 =
      batchC02704PlusFourthP010Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP010Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP010Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP010Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP010Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP010Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP010Input2558 =
      (batchC02704PlusFourthP010Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP010Input2558,
        batchC02704PlusFourthP010Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP010Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP010Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP010Center2558))).trans
  norm_num [batchC02704PlusFourthP010Error2558, batchC02704PlusFourthP010ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP010Center2558]

theorem batchC02704PlusFourthP010Bound2558 : batchC02704PlusFourthCell2558 ⟨10, by omega⟩ ≤
    batchC02704PlusFourthP010Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      batchC02704PlusFourthP010Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP010Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP010Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP010ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP010Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP010ExpUpper2558, batchC02704PlusFourthP010Frequency2558,
        batchC02704PlusFourthP010Upper2558]

def batchC02704PlusFourthP011Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP011Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP011Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP011ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP011Frequency2558 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def batchC02704PlusFourthP011Upper2558 : ℝ := ((967676115598543204657381 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02704PlusFourthP011Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP011ExpBound2558 :
    Real.exp batchC02704PlusFourthP011Exponent2558 ≤ batchC02704PlusFourthP011ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP011Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP011Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP011Input2558 13).1 =
      batchC02704PlusFourthP011Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP011Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP011Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP011Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP011Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP011Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP011Input2558 =
      (batchC02704PlusFourthP011Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP011Input2558,
        batchC02704PlusFourthP011Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP011Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP011Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP011Center2558))).trans
  norm_num [batchC02704PlusFourthP011Error2558, batchC02704PlusFourthP011ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP011Center2558]

theorem batchC02704PlusFourthP011Bound2558 : batchC02704PlusFourthCell2558 ⟨11, by omega⟩ ≤
    batchC02704PlusFourthP011Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      batchC02704PlusFourthP011Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP011Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP011Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP011ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP011Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP011ExpUpper2558, batchC02704PlusFourthP011Frequency2558,
        batchC02704PlusFourthP011Upper2558]

def batchC02704PlusFourthP012Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP012Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP012Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP012ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP012Frequency2558 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def batchC02704PlusFourthP012Upper2558 : ℝ := ((3870739662853747186434707 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704PlusFourthP012Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP012ExpBound2558 :
    Real.exp batchC02704PlusFourthP012Exponent2558 ≤ batchC02704PlusFourthP012ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP012Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP012Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP012Input2558 13).1 =
      batchC02704PlusFourthP012Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP012Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP012Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP012Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP012Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP012Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP012Input2558 =
      (batchC02704PlusFourthP012Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP012Input2558,
        batchC02704PlusFourthP012Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP012Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP012Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP012Center2558))).trans
  norm_num [batchC02704PlusFourthP012Error2558, batchC02704PlusFourthP012ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP012Center2558]

theorem batchC02704PlusFourthP012Bound2558 : batchC02704PlusFourthCell2558 ⟨12, by omega⟩ ≤
    batchC02704PlusFourthP012Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      batchC02704PlusFourthP012Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP012Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP012Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP012ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP012Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP012ExpUpper2558, batchC02704PlusFourthP012Frequency2558,
        batchC02704PlusFourthP012Upper2558]

def batchC02704PlusFourthP013Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP013Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP013Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP013ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP013Frequency2558 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def batchC02704PlusFourthP013Upper2558 : ℝ := ((1935385870748197386101557 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02704PlusFourthP013Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP013ExpBound2558 :
    Real.exp batchC02704PlusFourthP013Exponent2558 ≤ batchC02704PlusFourthP013ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP013Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP013Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP013Input2558 13).1 =
      batchC02704PlusFourthP013Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP013Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP013Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP013Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP013Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP013Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP013Input2558 =
      (batchC02704PlusFourthP013Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP013Input2558,
        batchC02704PlusFourthP013Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP013Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP013Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP013Center2558))).trans
  norm_num [batchC02704PlusFourthP013Error2558, batchC02704PlusFourthP013ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP013Center2558]

theorem batchC02704PlusFourthP013Bound2558 : batchC02704PlusFourthCell2558 ⟨13, by omega⟩ ≤
    batchC02704PlusFourthP013Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      batchC02704PlusFourthP013Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP013Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP013Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP013ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP013Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP013ExpUpper2558, batchC02704PlusFourthP013Frequency2558,
        batchC02704PlusFourthP013Upper2558]

def batchC02704PlusFourthP014Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP014Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP014Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP014ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP014Frequency2558 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def batchC02704PlusFourthP014Upper2558 : ℝ := ((967707795469994190649663 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02704PlusFourthP014Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP014ExpBound2558 :
    Real.exp batchC02704PlusFourthP014Exponent2558 ≤ batchC02704PlusFourthP014ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP014Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP014Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP014Input2558 13).1 =
      batchC02704PlusFourthP014Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP014Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP014Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP014Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP014Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP014Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP014Input2558 =
      (batchC02704PlusFourthP014Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP014Input2558,
        batchC02704PlusFourthP014Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP014Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP014Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP014Center2558))).trans
  norm_num [batchC02704PlusFourthP014Error2558, batchC02704PlusFourthP014ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP014Center2558]

theorem batchC02704PlusFourthP014Bound2558 : batchC02704PlusFourthCell2558 ⟨14, by omega⟩ ≤
    batchC02704PlusFourthP014Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      batchC02704PlusFourthP014Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP014Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP014Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP014ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP014Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP014ExpUpper2558, batchC02704PlusFourthP014Frequency2558,
        batchC02704PlusFourthP014Upper2558]

def batchC02704PlusFourthP015Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP015Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP015Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP015ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP015Frequency2558 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def batchC02704PlusFourthP015Upper2558 : ℝ := ((967718443095214099583807 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02704PlusFourthP015Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP015ExpBound2558 :
    Real.exp batchC02704PlusFourthP015Exponent2558 ≤ batchC02704PlusFourthP015ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP015Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP015Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP015Input2558 13).1 =
      batchC02704PlusFourthP015Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP015Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP015Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP015Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP015Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP015Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP015Input2558 =
      (batchC02704PlusFourthP015Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP015Input2558,
        batchC02704PlusFourthP015Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP015Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP015Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP015Center2558))).trans
  norm_num [batchC02704PlusFourthP015Error2558, batchC02704PlusFourthP015ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP015Center2558]

theorem batchC02704PlusFourthP015Bound2558 : batchC02704PlusFourthCell2558 ⟨15, by omega⟩ ≤
    batchC02704PlusFourthP015Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      batchC02704PlusFourthP015Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP015Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP015Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP015ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP015Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP015ExpUpper2558, batchC02704PlusFourthP015Frequency2558,
        batchC02704PlusFourthP015Upper2558]

def batchC02704PlusFourthP016Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP016Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP016Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP016ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP016Frequency2558 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def batchC02704PlusFourthP016Upper2558 : ℝ := ((3870904552154991645377839 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704PlusFourthP016Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP016ExpBound2558 :
    Real.exp batchC02704PlusFourthP016Exponent2558 ≤ batchC02704PlusFourthP016ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP016Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP016Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP016Input2558 13).1 =
      batchC02704PlusFourthP016Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP016Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP016Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP016Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP016Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP016Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP016Input2558 =
      (batchC02704PlusFourthP016Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP016Input2558,
        batchC02704PlusFourthP016Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP016Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP016Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP016Center2558))).trans
  norm_num [batchC02704PlusFourthP016Error2558, batchC02704PlusFourthP016ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP016Center2558]

theorem batchC02704PlusFourthP016Bound2558 : batchC02704PlusFourthCell2558 ⟨16, by omega⟩ ≤
    batchC02704PlusFourthP016Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      batchC02704PlusFourthP016Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP016Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP016Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP016ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP016Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP016ExpUpper2558, batchC02704PlusFourthP016Frequency2558,
        batchC02704PlusFourthP016Upper2558]

def batchC02704PlusFourthP017Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP017Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP017Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP017ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP017Frequency2558 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def batchC02704PlusFourthP017Upper2558 : ℝ := ((241935271318342328517689 : ℝ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936))

noncomputable def batchC02704PlusFourthP017Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP017ExpBound2558 :
    Real.exp batchC02704PlusFourthP017Exponent2558 ≤ batchC02704PlusFourthP017ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP017Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP017Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP017Input2558 13).1 =
      batchC02704PlusFourthP017Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP017Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP017Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP017Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP017Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP017Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP017Input2558 =
      (batchC02704PlusFourthP017Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP017Input2558,
        batchC02704PlusFourthP017Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP017Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP017Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP017Center2558))).trans
  norm_num [batchC02704PlusFourthP017Error2558, batchC02704PlusFourthP017ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP017Center2558]

theorem batchC02704PlusFourthP017Bound2558 : batchC02704PlusFourthCell2558 ⟨17, by omega⟩ ≤
    batchC02704PlusFourthP017Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      batchC02704PlusFourthP017Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP017Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP017Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP017ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP017Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP017ExpUpper2558, batchC02704PlusFourthP017Frequency2558,
        batchC02704PlusFourthP017Upper2558]

def batchC02704PlusFourthP018Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP018Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP018Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP018ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP018Frequency2558 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def batchC02704PlusFourthP018Upper2558 : ℝ := ((3870986946376885678543779 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704PlusFourthP018Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP018ExpBound2558 :
    Real.exp batchC02704PlusFourthP018Exponent2558 ≤ batchC02704PlusFourthP018ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP018Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP018Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP018Input2558 13).1 =
      batchC02704PlusFourthP018Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP018Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP018Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP018Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP018Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP018Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP018Input2558 =
      (batchC02704PlusFourthP018Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP018Input2558,
        batchC02704PlusFourthP018Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP018Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP018Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP018Center2558))).trans
  norm_num [batchC02704PlusFourthP018Error2558, batchC02704PlusFourthP018ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP018Center2558]

theorem batchC02704PlusFourthP018Bound2558 : batchC02704PlusFourthCell2558 ⟨18, by omega⟩ ≤
    batchC02704PlusFourthP018Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      batchC02704PlusFourthP018Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP018Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP018Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP018ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP018Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP018ExpUpper2558, batchC02704PlusFourthP018Frequency2558,
        batchC02704PlusFourthP018Upper2558]

def batchC02704PlusFourthP019Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP019Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP019Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP019ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP019Frequency2558 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def batchC02704PlusFourthP019Upper2558 : ℝ := ((1935513900364944448776163 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02704PlusFourthP019Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP019ExpBound2558 :
    Real.exp batchC02704PlusFourthP019Exponent2558 ≤ batchC02704PlusFourthP019ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP019Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP019Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP019Input2558 13).1 =
      batchC02704PlusFourthP019Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP019Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP019Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP019Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP019Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP019Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP019Input2558 =
      (batchC02704PlusFourthP019Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP019Input2558,
        batchC02704PlusFourthP019Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP019Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP019Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP019Center2558))).trans
  norm_num [batchC02704PlusFourthP019Error2558, batchC02704PlusFourthP019ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP019Center2558]

theorem batchC02704PlusFourthP019Bound2558 : batchC02704PlusFourthCell2558 ⟨19, by omega⟩ ≤
    batchC02704PlusFourthP019Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      batchC02704PlusFourthP019Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP019Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP019Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP019ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP019Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP019ExpUpper2558, batchC02704PlusFourthP019Frequency2558,
        batchC02704PlusFourthP019Upper2558]

def batchC02704PlusFourthP020Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP020Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP020Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP020ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP020Frequency2558 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def batchC02704PlusFourthP020Upper2558 : ℝ := ((3871072227191669323847077 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704PlusFourthP020Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP020ExpBound2558 :
    Real.exp batchC02704PlusFourthP020Exponent2558 ≤ batchC02704PlusFourthP020ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP020Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP020Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP020Input2558 13).1 =
      batchC02704PlusFourthP020Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP020Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP020Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP020Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP020Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP020Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP020Input2558 =
      (batchC02704PlusFourthP020Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP020Input2558,
        batchC02704PlusFourthP020Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP020Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP020Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP020Center2558))).trans
  norm_num [batchC02704PlusFourthP020Error2558, batchC02704PlusFourthP020ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP020Center2558]

theorem batchC02704PlusFourthP020Bound2558 : batchC02704PlusFourthCell2558 ⟨20, by omega⟩ ≤
    batchC02704PlusFourthP020Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      batchC02704PlusFourthP020Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP020Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP020Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP020ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP020Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP020ExpUpper2558, batchC02704PlusFourthP020Frequency2558,
        batchC02704PlusFourthP020Upper2558]

def batchC02704PlusFourthP021Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP021Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP021Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP021ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP021Frequency2558 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def batchC02704PlusFourthP021Upper2558 : ℝ := ((3871109303272587756184355 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704PlusFourthP021Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP021ExpBound2558 :
    Real.exp batchC02704PlusFourthP021Exponent2558 ≤ batchC02704PlusFourthP021ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP021Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP021Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP021Input2558 13).1 =
      batchC02704PlusFourthP021Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP021Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP021Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP021Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP021Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP021Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP021Input2558 =
      (batchC02704PlusFourthP021Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP021Input2558,
        batchC02704PlusFourthP021Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP021Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP021Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP021Center2558))).trans
  norm_num [batchC02704PlusFourthP021Error2558, batchC02704PlusFourthP021ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP021Center2558]

theorem batchC02704PlusFourthP021Bound2558 : batchC02704PlusFourthCell2558 ⟨21, by omega⟩ ≤
    batchC02704PlusFourthP021Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      batchC02704PlusFourthP021Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP021Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP021Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP021ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP021Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP021ExpUpper2558, batchC02704PlusFourthP021Frequency2558,
        batchC02704PlusFourthP021Upper2558]

def batchC02704PlusFourthP022Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP022Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP022Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP022ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP022Frequency2558 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def batchC02704PlusFourthP022Upper2558 : ℝ := ((3871128280333083228798205 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704PlusFourthP022Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP022ExpBound2558 :
    Real.exp batchC02704PlusFourthP022Exponent2558 ≤ batchC02704PlusFourthP022ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP022Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP022Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP022Input2558 13).1 =
      batchC02704PlusFourthP022Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP022Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP022Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP022Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP022Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP022Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP022Input2558 =
      (batchC02704PlusFourthP022Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP022Input2558,
        batchC02704PlusFourthP022Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP022Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP022Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP022Center2558))).trans
  norm_num [batchC02704PlusFourthP022Error2558, batchC02704PlusFourthP022ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP022Center2558]

theorem batchC02704PlusFourthP022Bound2558 : batchC02704PlusFourthCell2558 ⟨22, by omega⟩ ≤
    batchC02704PlusFourthP022Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      batchC02704PlusFourthP022Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP022Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP022Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP022ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP022Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP022ExpUpper2558, batchC02704PlusFourthP022Frequency2558,
        batchC02704PlusFourthP022Upper2558]

def batchC02704PlusFourthP023Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP023Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP023Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP023ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP023Frequency2558 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def batchC02704PlusFourthP023Upper2558 : ℝ := ((3871182995286712877289067 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704PlusFourthP023Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP023ExpBound2558 :
    Real.exp batchC02704PlusFourthP023Exponent2558 ≤ batchC02704PlusFourthP023ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP023Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP023Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP023Input2558 13).1 =
      batchC02704PlusFourthP023Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP023Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP023Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP023Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP023Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP023Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP023Input2558 =
      (batchC02704PlusFourthP023Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP023Input2558,
        batchC02704PlusFourthP023Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP023Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP023Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP023Center2558))).trans
  norm_num [batchC02704PlusFourthP023Error2558, batchC02704PlusFourthP023ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP023Center2558]

theorem batchC02704PlusFourthP023Bound2558 : batchC02704PlusFourthCell2558 ⟨23, by omega⟩ ≤
    batchC02704PlusFourthP023Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      batchC02704PlusFourthP023Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP023Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP023Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP023ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP023Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP023ExpUpper2558, batchC02704PlusFourthP023Frequency2558,
        batchC02704PlusFourthP023Upper2558]

def batchC02704PlusFourthP024Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP024Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP024Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP024ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP024Frequency2558 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def batchC02704PlusFourthP024Upper2558 : ℝ := ((483901017541733307533591 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC02704PlusFourthP024Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP024ExpBound2558 :
    Real.exp batchC02704PlusFourthP024Exponent2558 ≤ batchC02704PlusFourthP024ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP024Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP024Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP024Input2558 13).1 =
      batchC02704PlusFourthP024Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP024Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP024Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP024Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP024Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP024Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP024Input2558 =
      (batchC02704PlusFourthP024Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP024Input2558,
        batchC02704PlusFourthP024Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP024Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP024Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP024Center2558))).trans
  norm_num [batchC02704PlusFourthP024Error2558, batchC02704PlusFourthP024ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP024Center2558]

theorem batchC02704PlusFourthP024Bound2558 : batchC02704PlusFourthCell2558 ⟨24, by omega⟩ ≤
    batchC02704PlusFourthP024Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      batchC02704PlusFourthP024Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP024Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP024Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP024ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP024Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP024ExpUpper2558, batchC02704PlusFourthP024Frequency2558,
        batchC02704PlusFourthP024Upper2558]

def batchC02704PlusFourthP025Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP025Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP025Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP025ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP025Frequency2558 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def batchC02704PlusFourthP025Upper2558 : ℝ := ((967809916960286156306765 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def batchC02704PlusFourthP025Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP025ExpBound2558 :
    Real.exp batchC02704PlusFourthP025Exponent2558 ≤ batchC02704PlusFourthP025ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP025Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP025Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP025Input2558 13).1 =
      batchC02704PlusFourthP025Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP025Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP025Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP025Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP025Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP025Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP025Input2558 =
      (batchC02704PlusFourthP025Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP025Input2558,
        batchC02704PlusFourthP025Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP025Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP025Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP025Center2558))).trans
  norm_num [batchC02704PlusFourthP025Error2558, batchC02704PlusFourthP025ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP025Center2558]

theorem batchC02704PlusFourthP025Bound2558 : batchC02704PlusFourthCell2558 ⟨25, by omega⟩ ≤
    batchC02704PlusFourthP025Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      batchC02704PlusFourthP025Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP025Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP025Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP025ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP025Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP025ExpUpper2558, batchC02704PlusFourthP025Frequency2558,
        batchC02704PlusFourthP025Upper2558]

def batchC02704PlusFourthP026Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP026Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP026Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP026ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP026Frequency2558 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def batchC02704PlusFourthP026Upper2558 : ℝ := ((3871271887933041351091371 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def batchC02704PlusFourthP026Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP026ExpBound2558 :
    Real.exp batchC02704PlusFourthP026Exponent2558 ≤ batchC02704PlusFourthP026ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP026Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP026Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP026Input2558 13).1 =
      batchC02704PlusFourthP026Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP026Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP026Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP026Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP026Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP026Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP026Input2558 =
      (batchC02704PlusFourthP026Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP026Input2558,
        batchC02704PlusFourthP026Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP026Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP026Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP026Center2558))).trans
  norm_num [batchC02704PlusFourthP026Error2558, batchC02704PlusFourthP026ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP026Center2558]

theorem batchC02704PlusFourthP026Bound2558 : batchC02704PlusFourthCell2558 ⟨26, by omega⟩ ≤
    batchC02704PlusFourthP026Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      batchC02704PlusFourthP026Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP026Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP026Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP026ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP026Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP026ExpUpper2558, batchC02704PlusFourthP026Frequency2558,
        batchC02704PlusFourthP026Upper2558]

def batchC02704PlusFourthP027Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP027Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP027Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP027ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP027Frequency2558 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def batchC02704PlusFourthP027Upper2558 : ℝ := ((1935659191513995017591871 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02704PlusFourthP027Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP027ExpBound2558 :
    Real.exp batchC02704PlusFourthP027Exponent2558 ≤ batchC02704PlusFourthP027ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP027Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP027Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP027Input2558 13).1 =
      batchC02704PlusFourthP027Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP027Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP027Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP027Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP027Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP027Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP027Input2558 =
      (batchC02704PlusFourthP027Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP027Input2558,
        batchC02704PlusFourthP027Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP027Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP027Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP027Center2558))).trans
  norm_num [batchC02704PlusFourthP027Error2558, batchC02704PlusFourthP027ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP027Center2558]

theorem batchC02704PlusFourthP027Bound2558 : batchC02704PlusFourthCell2558 ⟨27, by omega⟩ ≤
    batchC02704PlusFourthP027Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      batchC02704PlusFourthP027Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP027Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP027Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP027ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP027Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP027ExpUpper2558, batchC02704PlusFourthP027Frequency2558,
        batchC02704PlusFourthP027Upper2558]

def batchC02704PlusFourthP028Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP028Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP028Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP028ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP028Frequency2558 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def batchC02704PlusFourthP028Upper2558 : ℝ := ((483917098902537606659923 : ℝ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))

noncomputable def batchC02704PlusFourthP028Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP028ExpBound2558 :
    Real.exp batchC02704PlusFourthP028Exponent2558 ≤ batchC02704PlusFourthP028ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP028Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP028Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP028Input2558 13).1 =
      batchC02704PlusFourthP028Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP028Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP028Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP028Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP028Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP028Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP028Input2558 =
      (batchC02704PlusFourthP028Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP028Input2558,
        batchC02704PlusFourthP028Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP028Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP028Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP028Center2558))).trans
  norm_num [batchC02704PlusFourthP028Error2558, batchC02704PlusFourthP028ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP028Center2558]

theorem batchC02704PlusFourthP028Bound2558 : batchC02704PlusFourthCell2558 ⟨28, by omega⟩ ≤
    batchC02704PlusFourthP028Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      batchC02704PlusFourthP028Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP028Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP028Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP028ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP028Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP028ExpUpper2558, batchC02704PlusFourthP028Frequency2558,
        batchC02704PlusFourthP028Upper2558]

def batchC02704PlusFourthP029Input2558 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusFourthP029Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusFourthP029Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP029ExpUpper2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def batchC02704PlusFourthP029Frequency2558 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def batchC02704PlusFourthP029Upper2558 : ℝ := ((1935682408332932262487215 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def batchC02704PlusFourthP029Exponent2558 : ℝ := (((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℝ) /
        ((1 * 10^40
        + 2729529535195401584731944887936195591671) * 10^40
        + 4234175053623929062188640995102720000000))

theorem batchC02704PlusFourthP029ExpBound2558 :
    Real.exp batchC02704PlusFourthP029Exponent2558 ≤ batchC02704PlusFourthP029ExpUpper2558 := by
  have hz : ‖embedPair2542 batchC02704PlusFourthP029Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusFourthP029Input2558]
  have hc : (compactExp2547 batchC02704PlusFourthP029Input2558 13).1 =
      batchC02704PlusFourthP029Center2558 := by decide +kernel
  have he : ((compactExp2547 batchC02704PlusFourthP029Input2558 13).2 : ℝ) =
      batchC02704PlusFourthP029Error2558 := by
    have hq : (compactExp2547 batchC02704PlusFourthP029Input2558 13).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [batchC02704PlusFourthP029Error2558]
  have h := compactExp_error2547 batchC02704PlusFourthP029Input2558 hz 13
  rw [hc, he] at h
  have ha : (2 : ℂ)^13 * embedPair2542 batchC02704PlusFourthP029Input2558 =
      (batchC02704PlusFourthP029Exponent2558 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, batchC02704PlusFourthP029Input2558,
        batchC02704PlusFourthP029Exponent2558,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (batchC02704PlusFourthP029Exponent2558 : ℂ)) (embedPair2542
        batchC02704PlusFourthP029Center2558) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542
      batchC02704PlusFourthP029Center2558))).trans
  norm_num [batchC02704PlusFourthP029Error2558, batchC02704PlusFourthP029ExpUpper2558,
      pairMagnitude2542,
      batchC02704PlusFourthP029Center2558]

theorem batchC02704PlusFourthP029Bound2558 : batchC02704PlusFourthCell2558 ⟨29, by omega⟩ ≤
    batchC02704PlusFourthP029Upper2558 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      batchC02704PlusFourthP029Frequency2558 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [batchC02704PlusFourthP029Frequency2558])
    norm_num [weightedLambda2537, nodeModulation2541, batchC02704PlusFourthP029Frequency2558,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000)
    (by norm_num) (by norm_num) hf
    (by convert batchC02704PlusFourthP029ExpBound2558 using 1; norm_num
        [batchC02704PlusFourthP029Exponent2558])
  have hid : batchC02704PlusFourthCell2558 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((1224550498505627069809523820651872256 : ℝ) /
        1227085781020926382656182059794453125) ((6125287793767277434078280643260710912 : ℝ) /
        6135428905104631913280910298972265625) (((-9895936151) : ℝ) /
        3200000000) (((-31653888483) : ℝ) /
        10240000000) := by
    norm_num [batchC02704PlusFourthCell2558, cellNearAbs2538, nodeExpN02704PlusPointPosition2577,
      nodeExpN02705PlusPointPosition2577, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    batchC02704PlusFourthP029ExpUpper2558, batchC02704PlusFourthP029Frequency2558,
        batchC02704PlusFourthP029Upper2558]

noncomputable def batchC02704PlusFourthP000Upper2558 : ℝ := 0

theorem batchC02704PlusFourthP000Bound2558 :
    batchC02704PlusFourthCell2558 ⟨0, by omega⟩ ≤ batchC02704PlusFourthP000Upper2558 := by
  norm_num [batchC02704PlusFourthCell2558, batchC02704PlusFourthP000Upper2558, cellNearAbs2538,
    nodeExpN02704PlusPointPosition2577, nodeExpN02705PlusPointPosition2577, storedWidth]

noncomputable def batchC02704PlusFourthP005Upper2558 : ℝ := 0

theorem batchC02704PlusFourthP005Bound2558 :
    batchC02704PlusFourthCell2558 ⟨5, by omega⟩ ≤ batchC02704PlusFourthP005Upper2558 := by
  norm_num [batchC02704PlusFourthCell2558, batchC02704PlusFourthP005Upper2558, cellNearAbs2538,
    nodeExpN02704PlusPointPosition2577, nodeExpN02705PlusPointPosition2577, storedWidth]

noncomputable def batchC02704PlusFourthUpper2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02704PlusFourthP000Upper2558
  | 1 => batchC02704PlusFourthP001Upper2558
  | 2 => batchC02704PlusFourthP002Upper2558
  | 3 => batchC02704PlusFourthP003Upper2558
  | 4 => batchC02704PlusFourthP004Upper2558
  | 5 => batchC02704PlusFourthP005Upper2558
  | 6 => batchC02704PlusFourthP006Upper2558
  | 7 => batchC02704PlusFourthP007Upper2558
  | 8 => batchC02704PlusFourthP008Upper2558
  | 9 => batchC02704PlusFourthP009Upper2558
  | 10 => batchC02704PlusFourthP010Upper2558
  | 11 => batchC02704PlusFourthP011Upper2558
  | 12 => batchC02704PlusFourthP012Upper2558
  | 13 => batchC02704PlusFourthP013Upper2558
  | 14 => batchC02704PlusFourthP014Upper2558
  | 15 => batchC02704PlusFourthP015Upper2558
  | 16 => batchC02704PlusFourthP016Upper2558
  | 17 => batchC02704PlusFourthP017Upper2558
  | 18 => batchC02704PlusFourthP018Upper2558
  | 19 => batchC02704PlusFourthP019Upper2558
  | 20 => batchC02704PlusFourthP020Upper2558
  | 21 => batchC02704PlusFourthP021Upper2558
  | 22 => batchC02704PlusFourthP022Upper2558
  | 23 => batchC02704PlusFourthP023Upper2558
  | 24 => batchC02704PlusFourthP024Upper2558
  | 25 => batchC02704PlusFourthP025Upper2558
  | 26 => batchC02704PlusFourthP026Upper2558
  | 27 => batchC02704PlusFourthP027Upper2558
  | 28 => batchC02704PlusFourthP028Upper2558
  | 29 => batchC02704PlusFourthP029Upper2558
  | _ => 0

theorem batchC02704PlusFourthBound2558 (i : Fin 30) :
    batchC02704PlusFourthCell2558 i ≤ batchC02704PlusFourthUpper2558 i := by
  fin_cases i
  · exact batchC02704PlusFourthP000Bound2558
  · exact batchC02704PlusFourthP001Bound2558
  · exact batchC02704PlusFourthP002Bound2558
  · exact batchC02704PlusFourthP003Bound2558
  · exact batchC02704PlusFourthP004Bound2558
  · exact batchC02704PlusFourthP005Bound2558
  · exact batchC02704PlusFourthP006Bound2558
  · exact batchC02704PlusFourthP007Bound2558
  · exact batchC02704PlusFourthP008Bound2558
  · exact batchC02704PlusFourthP009Bound2558
  · exact batchC02704PlusFourthP010Bound2558
  · exact batchC02704PlusFourthP011Bound2558
  · exact batchC02704PlusFourthP012Bound2558
  · exact batchC02704PlusFourthP013Bound2558
  · exact batchC02704PlusFourthP014Bound2558
  · exact batchC02704PlusFourthP015Bound2558
  · exact batchC02704PlusFourthP016Bound2558
  · exact batchC02704PlusFourthP017Bound2558
  · exact batchC02704PlusFourthP018Bound2558
  · exact batchC02704PlusFourthP019Bound2558
  · exact batchC02704PlusFourthP020Bound2558
  · exact batchC02704PlusFourthP021Bound2558
  · exact batchC02704PlusFourthP022Bound2558
  · exact batchC02704PlusFourthP023Bound2558
  · exact batchC02704PlusFourthP024Bound2558
  · exact batchC02704PlusFourthP025Bound2558
  · exact batchC02704PlusFourthP026Bound2558
  · exact batchC02704PlusFourthP027Bound2558
  · exact batchC02704PlusFourthP028Bound2558
  · exact batchC02704PlusFourthP029Bound2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP001Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP002Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP003Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP004Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP006Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP007Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP008Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP009Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP010Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP011Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP012Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP013Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP014Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP015Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP016Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP017Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP018Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP019Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP020Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP021Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP022Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP023Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP024Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP025Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP026Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP027Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP028Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP029Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthBound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP000Bound2558
#print axioms ConnesWeilRH.Dev.batchC02704PlusFourthP005Bound2558
