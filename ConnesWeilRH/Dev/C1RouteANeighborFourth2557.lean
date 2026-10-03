import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545
import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteAKernelN02701Plus2555
import ConnesWeilRH.Dev.C1RouteANeighborRight2557

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def neighborFourthCell2557 (i : Fin 30) : ℝ :=
  if cellNearAbs2538 kernelN02701PlusPosition2555 neighborRightPosition2557 < storedWidth i ^ 2
      then
    weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
      (cellNearAbs2538 kernelN02701PlusPosition2555 neighborRightPosition2557 / (storedWidth i ^
          2))
      (min (max |kernelN02701PlusPosition2555| |neighborRightPosition2557|) (storedWidth i ^ 2) /
        (storedWidth i ^ 2)) kernelN02701PlusPosition2555 neighborRightPosition2557
  else 0


def neighborFourthP001Input2557 : RatPair2542 := ((((-((18 * 10^40
        + 8957448532075589895690199699507613126779) * 10^40
        + 8635177651224989294368066657048977169169)) : ℚ) /
        ((26 * 10^40
        + 2663852726383707666861620696384351893585) * 10^40
        + 1910567287484067509185130541875200000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP001Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP001Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP001ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP001Frequency2557 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def neighborFourthP001Upper2557 : ℝ := ((375164486795 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP001Exponent2557 : ℝ := (((-((18 * 10^40
        + 8957448532075589895690199699507613126779) * 10^40
        + 8635177651224989294368066657048977169169)) : ℝ) /
        (1026030674712436358073678205845251374584 * 10^40
        + 3171525653466734638707754416179200000000))

theorem neighborFourthP001ExpBound2557 :
    Real.exp neighborFourthP001Exponent2557 ≤ neighborFourthP001ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP001Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP001Input2557]
  have hc : (compactExp2547 neighborFourthP001Input2557 8).1 = neighborFourthP001Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP001Input2557 8).2 : ℝ) = neighborFourthP001Error2557
      := by
    have hq : (compactExp2547 neighborFourthP001Input2557 8).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP001Error2557]
  have h := compactExp_error2547 neighborFourthP001Input2557 hz 8
  rw [hc, he] at h
  have ha : (2 : ℂ)^8 * embedPair2542 neighborFourthP001Input2557 =
      (neighborFourthP001Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP001Input2557,
        neighborFourthP001Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP001Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP001Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP001Center2557))).trans
  norm_num [neighborFourthP001Error2557, neighborFourthP001ExpUpper2557, pairMagnitude2542,
      neighborFourthP001Center2557]

theorem neighborFourthP001Bound2557 : neighborFourthCell2557 ⟨1, by omega⟩ ≤
    neighborFourthP001Upper2557 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      neighborFourthP001Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP001Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP001Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((31928949980445633354893769391996928 : ℝ) /
        34926414975038190094216904485546875) ((95826464023198495143285394738511872 : ℝ) /
        104779244925114570282650713456640625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP001ExpBound2557 using 1; norm_num [neighborFourthP001Exponent2557])
  have hid : neighborFourthCell2557 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((31928949980445633354893769391996928 : ℝ) /
        34926414975038190094216904485546875) ((95826464023198495143285394738511872 : ℝ) /
        104779244925114570282650713456640625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP001ExpUpper2557, neighborFourthP001Frequency2557, neighborFourthP001Upper2557]

def neighborFourthP002Input2557 : RatPair2542 := ((((-((501 * 10^40
        + 8839822183730904454132100309844276595994) * 10^40
        + 5478704563309233690904404413326847597329)) : ℚ) /
        ((509 * 10^40
        + 8939435365147015157098542575124546527505) * 10^40
        + 1932544207214962536740522167500800000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP002Center2557 : RatPair2542 := (((80074412868439191005 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP002Error2557 : ℝ := ((30156684643502409 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

noncomputable def neighborFourthP002ExpUpper2557 : ℝ := ((176085496072370142633444898212169 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

noncomputable def neighborFourthP002Frequency2557 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def neighborFourthP002Upper2557 : ℝ := ((14171085827585487778737480175 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def neighborFourthP002Exponent2557 : ℝ := (((-((501 * 10^40
        + 8839822183730904454132100309844276595994) * 10^40
        + 5478704563309233690904404413326847597329)) : ℝ) /
        ((7 * 10^40
        + 9670928677580422111829664727736321039492) * 10^40
        + 2686446003237733789636570658867200000000))

theorem neighborFourthP002ExpBound2557 :
    Real.exp neighborFourthP002Exponent2557 ≤ neighborFourthP002ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP002Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP002Input2557]
  have hc : (compactExp2547 neighborFourthP002Input2557 6).1 = neighborFourthP002Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP002Input2557 6).2 : ℝ) = neighborFourthP002Error2557
      := by
    have hq : (compactExp2547 neighborFourthP002Input2557 6).2 =
        ((30156684643502409 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP002Error2557]
  have h := compactExp_error2547 neighborFourthP002Input2557 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 neighborFourthP002Input2557 =
      (neighborFourthP002Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP002Input2557,
        neighborFourthP002Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP002Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP002Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP002Center2557))).trans
  norm_num [neighborFourthP002Error2557, neighborFourthP002ExpUpper2557, pairMagnitude2542,
      neighborFourthP002Center2557]

theorem neighborFourthP002Bound2557 : neighborFourthCell2557 ⟨2, by omega⟩ ≤
    neighborFourthP002Upper2557 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      neighborFourthP002Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP002Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP002Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((127715799921782533419575077567987712 : ℝ) /
        178527459532142319574701358885546875) ((383305856092793980573141578954047488 : ℝ) /
        535582378596426958724104076656640625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP002ExpBound2557 using 1; norm_num [neighborFourthP002Exponent2557])
  have hid : neighborFourthCell2557 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((127715799921782533419575077567987712 : ℝ) /
        178527459532142319574701358885546875) ((383305856092793980573141578954047488 : ℝ) /
        535582378596426958724104076656640625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP002ExpUpper2557, neighborFourthP002Frequency2557, neighborFourthP002Upper2557]

def neighborFourthP003Input2557 : RatPair2542 := ((((-((10686 * 10^40
        + 5514579033133485558018445580747464399624) * 10^40
        + 6137789117471636006252046452959068041489)) : ℚ) /
        ((14750 * 10^40
        + 3272438641351937974655549942583722485628) * 10^40
        + 1435370751161707864793864342732800000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP003Center2557 : RatPair2542 := (((5327421052927345222380711195 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP003Error2557 : ℝ := ((1547288813920703326910549 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP003ExpUpper2557 : ℝ := (((1 * 10^40
        + 1715122787504555937933038864701319215189) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP003Frequency2557 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def neighborFourthP003Upper2557 : ℝ := ((88907669485178871964168491793832637 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP003Exponent2557 : ℝ := (((-((10686 * 10^40
        + 5514579033133485558018445580747464399624) * 10^40
        + 6137789117471636006252046452959068041489)) : ℝ) /
        ((230 * 10^40
        + 4738631853771124030853992967852870663837) * 10^40
        + 9397427667986901685387404130355200000000))

theorem neighborFourthP003ExpBound2557 :
    Real.exp neighborFourthP003Exponent2557 ≤ neighborFourthP003ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP003Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP003Input2557]
  have hc : (compactExp2547 neighborFourthP003Input2557 6).1 = neighborFourthP003Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP003Input2557 6).2 : ℝ) = neighborFourthP003Error2557
      := by
    have hq : (compactExp2547 neighborFourthP003Input2557 6).2 =
        ((1547288813920703326910549 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP003Error2557]
  have h := compactExp_error2547 neighborFourthP003Input2557 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 neighborFourthP003Input2557 =
      (neighborFourthP003Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP003Input2557,
        neighborFourthP003Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP003Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP003Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP003Center2557))).trans
  norm_num [neighborFourthP003Error2557, neighborFourthP003ExpUpper2557, pairMagnitude2542,
      neighborFourthP003Center2557]

theorem neighborFourthP003Bound2557 : neighborFourthCell2557 ⟨3, by omega⟩ ≤
    neighborFourthP003Upper2557 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      neighborFourthP003Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP003Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP003Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP003ExpBound2557 using 1; norm_num [neighborFourthP003Exponent2557])
  have hid : neighborFourthCell2557 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP003ExpUpper2557, neighborFourthP003Frequency2557, neighborFourthP003Upper2557]

def neighborFourthP004Input2557 : RatPair2542 := ((((-((1168 * 10^40
        + 3530673673730106098996702978531164745704) * 10^40
        + 2277384033427170932559140326412785097329)) : ℚ) /
        ((1861 * 10^40
        + 9501881354407191866361252884379948629213) * 10^40
        + 8925004825397922536740522167500800000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP004Center2557 : RatPair2542 := (((82729725218039363621007023609 : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP004Error2557 : ℝ := ((697808605951632476138097935 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP004ExpUpper2557 : ℝ := (((582 * 10^40
        + 1586869756650759515907716538745076567311) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP004Frequency2557 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def neighborFourthP004Upper2557 : ℝ := ((12382094047606107543579996845166756613 : ℝ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def neighborFourthP004Exponent2557 : ℝ := (((-((1168 * 10^40
        + 3530673673730106098996702978531164745704) * 10^40
        + 2277384033427170932559140326412785097329)) : ℝ) /
        ((29 * 10^40
        + 929716896162612372911894576318436697331) * 10^40
        + 4670703200396842539636570658867200000000))

theorem neighborFourthP004ExpBound2557 :
    Real.exp neighborFourthP004Exponent2557 ≤ neighborFourthP004ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP004Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP004Input2557]
  have hc : (compactExp2547 neighborFourthP004Input2557 6).1 = neighborFourthP004Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP004Input2557 6).2 : ℝ) = neighborFourthP004Error2557
      := by
    have hq : (compactExp2547 neighborFourthP004Input2557 6).2 =
        ((697808605951632476138097935 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP004Error2557]
  have h := compactExp_error2547 neighborFourthP004Input2557 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 neighborFourthP004Input2557 =
      (neighborFourthP004Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP004Input2557,
        neighborFourthP004Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP004Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP004Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP004Center2557))).trans
  norm_num [neighborFourthP004Error2557, neighborFourthP004ExpUpper2557, pairMagnitude2542,
      neighborFourthP004Center2557]

theorem neighborFourthP004Bound2557 : neighborFourthCell2557 ⟨4, by omega⟩ ≤
    neighborFourthP004Upper2557 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      neighborFourthP004Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP004Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP004Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((127715799921782533419575077567987712 : ℝ) /
        270432128048689044069954655791796875) ((383305856092793980573141578954047488 : ℝ) /
        811296384146067132209863967375390625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP004ExpBound2557 using 1; norm_num [neighborFourthP004Exponent2557])
  have hid : neighborFourthCell2557 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((127715799921782533419575077567987712 : ℝ) /
        270432128048689044069954655791796875) ((383305856092793980573141578954047488 : ℝ) /
        811296384146067132209863967375390625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP004ExpUpper2557, neighborFourthP004Frequency2557, neighborFourthP004Upper2557]

def neighborFourthP006Input2557 : RatPair2542 := ((((-16439531033496690691568499820795671) : ℚ) /
        27576812937084734710212198400000000),
    ((0 : ℚ) /
        1))

def neighborFourthP006Center2557 : RatPair2542 := (((1061161581669737 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP006Error2557 : ℝ := ((308762315073 : ℝ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))

noncomputable def neighborFourthP006ExpUpper2557 : ℝ := ((145844937249381220375791937 : ℝ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))

noncomputable def neighborFourthP006Frequency2557 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def neighborFourthP006Upper2557 : ℝ := ((8106809838388439180011 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def neighborFourthP006Exponent2557 : ℝ := (((-16439531033496690691568499820795671) :
    ℝ)
    /
        215443851070974489923532800000000)

theorem neighborFourthP006ExpBound2557 :
    Real.exp neighborFourthP006Exponent2557 ≤ neighborFourthP006ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP006Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP006Input2557]
  have hc : (compactExp2547 neighborFourthP006Input2557 7).1 = neighborFourthP006Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP006Input2557 7).2 : ℝ) = neighborFourthP006Error2557
      := by
    have hq : (compactExp2547 neighborFourthP006Input2557 7).2 =
        ((308762315073 : ℚ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP006Error2557]
  have h := compactExp_error2547 neighborFourthP006Input2557 hz 7
  rw [hc, he] at h
  have ha : (2 : ℂ)^7 * embedPair2542 neighborFourthP006Input2557 =
      (neighborFourthP006Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP006Input2557,
        neighborFourthP006Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP006Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP006Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP006Center2557))).trans
  norm_num [neighborFourthP006Error2557, neighborFourthP006ExpUpper2557, pairMagnitude2542,
      neighborFourthP006Center2557]

theorem neighborFourthP006Bound2557 : neighborFourthCell2557 ⟨6, by omega⟩ ≤
    neighborFourthP006Upper2557 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      neighborFourthP006Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP006Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP006Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) ((79233025209 : ℝ) /
        102400000000) ((158531586419 : ℝ) /
        204800000000) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP006ExpBound2557 using 1; norm_num [neighborFourthP006Exponent2557])
  have hid : neighborFourthCell2557 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) ((79233025209 : ℝ) /
        102400000000) ((158531586419 : ℝ) /
        204800000000) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP006ExpUpper2557, neighborFourthP006Frequency2557, neighborFourthP006Upper2557]

def neighborFourthP007Input2557 : RatPair2542 := ((((-((10686 * 10^40
        + 5514579033133485558018445580747464399624) * 10^40
        + 6137789117471636006252046452959068041489)) : ℚ) /
        ((14750 * 10^40
        + 3272438641351937974655549942583722485628) * 10^40
        + 1435370751161707864793864342732800000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP007Center2557 : RatPair2542 := (((5327421052927345222380711195 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP007Error2557 : ℝ := ((1547288813920703326910549 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP007ExpUpper2557 : ℝ := (((1 * 10^40
        + 1715122787504555937933038864701319215189) : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP007Frequency2557 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def neighborFourthP007Upper2557 : ℝ := ((290586220748806158372759479630025 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def neighborFourthP007Exponent2557 : ℝ := (((-((10686 * 10^40
        + 5514579033133485558018445580747464399624) * 10^40
        + 6137789117471636006252046452959068041489)) : ℝ) /
        ((230 * 10^40
        + 4738631853771124030853992967852870663837) * 10^40
        + 9397427667986901685387404130355200000000))

theorem neighborFourthP007ExpBound2557 :
    Real.exp neighborFourthP007Exponent2557 ≤ neighborFourthP007ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP007Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP007Input2557]
  have hc : (compactExp2547 neighborFourthP007Input2557 6).1 = neighborFourthP007Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP007Input2557 6).2 : ℝ) = neighborFourthP007Error2557
      := by
    have hq : (compactExp2547 neighborFourthP007Input2557 6).2 =
        ((1547288813920703326910549 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP007Error2557]
  have h := compactExp_error2547 neighborFourthP007Input2557 hz 6
  rw [hc, he] at h
  have ha : (2 : ℂ)^6 * embedPair2542 neighborFourthP007Input2557 =
      (neighborFourthP007Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP007Input2557,
        neighborFourthP007Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP007Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP007Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP007Center2557))).trans
  norm_num [neighborFourthP007Error2557, neighborFourthP007ExpUpper2557, pairMagnitude2542,
      neighborFourthP007Center2557]

theorem neighborFourthP007Bound2557 : neighborFourthCell2557 ⟨7, by omega⟩ ≤
    neighborFourthP007Upper2557 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      neighborFourthP007Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP007Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP007Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP007ExpBound2557 using 1; norm_num [neighborFourthP007Exponent2557])
  have hid : neighborFourthCell2557 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((471566030480427815703046440251031552 : ℝ) /
        820072426763031369022145809814453125) ((6132893697484703689170265263264759808 : ℝ) /
        10660941547919407797287895527587890625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP007ExpUpper2557, neighborFourthP007Frequency2557, neighborFourthP007Upper2557]

def neighborFourthP008Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP008Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP008Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP008ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP008Frequency2557 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def neighborFourthP008Upper2557 : ℝ := ((5909173563002281060698845961 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP008Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP008ExpBound2557 :
    Real.exp neighborFourthP008Exponent2557 ≤ neighborFourthP008ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP008Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP008Input2557]
  have hc : (compactExp2547 neighborFourthP008Input2557 15).1 = neighborFourthP008Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP008Input2557 15).2 : ℝ) = neighborFourthP008Error2557
      := by
    have hq : (compactExp2547 neighborFourthP008Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP008Error2557]
  have h := compactExp_error2547 neighborFourthP008Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP008Input2557 =
      (neighborFourthP008Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP008Input2557,
        neighborFourthP008Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP008Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP008Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP008Center2557))).trans
  norm_num [neighborFourthP008Error2557, neighborFourthP008ExpUpper2557, pairMagnitude2542,
      neighborFourthP008Center2557]

theorem neighborFourthP008Bound2557 : neighborFourthCell2557 ⟨8, by omega⟩ ≤
    neighborFourthP008Upper2557 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      neighborFourthP008Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP008Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP008Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP008ExpBound2557 using 1; norm_num [neighborFourthP008Exponent2557])
  have hid : neighborFourthCell2557 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP008ExpUpper2557, neighborFourthP008Frequency2557, neighborFourthP008Upper2557]

def neighborFourthP009Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP009Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP009Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP009ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP009Frequency2557 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def neighborFourthP009Upper2557 : ℝ := ((5909195049938260179575100899 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP009Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP009ExpBound2557 :
    Real.exp neighborFourthP009Exponent2557 ≤ neighborFourthP009ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP009Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP009Input2557]
  have hc : (compactExp2547 neighborFourthP009Input2557 15).1 = neighborFourthP009Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP009Input2557 15).2 : ℝ) = neighborFourthP009Error2557
      := by
    have hq : (compactExp2547 neighborFourthP009Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP009Error2557]
  have h := compactExp_error2547 neighborFourthP009Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP009Input2557 =
      (neighborFourthP009Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP009Input2557,
        neighborFourthP009Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP009Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP009Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP009Center2557))).trans
  norm_num [neighborFourthP009Error2557, neighborFourthP009ExpUpper2557, pairMagnitude2542,
      neighborFourthP009Center2557]

theorem neighborFourthP009Bound2557 : neighborFourthCell2557 ⟨9, by omega⟩ ≤
    neighborFourthP009Upper2557 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      neighborFourthP009Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP009Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP009Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP009ExpBound2557 using 1; norm_num [neighborFourthP009Exponent2557])
  have hid : neighborFourthCell2557 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP009ExpUpper2557, neighborFourthP009Frequency2557, neighborFourthP009Upper2557]

def neighborFourthP010Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP010Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP010Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP010ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP010Frequency2557 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def neighborFourthP010Upper2557 : ℝ := ((5909207496492113742843870253 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP010Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP010ExpBound2557 :
    Real.exp neighborFourthP010Exponent2557 ≤ neighborFourthP010ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP010Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP010Input2557]
  have hc : (compactExp2547 neighborFourthP010Input2557 15).1 = neighborFourthP010Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP010Input2557 15).2 : ℝ) = neighborFourthP010Error2557
      := by
    have hq : (compactExp2547 neighborFourthP010Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP010Error2557]
  have h := compactExp_error2547 neighborFourthP010Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP010Input2557 =
      (neighborFourthP010Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP010Input2557,
        neighborFourthP010Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP010Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP010Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP010Center2557))).trans
  norm_num [neighborFourthP010Error2557, neighborFourthP010ExpUpper2557, pairMagnitude2542,
      neighborFourthP010Center2557]

theorem neighborFourthP010Bound2557 : neighborFourthCell2557 ⟨10, by omega⟩ ≤
    neighborFourthP010Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      neighborFourthP010Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP010Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP010Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP010ExpBound2557 using 1; norm_num [neighborFourthP010Exponent2557])
  have hid : neighborFourthCell2557 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP010ExpUpper2557, neighborFourthP010Frequency2557, neighborFourthP010Upper2557]

def neighborFourthP011Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP011Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP011Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP011ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP011Frequency2557 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def neighborFourthP011Upper2557 : ℝ := ((92331496804173259513001223 : ℝ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984))

noncomputable def neighborFourthP011Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP011ExpBound2557 :
    Real.exp neighborFourthP011Exponent2557 ≤ neighborFourthP011ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP011Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP011Input2557]
  have hc : (compactExp2547 neighborFourthP011Input2557 15).1 = neighborFourthP011Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP011Input2557 15).2 : ℝ) = neighborFourthP011Error2557
      := by
    have hq : (compactExp2547 neighborFourthP011Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP011Error2557]
  have h := compactExp_error2547 neighborFourthP011Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP011Input2557 =
      (neighborFourthP011Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP011Input2557,
        neighborFourthP011Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP011Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP011Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP011Center2557))).trans
  norm_num [neighborFourthP011Error2557, neighborFourthP011ExpUpper2557, pairMagnitude2542,
      neighborFourthP011Center2557]

theorem neighborFourthP011Bound2557 : neighborFourthCell2557 ⟨11, by omega⟩ ≤
    neighborFourthP011Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      neighborFourthP011Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP011Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP011Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP011ExpBound2557 using 1; norm_num [neighborFourthP011Exponent2557])
  have hid : neighborFourthCell2557 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP011ExpUpper2557, neighborFourthP011Frequency2557, neighborFourthP011Upper2557]

def neighborFourthP012Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP012Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP012Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP012ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP012Frequency2557 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def neighborFourthP012Upper2557 : ℝ := ((5909224391459577560014098539 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP012Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP012ExpBound2557 :
    Real.exp neighborFourthP012Exponent2557 ≤ neighborFourthP012ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP012Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP012Input2557]
  have hc : (compactExp2547 neighborFourthP012Input2557 15).1 = neighborFourthP012Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP012Input2557 15).2 : ℝ) = neighborFourthP012Error2557
      := by
    have hq : (compactExp2547 neighborFourthP012Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP012Error2557]
  have h := compactExp_error2547 neighborFourthP012Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP012Input2557 =
      (neighborFourthP012Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP012Input2557,
        neighborFourthP012Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP012Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP012Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP012Center2557))).trans
  norm_num [neighborFourthP012Error2557, neighborFourthP012ExpUpper2557, pairMagnitude2542,
      neighborFourthP012Center2557]

theorem neighborFourthP012Bound2557 : neighborFourthCell2557 ⟨12, by omega⟩ ≤
    neighborFourthP012Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      neighborFourthP012Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP012Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP012Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP012ExpBound2557 using 1; norm_num [neighborFourthP012Exponent2557])
  have hid : neighborFourthCell2557 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP012ExpUpper2557, neighborFourthP012Frequency2557, neighborFourthP012Upper2557]

def neighborFourthP013Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP013Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP013Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP013ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP013Frequency2557 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def neighborFourthP013Upper2557 : ℝ := ((5909232225057521861936677647 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP013Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP013ExpBound2557 :
    Real.exp neighborFourthP013Exponent2557 ≤ neighborFourthP013ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP013Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP013Input2557]
  have hc : (compactExp2547 neighborFourthP013Input2557 15).1 = neighborFourthP013Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP013Input2557 15).2 : ℝ) = neighborFourthP013Error2557
      := by
    have hq : (compactExp2547 neighborFourthP013Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP013Error2557]
  have h := compactExp_error2547 neighborFourthP013Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP013Input2557 =
      (neighborFourthP013Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP013Input2557,
        neighborFourthP013Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP013Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP013Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP013Center2557))).trans
  norm_num [neighborFourthP013Error2557, neighborFourthP013ExpUpper2557, pairMagnitude2542,
      neighborFourthP013Center2557]

theorem neighborFourthP013Bound2557 : neighborFourthCell2557 ⟨13, by omega⟩ ≤
    neighborFourthP013Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      neighborFourthP013Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP013Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP013Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP013ExpBound2557 using 1; norm_num [neighborFourthP013Exponent2557])
  have hid : neighborFourthCell2557 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP013ExpUpper2557, neighborFourthP013Frequency2557, neighborFourthP013Upper2557]

def neighborFourthP014Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP014Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP014Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP014ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP014Frequency2557 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def neighborFourthP014Upper2557 : ℝ := ((2954623370138946023806003689 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def neighborFourthP014Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP014ExpBound2557 :
    Real.exp neighborFourthP014Exponent2557 ≤ neighborFourthP014ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP014Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP014Input2557]
  have hc : (compactExp2547 neighborFourthP014Input2557 15).1 = neighborFourthP014Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP014Input2557 15).2 : ℝ) = neighborFourthP014Error2557
      := by
    have hq : (compactExp2547 neighborFourthP014Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP014Error2557]
  have h := compactExp_error2547 neighborFourthP014Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP014Input2557 =
      (neighborFourthP014Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP014Input2557,
        neighborFourthP014Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP014Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP014Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP014Center2557))).trans
  norm_num [neighborFourthP014Error2557, neighborFourthP014ExpUpper2557, pairMagnitude2542,
      neighborFourthP014Center2557]

theorem neighborFourthP014Bound2557 : neighborFourthCell2557 ⟨14, by omega⟩ ≤
    neighborFourthP014Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      neighborFourthP014Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP014Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP014Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP014ExpBound2557 using 1; norm_num [neighborFourthP014Exponent2557])
  have hid : neighborFourthCell2557 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP014ExpUpper2557, neighborFourthP014Frequency2557, neighborFourthP014Upper2557]

def neighborFourthP015Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP015Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP015Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP015ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP015Frequency2557 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def neighborFourthP015Upper2557 : ℝ := ((2954628570352075329484660245 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def neighborFourthP015Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP015ExpBound2557 :
    Real.exp neighborFourthP015Exponent2557 ≤ neighborFourthP015ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP015Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP015Input2557]
  have hc : (compactExp2547 neighborFourthP015Input2557 15).1 = neighborFourthP015Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP015Input2557 15).2 : ℝ) = neighborFourthP015Error2557
      := by
    have hq : (compactExp2547 neighborFourthP015Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP015Error2557]
  have h := compactExp_error2547 neighborFourthP015Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP015Input2557 =
      (neighborFourthP015Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP015Input2557,
        neighborFourthP015Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP015Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP015Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP015Center2557))).trans
  norm_num [neighborFourthP015Error2557, neighborFourthP015ExpUpper2557, pairMagnitude2542,
      neighborFourthP015Center2557]

theorem neighborFourthP015Bound2557 : neighborFourthCell2557 ⟨15, by omega⟩ ≤
    neighborFourthP015Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      neighborFourthP015Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP015Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP015Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP015ExpBound2557 using 1; norm_num [neighborFourthP015Exponent2557])
  have hid : neighborFourthCell2557 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP015ExpUpper2557, neighborFourthP015Frequency2557, neighborFourthP015Upper2557]

def neighborFourthP016Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP016Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP016Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP016ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP016Frequency2557 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def neighborFourthP016Upper2557 : ℝ := ((2954632328476960164631006819 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def neighborFourthP016Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP016ExpBound2557 :
    Real.exp neighborFourthP016Exponent2557 ≤ neighborFourthP016ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP016Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP016Input2557]
  have hc : (compactExp2547 neighborFourthP016Input2557 15).1 = neighborFourthP016Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP016Input2557 15).2 : ℝ) = neighborFourthP016Error2557
      := by
    have hq : (compactExp2547 neighborFourthP016Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP016Error2557]
  have h := compactExp_error2547 neighborFourthP016Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP016Input2557 =
      (neighborFourthP016Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP016Input2557,
        neighborFourthP016Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP016Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP016Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP016Center2557))).trans
  norm_num [neighborFourthP016Error2557, neighborFourthP016ExpUpper2557, pairMagnitude2542,
      neighborFourthP016Center2557]

theorem neighborFourthP016Bound2557 : neighborFourthCell2557 ⟨16, by omega⟩ ≤
    neighborFourthP016Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      neighborFourthP016Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP016Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP016Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP016ExpBound2557 using 1; norm_num [neighborFourthP016Exponent2557])
  have hid : neighborFourthCell2557 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP016ExpUpper2557, neighborFourthP016Frequency2557, neighborFourthP016Upper2557]

def neighborFourthP017Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP017Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP017Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP017ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP017Frequency2557 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def neighborFourthP017Upper2557 : ℝ := ((5909279256971808120426219925 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP017Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP017ExpBound2557 :
    Real.exp neighborFourthP017Exponent2557 ≤ neighborFourthP017ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP017Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP017Input2557]
  have hc : (compactExp2547 neighborFourthP017Input2557 15).1 = neighborFourthP017Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP017Input2557 15).2 : ℝ) = neighborFourthP017Error2557
      := by
    have hq : (compactExp2547 neighborFourthP017Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP017Error2557]
  have h := compactExp_error2547 neighborFourthP017Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP017Input2557 =
      (neighborFourthP017Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP017Input2557,
        neighborFourthP017Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP017Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP017Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP017Center2557))).trans
  norm_num [neighborFourthP017Error2557, neighborFourthP017ExpUpper2557, pairMagnitude2542,
      neighborFourthP017Center2557]

theorem neighborFourthP017Bound2557 : neighborFourthCell2557 ⟨17, by omega⟩ ≤
    neighborFourthP017Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      neighborFourthP017Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP017Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP017Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP017ExpBound2557 using 1; norm_num [neighborFourthP017Exponent2557])
  have hid : neighborFourthCell2557 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP017ExpUpper2557, neighborFourthP017Frequency2557, neighborFourthP017Upper2557]

def neighborFourthP018Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP018Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP018Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP018ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP018Frequency2557 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def neighborFourthP018Upper2557 : ℝ := ((5909284776977974914640013257 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP018Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP018ExpBound2557 :
    Real.exp neighborFourthP018Exponent2557 ≤ neighborFourthP018ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP018Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP018Input2557]
  have hc : (compactExp2547 neighborFourthP018Input2557 15).1 = neighborFourthP018Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP018Input2557 15).2 : ℝ) = neighborFourthP018Error2557
      := by
    have hq : (compactExp2547 neighborFourthP018Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP018Error2557]
  have h := compactExp_error2547 neighborFourthP018Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP018Input2557 =
      (neighborFourthP018Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP018Input2557,
        neighborFourthP018Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP018Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP018Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP018Center2557))).trans
  norm_num [neighborFourthP018Error2557, neighborFourthP018ExpUpper2557, pairMagnitude2542,
      neighborFourthP018Center2557]

theorem neighborFourthP018Bound2557 : neighborFourthCell2557 ⟨18, by omega⟩ ≤
    neighborFourthP018Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      neighborFourthP018Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP018Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP018Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP018ExpBound2557 using 1; norm_num [neighborFourthP018Exponent2557])
  have hid : neighborFourthCell2557 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP018ExpUpper2557, neighborFourthP018Frequency2557, neighborFourthP018Upper2557]

def neighborFourthP019Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP019Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP019Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP019ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP019Frequency2557 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def neighborFourthP019Upper2557 : ℝ := ((5909294753190229834671786109 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP019Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP019ExpBound2557 :
    Real.exp neighborFourthP019Exponent2557 ≤ neighborFourthP019ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP019Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP019Input2557]
  have hc : (compactExp2547 neighborFourthP019Input2557 15).1 = neighborFourthP019Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP019Input2557 15).2 : ℝ) = neighborFourthP019Error2557
      := by
    have hq : (compactExp2547 neighborFourthP019Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP019Error2557]
  have h := compactExp_error2547 neighborFourthP019Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP019Input2557 =
      (neighborFourthP019Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP019Input2557,
        neighborFourthP019Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP019Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP019Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP019Center2557))).trans
  norm_num [neighborFourthP019Error2557, neighborFourthP019ExpUpper2557, pairMagnitude2542,
      neighborFourthP019Center2557]

theorem neighborFourthP019Bound2557 : neighborFourthCell2557 ⟨19, by omega⟩ ≤
    neighborFourthP019Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      neighborFourthP019Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP019Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP019Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP019ExpBound2557 using 1; norm_num [neighborFourthP019Exponent2557])
  have hid : neighborFourthCell2557 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP019ExpUpper2557, neighborFourthP019Frequency2557, neighborFourthP019Upper2557]

def neighborFourthP020Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP020Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP020Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP020ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP020Frequency2557 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def neighborFourthP020Upper2557 : ℝ := ((2954652800799345591304433769 : ℝ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))

noncomputable def neighborFourthP020Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP020ExpBound2557 :
    Real.exp neighborFourthP020Exponent2557 ≤ neighborFourthP020ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP020Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP020Input2557]
  have hc : (compactExp2547 neighborFourthP020Input2557 15).1 = neighborFourthP020Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP020Input2557 15).2 : ℝ) = neighborFourthP020Error2557
      := by
    have hq : (compactExp2547 neighborFourthP020Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP020Error2557]
  have h := compactExp_error2547 neighborFourthP020Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP020Input2557 =
      (neighborFourthP020Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP020Input2557,
        neighborFourthP020Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP020Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP020Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP020Center2557))).trans
  norm_num [neighborFourthP020Error2557, neighborFourthP020ExpUpper2557, pairMagnitude2542,
      neighborFourthP020Center2557]

theorem neighborFourthP020Bound2557 : neighborFourthCell2557 ⟨20, by omega⟩ ≤
    neighborFourthP020Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      neighborFourthP020Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP020Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP020Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP020ExpBound2557 using 1; norm_num [neighborFourthP020Exponent2557])
  have hid : neighborFourthCell2557 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP020ExpUpper2557, neighborFourthP020Frequency2557, neighborFourthP020Upper2557]

def neighborFourthP021Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP021Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP021Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP021ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP021Frequency2557 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def neighborFourthP021Upper2557 : ℝ := ((1477328663767956256761638021 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def neighborFourthP021Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP021ExpBound2557 :
    Real.exp neighborFourthP021Exponent2557 ≤ neighborFourthP021ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP021Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP021Input2557]
  have hc : (compactExp2547 neighborFourthP021Input2557 15).1 = neighborFourthP021Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP021Input2557 15).2 : ℝ) = neighborFourthP021Error2557
      := by
    have hq : (compactExp2547 neighborFourthP021Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP021Error2557]
  have h := compactExp_error2547 neighborFourthP021Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP021Input2557 =
      (neighborFourthP021Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP021Input2557,
        neighborFourthP021Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP021Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP021Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP021Center2557))).trans
  norm_num [neighborFourthP021Error2557, neighborFourthP021ExpUpper2557, pairMagnitude2542,
      neighborFourthP021Center2557]

theorem neighborFourthP021Bound2557 : neighborFourthCell2557 ⟨21, by omega⟩ ≤
    neighborFourthP021Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      neighborFourthP021Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP021Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP021Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP021ExpBound2557 using 1; norm_num [neighborFourthP021Exponent2557])
  have hid : neighborFourthCell2557 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP021ExpUpper2557, neighborFourthP021Frequency2557, neighborFourthP021Upper2557]

def neighborFourthP022Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP022Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP022Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP022ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP022Frequency2557 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def neighborFourthP022Upper2557 : ℝ := ((5909319288989766954684515467 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP022Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP022ExpBound2557 :
    Real.exp neighborFourthP022Exponent2557 ≤ neighborFourthP022ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP022Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP022Input2557]
  have hc : (compactExp2547 neighborFourthP022Input2557 15).1 = neighborFourthP022Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP022Input2557 15).2 : ℝ) = neighborFourthP022Error2557
      := by
    have hq : (compactExp2547 neighborFourthP022Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP022Error2557]
  have h := compactExp_error2547 neighborFourthP022Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP022Input2557 =
      (neighborFourthP022Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP022Input2557,
        neighborFourthP022Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP022Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP022Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP022Center2557))).trans
  norm_num [neighborFourthP022Error2557, neighborFourthP022ExpUpper2557, pairMagnitude2542,
      neighborFourthP022Center2557]

theorem neighborFourthP022Bound2557 : neighborFourthCell2557 ⟨22, by omega⟩ ≤
    neighborFourthP022Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      neighborFourthP022Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP022Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP022Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP022ExpBound2557 using 1; norm_num [neighborFourthP022Exponent2557])
  have hid : neighborFourthCell2557 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP022ExpUpper2557, neighborFourthP022Frequency2557, neighborFourthP022Upper2557]

def neighborFourthP023Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP023Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP023Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP023ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP023Frequency2557 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def neighborFourthP023Upper2557 : ℝ := ((5909332649492632842648795565 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP023Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP023ExpBound2557 :
    Real.exp neighborFourthP023Exponent2557 ≤ neighborFourthP023ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP023Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP023Input2557]
  have hc : (compactExp2547 neighborFourthP023Input2557 15).1 = neighborFourthP023Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP023Input2557 15).2 : ℝ) = neighborFourthP023Error2557
      := by
    have hq : (compactExp2547 neighborFourthP023Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP023Error2557]
  have h := compactExp_error2547 neighborFourthP023Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP023Input2557 =
      (neighborFourthP023Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP023Input2557,
        neighborFourthP023Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP023Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP023Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP023Center2557))).trans
  norm_num [neighborFourthP023Error2557, neighborFourthP023ExpUpper2557, pairMagnitude2542,
      neighborFourthP023Center2557]

theorem neighborFourthP023Bound2557 : neighborFourthCell2557 ⟨23, by omega⟩ ≤
    neighborFourthP023Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      neighborFourthP023Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP023Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP023Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP023ExpBound2557 using 1; norm_num [neighborFourthP023Exponent2557])
  have hid : neighborFourthCell2557 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP023ExpUpper2557, neighborFourthP023Frequency2557, neighborFourthP023Upper2557]

def neighborFourthP024Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP024Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP024Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP024ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP024Frequency2557 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def neighborFourthP024Upper2557 : ℝ := ((5909338789464419944217059477 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP024Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP024ExpBound2557 :
    Real.exp neighborFourthP024Exponent2557 ≤ neighborFourthP024ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP024Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP024Input2557]
  have hc : (compactExp2547 neighborFourthP024Input2557 15).1 = neighborFourthP024Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP024Input2557 15).2 : ℝ) = neighborFourthP024Error2557
      := by
    have hq : (compactExp2547 neighborFourthP024Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP024Error2557]
  have h := compactExp_error2547 neighborFourthP024Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP024Input2557 =
      (neighborFourthP024Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP024Input2557,
        neighborFourthP024Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP024Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP024Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP024Center2557))).trans
  norm_num [neighborFourthP024Error2557, neighborFourthP024ExpUpper2557, pairMagnitude2542,
      neighborFourthP024Center2557]

theorem neighborFourthP024Bound2557 : neighborFourthCell2557 ⟨24, by omega⟩ ≤
    neighborFourthP024Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      neighborFourthP024Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP024Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP024Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP024ExpBound2557 using 1; norm_num [neighborFourthP024Exponent2557])
  have hid : neighborFourthCell2557 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP024ExpUpper2557, neighborFourthP024Frequency2557, neighborFourthP024Upper2557]

def neighborFourthP025Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP025Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP025Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP025ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP025Frequency2557 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def neighborFourthP025Upper2557 : ℝ := ((5909346487883247116836575453 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP025Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP025ExpBound2557 :
    Real.exp neighborFourthP025Exponent2557 ≤ neighborFourthP025ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP025Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP025Input2557]
  have hc : (compactExp2547 neighborFourthP025Input2557 15).1 = neighborFourthP025Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP025Input2557 15).2 : ℝ) = neighborFourthP025Error2557
      := by
    have hq : (compactExp2547 neighborFourthP025Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP025Error2557]
  have h := compactExp_error2547 neighborFourthP025Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP025Input2557 =
      (neighborFourthP025Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP025Input2557,
        neighborFourthP025Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP025Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP025Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP025Center2557))).trans
  norm_num [neighborFourthP025Error2557, neighborFourthP025ExpUpper2557, pairMagnitude2542,
      neighborFourthP025Center2557]

theorem neighborFourthP025Bound2557 : neighborFourthCell2557 ⟨25, by omega⟩ ≤
    neighborFourthP025Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      neighborFourthP025Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP025Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP025Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP025ExpBound2557 using 1; norm_num [neighborFourthP025Exponent2557])
  have hid : neighborFourthCell2557 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP025ExpUpper2557, neighborFourthP025Frequency2557, neighborFourthP025Upper2557]

def neighborFourthP026Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP026Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP026Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP026ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP026Frequency2557 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def neighborFourthP026Upper2557 : ℝ := ((5909354355376910988070849507 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP026Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP026ExpBound2557 :
    Real.exp neighborFourthP026Exponent2557 ≤ neighborFourthP026ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP026Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP026Input2557]
  have hc : (compactExp2547 neighborFourthP026Input2557 15).1 = neighborFourthP026Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP026Input2557 15).2 : ℝ) = neighborFourthP026Error2557
      := by
    have hq : (compactExp2547 neighborFourthP026Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP026Error2557]
  have h := compactExp_error2547 neighborFourthP026Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP026Input2557 =
      (neighborFourthP026Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP026Input2557,
        neighborFourthP026Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP026Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP026Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP026Center2557))).trans
  norm_num [neighborFourthP026Error2557, neighborFourthP026ExpUpper2557, pairMagnitude2542,
      neighborFourthP026Center2557]

theorem neighborFourthP026Bound2557 : neighborFourthCell2557 ⟨26, by omega⟩ ≤
    neighborFourthP026Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      neighborFourthP026Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP026Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP026Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP026ExpBound2557 using 1; norm_num [neighborFourthP026Exponent2557])
  have hid : neighborFourthCell2557 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP026ExpUpper2557, neighborFourthP026Frequency2557, neighborFourthP026Upper2557]

def neighborFourthP027Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP027Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP027Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP027ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP027Frequency2557 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def neighborFourthP027Upper2557 : ℝ := ((1477341427115933043002903169 : ℝ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))

noncomputable def neighborFourthP027Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP027ExpBound2557 :
    Real.exp neighborFourthP027Exponent2557 ≤ neighborFourthP027ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP027Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP027Input2557]
  have hc : (compactExp2547 neighborFourthP027Input2557 15).1 = neighborFourthP027Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP027Input2557 15).2 : ℝ) = neighborFourthP027Error2557
      := by
    have hq : (compactExp2547 neighborFourthP027Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP027Error2557]
  have h := compactExp_error2547 neighborFourthP027Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP027Input2557 =
      (neighborFourthP027Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP027Input2557,
        neighborFourthP027Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP027Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP027Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP027Center2557))).trans
  norm_num [neighborFourthP027Error2557, neighborFourthP027ExpUpper2557, pairMagnitude2542,
      neighborFourthP027Center2557]

theorem neighborFourthP027Bound2557 : neighborFourthCell2557 ⟨27, by omega⟩ ≤
    neighborFourthP027Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      neighborFourthP027Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP027Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP027Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP027ExpBound2557 using 1; norm_num [neighborFourthP027Exponent2557])
  have hid : neighborFourthCell2557 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP027ExpUpper2557, neighborFourthP027Frequency2557, neighborFourthP027Upper2557]

def neighborFourthP028Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP028Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP028Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP028ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP028Frequency2557 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def neighborFourthP028Upper2557 : ℝ := ((5909370203318340831251978527 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP028Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP028ExpBound2557 :
    Real.exp neighborFourthP028Exponent2557 ≤ neighborFourthP028ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP028Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP028Input2557]
  have hc : (compactExp2547 neighborFourthP028Input2557 15).1 = neighborFourthP028Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP028Input2557 15).2 : ℝ) = neighborFourthP028Error2557
      := by
    have hq : (compactExp2547 neighborFourthP028Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP028Error2557]
  have h := compactExp_error2547 neighborFourthP028Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP028Input2557 =
      (neighborFourthP028Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP028Input2557,
        neighborFourthP028Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP028Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP028Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP028Center2557))).trans
  norm_num [neighborFourthP028Error2557, neighborFourthP028ExpUpper2557, pairMagnitude2542,
      neighborFourthP028Center2557]

theorem neighborFourthP028Bound2557 : neighborFourthCell2557 ⟨28, by omega⟩ ≤
    neighborFourthP028Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      neighborFourthP028Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP028Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP028Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP028ExpBound2557 using 1; norm_num [neighborFourthP028Exponent2557])
  have hid : neighborFourthCell2557 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP028ExpUpper2557, neighborFourthP028Frequency2557, neighborFourthP028Upper2557]

def neighborFourthP029Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((0 : ℚ) /
        1))

def neighborFourthP029Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborFourthP029Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP029ExpUpper2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

noncomputable def neighborFourthP029Frequency2557 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def neighborFourthP029Upper2557 : ℝ := ((5909377046457567147687827547 : ℝ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))

noncomputable def neighborFourthP029Exponent2557 : ℝ := (((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℝ) /
        ((31 * 10^40
        + 8432169855837470023946853688601202822129) * 10^40
        + 6252851071400568705471298030028800000000))

theorem neighborFourthP029ExpBound2557 :
    Real.exp neighborFourthP029Exponent2557 ≤ neighborFourthP029ExpUpper2557 := by
  have hz : ‖embedPair2542 neighborFourthP029Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborFourthP029Input2557]
  have hc : (compactExp2547 neighborFourthP029Input2557 15).1 = neighborFourthP029Center2557 := by
      decide +kernel
  have he : ((compactExp2547 neighborFourthP029Input2557 15).2 : ℝ) = neighborFourthP029Error2557
      := by
    have hq : (compactExp2547 neighborFourthP029Input2557 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by decide +kernel
    rw [hq]
    norm_num [neighborFourthP029Error2557]
  have h := compactExp_error2547 neighborFourthP029Input2557 hz 15
  rw [hc, he] at h
  have ha : (2 : ℂ)^15 * embedPair2542 neighborFourthP029Input2557 =
      (neighborFourthP029Exponent2557 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, neighborFourthP029Input2557,
        neighborFourthP029Exponent2557,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (neighborFourthP029Exponent2557 : ℂ)) (embedPair2542
        neighborFourthP029Center2557) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 neighborFourthP029Center2557))).trans
  norm_num [neighborFourthP029Error2557, neighborFourthP029ExpUpper2557, pairMagnitude2542,
      neighborFourthP029Center2557]

theorem neighborFourthP029Bound2557 : neighborFourthCell2557 ⟨29, by omega⟩ ≤
    neighborFourthP029Upper2557 :=
    by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      neighborFourthP029Frequency2557 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [neighborFourthP029Frequency2557])
    norm_num [weightedLambda2537, nodeModulation2541, neighborFourthP029Frequency2557,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000)
    (by norm_num) (by norm_num) hf
    (by convert neighborFourthP029ExpBound2557 using 1; norm_num [neighborFourthP029Exponent2557])
  have hid : neighborFourthCell2557 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((6130358396245561604139603723263410176 : ℝ) /
        6135428905104631913280910298972265625) ((6132893697484703689170265263264759808 : ℝ) /
        6135428905104631913280910298972265625) (((-158531586419) : ℝ) /
        51200000000) (((-79233025209) : ℝ) /
        25600000000) := by
    norm_num [neighborFourthCell2557, cellNearAbs2538, kernelN02701PlusPosition2555,
      neighborRightPosition2557, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    neighborFourthP029ExpUpper2557, neighborFourthP029Frequency2557, neighborFourthP029Upper2557]

noncomputable def neighborFourthP000Upper2557 : ℝ := 0

theorem neighborFourthP000Bound2557 :
    neighborFourthCell2557 ⟨0, by omega⟩ ≤ neighborFourthP000Upper2557 := by
  norm_num [neighborFourthCell2557, neighborFourthP000Upper2557, cellNearAbs2538,
    kernelN02701PlusPosition2555, neighborRightPosition2557, storedWidth]

noncomputable def neighborFourthP005Upper2557 : ℝ := 0

theorem neighborFourthP005Bound2557 :
    neighborFourthCell2557 ⟨5, by omega⟩ ≤ neighborFourthP005Upper2557 := by
  norm_num [neighborFourthCell2557, neighborFourthP005Upper2557, cellNearAbs2538,
    kernelN02701PlusPosition2555, neighborRightPosition2557, storedWidth]

noncomputable def neighborFourthUpper2557 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => neighborFourthP000Upper2557
  | 1 => neighborFourthP001Upper2557
  | 2 => neighborFourthP002Upper2557
  | 3 => neighborFourthP003Upper2557
  | 4 => neighborFourthP004Upper2557
  | 5 => neighborFourthP005Upper2557
  | 6 => neighborFourthP006Upper2557
  | 7 => neighborFourthP007Upper2557
  | 8 => neighborFourthP008Upper2557
  | 9 => neighborFourthP009Upper2557
  | 10 => neighborFourthP010Upper2557
  | 11 => neighborFourthP011Upper2557
  | 12 => neighborFourthP012Upper2557
  | 13 => neighborFourthP013Upper2557
  | 14 => neighborFourthP014Upper2557
  | 15 => neighborFourthP015Upper2557
  | 16 => neighborFourthP016Upper2557
  | 17 => neighborFourthP017Upper2557
  | 18 => neighborFourthP018Upper2557
  | 19 => neighborFourthP019Upper2557
  | 20 => neighborFourthP020Upper2557
  | 21 => neighborFourthP021Upper2557
  | 22 => neighborFourthP022Upper2557
  | 23 => neighborFourthP023Upper2557
  | 24 => neighborFourthP024Upper2557
  | 25 => neighborFourthP025Upper2557
  | 26 => neighborFourthP026Upper2557
  | 27 => neighborFourthP027Upper2557
  | 28 => neighborFourthP028Upper2557
  | 29 => neighborFourthP029Upper2557
  | _ => 0

theorem neighborFourthBound2557 (i : Fin 30) :
    neighborFourthCell2557 i ≤ neighborFourthUpper2557 i := by
  fin_cases i
  · exact neighborFourthP000Bound2557
  · exact neighborFourthP001Bound2557
  · exact neighborFourthP002Bound2557
  · exact neighborFourthP003Bound2557
  · exact neighborFourthP004Bound2557
  · exact neighborFourthP005Bound2557
  · exact neighborFourthP006Bound2557
  · exact neighborFourthP007Bound2557
  · exact neighborFourthP008Bound2557
  · exact neighborFourthP009Bound2557
  · exact neighborFourthP010Bound2557
  · exact neighborFourthP011Bound2557
  · exact neighborFourthP012Bound2557
  · exact neighborFourthP013Bound2557
  · exact neighborFourthP014Bound2557
  · exact neighborFourthP015Bound2557
  · exact neighborFourthP016Bound2557
  · exact neighborFourthP017Bound2557
  · exact neighborFourthP018Bound2557
  · exact neighborFourthP019Bound2557
  · exact neighborFourthP020Bound2557
  · exact neighborFourthP021Bound2557
  · exact neighborFourthP022Bound2557
  · exact neighborFourthP023Bound2557
  · exact neighborFourthP024Bound2557
  · exact neighborFourthP025Bound2557
  · exact neighborFourthP026Bound2557
  · exact neighborFourthP027Bound2557
  · exact neighborFourthP028Bound2557
  · exact neighborFourthP029Bound2557

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.neighborFourthP001Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP002Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP003Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP004Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP006Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP007Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP008Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP009Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP010Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP011Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP012Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP013Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP014Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP015Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP016Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP017Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP018Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP019Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP020Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP021Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP022Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP023Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP024Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP025Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP026Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP027Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP028Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP029Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthBound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP000Bound2557
#print axioms ConnesWeilRH.Dev.neighborFourthP005Bound2557
