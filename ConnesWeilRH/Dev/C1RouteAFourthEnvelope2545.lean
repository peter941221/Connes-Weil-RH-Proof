import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def fourthP000Input2545 : RatPair2542 := ((((-((10460 * 10^40
        + 9575256529414491884740341061094297670152) * 10^40
        + 8725674896932554369685259396121736233453)) : ℚ) /
        ((10945 * 10^40
        + 7383380871378782620851011200610251055133) * 10^40
        + 2366428694819926954519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP000Center2545 : RatPair2542 := (((66234687073197151 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP000Error2545 : ℝ := ((8259338010829 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

noncomputable def fourthP000ExpUpper2545 : ℝ := ((72825808599084993015913677005 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

noncomputable def fourthP000Frequency2545 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def fourthP000Upper2545 : ℝ := ((59537413979989406369103 : ℝ) /
        316912650057057350374175801344)

noncomputable def fourthP000Exponent2545 : ℝ := (((-((10460 * 10^40
        + 9575256529414491884740341061094297670152) * 10^40
        + 8725674896932554369685259396121736233453)) : ℝ) /
        ((342 * 10^40
        + 543230652230586956901594100019070345472) * 10^40
        + 9136450896713122717328748165836800000000))

theorem fourthP000ExpBound2545 :
    Real.exp fourthP000Exponent2545 ≤ fourthP000ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP000Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP000Input2545]
  have hc : (compactExp2542 fourthP000Input2545 5).1 = fourthP000Center2545 := by cbv
  have he : ((compactExp2542 fourthP000Input2545 5).2 : ℝ) = fourthP000Error2545 := by
    have hq : (compactExp2542 fourthP000Input2545 5).2 =
        ((8259338010829 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [fourthP000Error2545]
  have h := compactExp_error2542 fourthP000Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP000Input2545 =
      (fourthP000Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP000Input2545, fourthP000Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP000Exponent2545 : ℂ)) (embedPair2542 fourthP000Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP000Center2545))).trans
  norm_num [fourthP000Error2545, fourthP000ExpUpper2545, pairMagnitude2542, fourthP000Center2545]

theorem fourthP000Bound2545 : fourthCellTerm2544 ⟨0, by omega⟩ ≤ fourthP000Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨0, by omega⟩)‖ ≤
      fourthP000Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP000Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP000Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    ((12980742146337070512478121581609 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1014120480182583633787353248563203125) ((813831697764609294842354340433231872 : ℝ) /
        5070602400912918168936766242816015625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP000ExpBound2545 using 1; norm_num [fourthP000Exponent2545])
  have hid : fourthCellTerm2544 ⟨0, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨0, by omega⟩)
        ((12980742146337070512478121581609 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1014120480182583633787353248563203125) ((813831697764609294842354340433231872 : ℝ) /
        5070602400912918168936766242816015625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP000ExpUpper2545, fourthP000Frequency2545, fourthP000Upper2545]

def fourthP001Input2545 : RatPair2542 := ((((-((13 * 10^40
        + 3995829578410779517637540986559440833698) * 10^40
        + 73456670005194526678701454014728599479)) : ℚ) /
        ((14 * 10^40
        + 1793641860264920813397630277339159466940) * 10^40
        + 7639419666551648075479384722636800000000)),
    ((0 : ℚ) /
        1))

def fourthP001Center2545 : RatPair2542 := (((93293695811504727 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP001Error2545 : ℝ := ((5322141548473 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

noncomputable def fourthP001ExpUpper2545 : ℝ := ((51288751671473283147985797049 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

noncomputable def fourthP001Frequency2545 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def fourthP001Upper2545 : ℝ := ((2196128807149184431921 : ℝ) /
        9903520314283042199192993792)

noncomputable def fourthP001Exponent2545 : ℝ := (((-((13 * 10^40
        + 3995829578410779517637540986559440833698) * 10^40
        + 73456670005194526678701454014728599479)) : ℝ) /
        (4431051308133278775418675946166848733341 * 10^40
        + 8988731864579739002358730772582400000000))

theorem fourthP001ExpBound2545 :
    Real.exp fourthP001Exponent2545 ≤ fourthP001ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP001Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP001Input2545]
  have hc : (compactExp2542 fourthP001Input2545 5).1 = fourthP001Center2545 := by cbv
  have he : ((compactExp2542 fourthP001Input2545 5).2 : ℝ) = fourthP001Error2545 := by
    have hq : (compactExp2542 fourthP001Input2545 5).2 =
        ((5322141548473 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [fourthP001Error2545]
  have h := compactExp_error2542 fourthP001Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP001Input2545 =
      (fourthP001Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP001Input2545, fourthP001Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP001Exponent2545 : ℂ)) (embedPair2542 fourthP001Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP001Center2545))).trans
  norm_num [fourthP001Error2545, fourthP001ExpUpper2545, pairMagnitude2542, fourthP001Center2545]

theorem fourthP001Bound2545 : fourthCellTerm2544 ⟨1, by omega⟩ ≤ fourthP001Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨1, by omega⟩)‖ ≤
      fourthP001Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP001Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP001Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
    ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((2535301239142085030661540001349632 : ℝ) /
        20955848985022914056530142691328125) ((4238706759190673410637262189756416 : ℝ) /
        34926414975038190094216904485546875) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP001ExpBound2545 using 1; norm_num [fourthP001Exponent2545])
  have hid : fourthCellTerm2544 ⟨1, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
        ((268234867008293299923585826449 : ℝ) /
        79228162514264337593543950336) ((2535301239142085030661540001349632 : ℝ) /
        20955848985022914056530142691328125) ((4238706759190673410637262189756416 : ℝ) /
        34926414975038190094216904485546875) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP001ExpUpper2545, fourthP001Frequency2545, fourthP001Upper2545]

def fourthP002Input2545 : RatPair2542 := ((((-((350 * 10^40
        + 872737329593285865398413009696175181375) * 10^40
        + 5806175964389366211575511562178772826039)) : ℚ) /
        ((372 * 10^40
        + 6080518569699119430636825961677921494191) * 10^40
        + 4175213685446698507670155562188800000000)),
    ((0 : ℚ) /
        1))

def fourthP002Center2545 : RatPair2542 := (((111057879481343953 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP002Error2545 : ℝ := ((12197746710167 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

noncomputable def fourthP002ExpUpper2545 : ℝ := ((122109429845883332584911148695 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

noncomputable def fourthP002Frequency2545 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def fourthP002Upper2545 : ℝ := ((305226212552874734747281 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP002Exponent2545 : ℝ := (((-((350 * 10^40
        + 872737329593285865398413009696175181375) * 10^40
        + 5806175964389366211575511562178772826039)) : ℝ) /
        ((11 * 10^40
        + 6440016205303097482207400811302435046693) * 10^40
        + 4817975427670209328364692361318400000000))

theorem fourthP002ExpBound2545 :
    Real.exp fourthP002Exponent2545 ≤ fourthP002ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP002Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP002Input2545]
  have hc : (compactExp2542 fourthP002Input2545 5).1 = fourthP002Center2545 := by cbv
  have he : ((compactExp2542 fourthP002Input2545 5).2 : ℝ) = fourthP002Error2545 := by
    have hq : (compactExp2542 fourthP002Input2545 5).2 =
        ((12197746710167 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [fourthP002Error2545]
  have h := compactExp_error2542 fourthP002Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP002Input2545 =
      (fourthP002Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP002Input2545, fourthP002Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP002Exponent2545 : ℂ)) (embedPair2542 fourthP002Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP002Center2545))).trans
  norm_num [fourthP002Error2545, fourthP002ExpUpper2545, pairMagnitude2542, fourthP002Center2545]

theorem fourthP002Bound2545 : fourthCellTerm2544 ⟨2, by omega⟩ ≤ fourthP002Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨2, by omega⟩)‖ ≤
      fourthP002Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP002Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP002Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
    ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((10141204956568340122646160005398528 : ℝ) /
        107116475719285391744820815331328125) ((16954827036762693642549048759025664 : ℝ) /
        178527459532142319574701358885546875) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP002ExpBound2545 using 1; norm_num [fourthP002Exponent2545])
  have hid : fourthCellTerm2544 ⟨2, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
        ((1371090889206853014333706436241 : ℝ) /
        316912650057057350374175801344) ((10141204956568340122646160005398528 : ℝ) /
        107116475719285391744820815331328125) ((16954827036762693642549048759025664 : ℝ) /
        178527459532142319574701358885546875) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP002ExpUpper2545, fourthP002Frequency2545, fourthP002Upper2545]

def fourthP003Input2545 : RatPair2542 := ((((-((46236 * 10^40
        + 4131255514699533833354090203640434616631) * 10^40
        + 4783606347868318382953483916336579983453)) : ℚ) /
        ((49369 * 10^40
        + 3492025268854919357832426692645219513656) * 10^40
        + 8418178538425671914519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP003Center2545 : RatPair2542 := (((30579796410523877 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def fourthP003Error2545 : ℝ := ((6589216220027 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

noncomputable def fourthP003ExpUpper2545 : ℝ := ((67245683456787586463585035131 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

noncomputable def fourthP003Frequency2545 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def fourthP003Upper2545 : ℝ := ((159635821995442042904045 : ℝ) /
        633825300114114700748351602688)

noncomputable def fourthP003Exponent2545 : ℝ := (((-((46236 * 10^40
        + 4131255514699533833354090203640434616631) * 10^40
        + 4783606347868318382953483916336579983453)) : ℝ) /
        ((1542 * 10^40
        + 7921625789651716229932263334145163109801) * 10^40
        + 7763068079325802247328748165836800000000))

theorem fourthP003ExpBound2545 :
    Real.exp fourthP003Exponent2545 ≤ fourthP003ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP003Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP003Input2545]
  have hc : (compactExp2542 fourthP003Input2545 5).1 = fourthP003Center2545 := by cbv
  have he : ((compactExp2542 fourthP003Input2545 5).2 : ℝ) = fourthP003Error2545 := by
    have hq : (compactExp2542 fourthP003Input2545 5).2 =
        ((6589216220027 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [fourthP003Error2545]
  have h := compactExp_error2542 fourthP003Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP003Input2545 =
      (fourthP003Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP003Input2545, fourthP003Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP003Exponent2545 : ℂ)) (embedPair2542 fourthP003Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP003Center2545))).trans
  norm_num [fourthP003Error2545, fourthP003ExpUpper2545, pairMagnitude2542, fourthP003Center2545]

theorem fourthP003Bound2545 : fourthCellTerm2544 ⟨3, by omega⟩ ≤ fourthP003Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨3, by omega⟩)‖ ≤
      fourthP003Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP003Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP003Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        2132188309583881559457579105517578125) ((813831697764609294842354340433231872 : ℝ) /
        10660941547919407797287895527587890625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP003ExpBound2545 using 1; norm_num [fourthP003Exponent2545])
  have hid : fourthCellTerm2544 ⟨3, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        2132188309583881559457579105517578125) ((813831697764609294842354340433231872 : ℝ) /
        10660941547919407797287895527587890625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP003ExpUpper2545, fourthP003Frequency2545, fourthP003Upper2545]

def fourthP004Input2545 : RatPair2542 := ((((-((803 * 10^40
        + 2813838448980530537892295650294870717432) * 10^40
        + 1942365874262152752397991891280335326039)) : ℚ) /
        ((859 * 10^40
        + 3482999125832783045971401673009866250806) * 10^40
        + 5492499507992564107670155562188800000000)),
    ((0 : ℚ) /
        1))

def fourthP004Center2545 : RatPair2542 := (((64753478505592107 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def fourthP004Error2545 : ℝ := ((13802884678411 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

noncomputable def fourthP004ExpUpper2545 : ℝ := ((142394405111683624775419806475 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

noncomputable def fourthP004Frequency2545 : ℝ := ((10790506226839 : ℝ) /
        274877906944)

noncomputable def fourthP004Upper2545 : ℝ := ((327806186980341684457831 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP004Exponent2545 : ℝ := (((-((803 * 10^40
        + 2813838448980530537892295650294870717432) * 10^40
        + 1942365874262152752397991891280335326039)) : ℝ) /
        ((26 * 10^40
        + 8546343722682274470186606302281558320337) * 10^40
        + 7046640609624767628364692361318400000000))

theorem fourthP004ExpBound2545 :
    Real.exp fourthP004Exponent2545 ≤ fourthP004ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP004Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP004Input2545]
  have hc : (compactExp2542 fourthP004Input2545 5).1 = fourthP004Center2545 := by cbv
  have he : ((compactExp2542 fourthP004Input2545 5).2 : ℝ) = fourthP004Error2545 := by
    have hq : (compactExp2542 fourthP004Input2545 5).2 =
        ((13802884678411 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [fourthP004Error2545]
  have h := compactExp_error2542 fourthP004Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP004Input2545 =
      (fourthP004Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP004Input2545, fourthP004Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP004Exponent2545 : ℂ)) (embedPair2542 fourthP004Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP004Center2545))).trans
  norm_num [fourthP004Error2545, fourthP004ExpUpper2545, pairMagnitude2542, fourthP004Center2545]

theorem fourthP004Bound2545 : fourthCellTerm2544 ⟨4, by omega⟩ ≤ fourthP004Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨4, by omega⟩)‖ ≤
      fourthP004Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP004Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP004Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
    ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((10141204956568340122646160005398528 : ℝ) /
        162259276829213426441972793475078125) ((16954827036762693642549048759025664 : ℝ) /
        270432128048689044069954655791796875) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP004ExpBound2545 using 1; norm_num [fourthP004Exponent2545])
  have hid : fourthCellTerm2544 ⟨4, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
        ((2076918743413931858457251756481 : ℝ) /
        316912650057057350374175801344) ((10141204956568340122646160005398528 : ℝ) /
        162259276829213426441972793475078125) ((16954827036762693642549048759025664 : ℝ) /
        270432128048689044069954655791796875) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP004ExpUpper2545, fourthP004Frequency2545, fourthP004Upper2545]

def fourthP005Input2545 : RatPair2542 := ((((-((38144 * 10^40
        + 8841461898211752119661724894242293216339) * 10^40
        + 3153870498936871630788029349009739950359)) : ℚ) /
        ((40099 * 10^40
        + 7612723084624532412913406188229967784921) * 10^40
        + 4926440726241321663559823920332800000000)),
    ((0 : ℚ) /
        1))

def fourthP005Center2545 : RatPair2542 := (((76397704122214015 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP005Error2545 : ℝ := ((9158116517101 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

noncomputable def fourthP005ExpUpper2545 : ℝ := ((84000164017764766031806997741 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

noncomputable def fourthP005Frequency2545 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def fourthP005Upper2545 : ℝ := ((4498800519068166235 : ℝ) /
        79228162514264337593543950336)

noncomputable def fourthP005Exponent2545 : ℝ := (((-((38144 * 10^40
        + 8841461898211752119661724894242293216339) * 10^40
        + 3153870498936871630788029349009739950359)) : ℝ) /
        ((1253 * 10^40
        + 1175397596394516637903543943382186493278) * 10^40
        + 7966451272695041301986244497510400000000))

theorem fourthP005ExpBound2545 :
    Real.exp fourthP005Exponent2545 ≤ fourthP005ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP005Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP005Input2545]
  have hc : (compactExp2542 fourthP005Input2545 5).1 = fourthP005Center2545 := by cbv
  have he : ((compactExp2542 fourthP005Input2545 5).2 : ℝ) = fourthP005Error2545 := by
    have hq : (compactExp2542 fourthP005Input2545 5).2 =
        ((9158116517101 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [fourthP005Error2545]
  have h := compactExp_error2542 fourthP005Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP005Input2545 =
      (fourthP005Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP005Input2545, fourthP005Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP005Exponent2545 : ℂ)) (embedPair2542 fourthP005Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP005Center2545))).trans
  norm_num [fourthP005Error2545, fourthP005ExpUpper2545, pairMagnitude2542, fourthP005Center2545]

theorem fourthP005Bound2545 : fourthCellTerm2544 ⟨5, by omega⟩ ≤ fourthP005Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨5, by omega⟩)‖ ≤
      fourthP005Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP005Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP005Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    ((14311268216336621374914235141089 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1118067829401298544915174620397578125) ((271277232588203098280784780144410624 : ℝ) /
        1863446382335497574858624367329296875) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP005ExpBound2545 using 1; norm_num [fourthP005Exponent2545])
  have hid : fourthCellTerm2544 ⟨5, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨5, by omega⟩)
        ((14311268216336621374914235141089 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1118067829401298544915174620397578125) ((271277232588203098280784780144410624 : ℝ) /
        1863446382335497574858624367329296875) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP005ExpUpper2545, fourthP005Frequency2545, fourthP005Upper2545]

def fourthP006Input2545 : RatPair2542 := ((((-416588258400859524715053056107) : ℚ) /
        442701176911656822374400000000),
    ((0 : ℚ) /
        1))

def fourthP006Center2545 : RatPair2542 := (((106003844822497371 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP006Error2545 : ℝ := ((11756624699907 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

noncomputable def fourthP006ExpUpper2545 : ℝ := ((116552459971298605930315276803 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

noncomputable def fourthP006Frequency2545 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def fourthP006Upper2545 : ℝ := ((15700621622015810429 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP006Exponent2545 : ℝ := (((-416588258400859524715053056107) : ℝ) /
        13834411778489275699200000000)

theorem fourthP006ExpBound2545 :
    Real.exp fourthP006Exponent2545 ≤ fourthP006ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP006Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP006Input2545]
  have hc : (compactExp2542 fourthP006Input2545 5).1 = fourthP006Center2545 := by cbv
  have he : ((compactExp2542 fourthP006Input2545 5).2 : ℝ) = fourthP006Error2545 := by
    have hq : (compactExp2542 fourthP006Input2545 5).2 =
        ((11756624699907 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [fourthP006Error2545]
  have h := compactExp_error2542 fourthP006Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP006Input2545 =
      (fourthP006Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP006Input2545, fourthP006Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP006Exponent2545 : ℂ)) (embedPair2542 fourthP006Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP006Center2545))).trans
  norm_num [fourthP006Error2545, fourthP006ExpUpper2545, pairMagnitude2542, fourthP006Center2545]

theorem fourthP006Bound2545 : fourthCellTerm2544 ⟨6, by omega⟩ ≤ fourthP006Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨6, by omega⟩)‖ ≤
      fourthP006Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP006Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP006Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (4 : ℝ) ((65536001 : ℝ) /
        640000000) ((21037056321 : ℝ) /
        204800000000) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP006ExpBound2545 using 1; norm_num [fourthP006Exponent2545])
  have hid : fourthCellTerm2544 ⟨6, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
        (4 : ℝ) ((65536001 : ℝ) /
        640000000) ((21037056321 : ℝ) /
        204800000000) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP006ExpUpper2545, fourthP006Frequency2545, fourthP006Upper2545]

def fourthP007Input2545 : RatPair2542 := ((((-((46236 * 10^40
        + 4131255514699533833354090203640434616631) * 10^40
        + 4783606347868318382953483916336579983453)) : ℚ) /
        ((49369 * 10^40
        + 3492025268854919357832426692645219513656) * 10^40
        + 8418178538425671914519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP007Center2545 : RatPair2542 := (((30579796410523877 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def fourthP007Error2545 : ℝ := ((6589216220027 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

noncomputable def fourthP007ExpUpper2545 : ℝ := ((67245683456787586463585035131 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

noncomputable def fourthP007Frequency2545 : ℝ := ((549755813889 : ℝ) /
        1099511627776)

noncomputable def fourthP007Upper2545 : ℝ := ((2264083415261489869 : ℝ) /
        633825300114114700748351602688)

noncomputable def fourthP007Exponent2545 : ℝ := (((-((46236 * 10^40
        + 4131255514699533833354090203640434616631) * 10^40
        + 4783606347868318382953483916336579983453)) : ℝ) /
        ((1542 * 10^40
        + 7921625789651716229932263334145163109801) * 10^40
        + 7763068079325802247328748165836800000000))

theorem fourthP007ExpBound2545 :
    Real.exp fourthP007Exponent2545 ≤ fourthP007ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP007Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP007Input2545]
  have hc : (compactExp2542 fourthP007Input2545 5).1 = fourthP007Center2545 := by cbv
  have he : ((compactExp2542 fourthP007Input2545 5).2 : ℝ) = fourthP007Error2545 := by
    have hq : (compactExp2542 fourthP007Input2545 5).2 =
        ((6589216220027 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [fourthP007Error2545]
  have h := compactExp_error2542 fourthP007Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP007Input2545 =
      (fourthP007Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP007Input2545, fourthP007Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP007Exponent2545 : ℂ)) (embedPair2542 fourthP007Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP007Center2545))).trans
  norm_num [fourthP007Error2545, fourthP007ExpUpper2545, pairMagnitude2542, fourthP007Center2545]

theorem fourthP007Bound2545 : fourthCellTerm2544 ⟨7, by omega⟩ ≤ fourthP007Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨7, by omega⟩)‖ ≤
      fourthP007Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP007Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP007Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
    ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        2132188309583881559457579105517578125) ((813831697764609294842354340433231872 : ℝ) /
        10660941547919407797287895527587890625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP007ExpBound2545 using 1; norm_num [fourthP007Exponent2545])
  have hid : fourthCellTerm2544 ⟨7, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
        ((27292010362673683961057012550625 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        2132188309583881559457579105517578125) ((813831697764609294842354340433231872 : ℝ) /
        10660941547919407797287895527587890625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP007ExpUpper2545, fourthP007Frequency2545, fourthP007Upper2545]

def fourthP008Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP008Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP008Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP008ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP008Frequency2545 : ℝ := ((1943876888199 : ℝ) /
        137438953472)

noncomputable def fourthP008Upper2545 : ℝ := ((7739308147116427011335 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP008Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP008ExpBound2545 :
    Real.exp fourthP008Exponent2545 ≤ fourthP008ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP008Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP008Input2545]
  have hc : (compactExp2542 fourthP008Input2545 5).1 = fourthP008Center2545 := by cbv
  have he : ((compactExp2542 fourthP008Input2545 5).2 : ℝ) = fourthP008Error2545 := by
    have hq : (compactExp2542 fourthP008Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP008Error2545]
  have h := compactExp_error2542 fourthP008Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP008Input2545 =
      (fourthP008Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP008Input2545, fourthP008Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP008Exponent2545 : ℂ)) (embedPair2542 fourthP008Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP008Center2545))).trans
  norm_num [fourthP008Error2545, fourthP008ExpUpper2545, pairMagnitude2542, fourthP008Center2545]

theorem fourthP008Bound2545 : fourthCellTerm2544 ⟨8, by omega⟩ ≤ fourthP008Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨8, by omega⟩)‖ ≤
      fourthP008Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP008Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP008Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP008ExpBound2545 using 1; norm_num [fourthP008Exponent2545])
  have hid : fourthCellTerm2544 ⟨8, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP008ExpUpper2545, fourthP008Frequency2545, fourthP008Upper2545]

def fourthP009Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP009Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP009Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP009ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP009Frequency2545 : ℝ := ((5780128487147 : ℝ) /
        274877906944)

noncomputable def fourthP009Upper2545 : ℝ := ((28744158992612224250513 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP009Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP009ExpBound2545 :
    Real.exp fourthP009Exponent2545 ≤ fourthP009ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP009Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP009Input2545]
  have hc : (compactExp2542 fourthP009Input2545 5).1 = fourthP009Center2545 := by cbv
  have he : ((compactExp2542 fourthP009Input2545 5).2 : ℝ) = fourthP009Error2545 := by
    have hq : (compactExp2542 fourthP009Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP009Error2545]
  have h := compactExp_error2542 fourthP009Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP009Input2545 =
      (fourthP009Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP009Input2545, fourthP009Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP009Exponent2545 : ℂ)) (embedPair2542 fourthP009Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP009Center2545))).trans
  norm_num [fourthP009Error2545, fourthP009ExpUpper2545, pairMagnitude2542, fourthP009Center2545]

theorem fourthP009Bound2545 : fourthCellTerm2544 ⟨9, by omega⟩ ≤ fourthP009Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨9, by omega⟩)‖ ≤
      fourthP009Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP009Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP009Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP009ExpBound2545 using 1; norm_num [fourthP009Exponent2545])
  have hid : fourthCellTerm2544 ⟨9, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP009ExpUpper2545, fourthP009Frequency2545, fourthP009Upper2545]

def fourthP010Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP010Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP010Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP010ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP010Frequency2545 : ℝ := ((13752611676329 : ℝ) /
        549755813888)

noncomputable def fourthP010Upper2545 : ℝ := ((52641203320902409110363 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP010Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP010ExpBound2545 :
    Real.exp fourthP010Exponent2545 ≤ fourthP010ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP010Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP010Input2545]
  have hc : (compactExp2542 fourthP010Input2545 5).1 = fourthP010Center2545 := by cbv
  have he : ((compactExp2542 fourthP010Input2545 5).2 : ℝ) = fourthP010Error2545 := by
    have hq : (compactExp2542 fourthP010Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP010Error2545]
  have h := compactExp_error2542 fourthP010Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP010Input2545 =
      (fourthP010Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP010Input2545, fourthP010Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP010Exponent2545 : ℂ)) (embedPair2542 fourthP010Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP010Center2545))).trans
  norm_num [fourthP010Error2545, fourthP010ExpUpper2545, pairMagnitude2542, fourthP010Center2545]

theorem fourthP010Bound2545 : fourthCellTerm2544 ⟨10, by omega⟩ ≤ fourthP010Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨10, by omega⟩)‖ ≤
      fourthP010Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP010Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP010Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP010ExpBound2545 using 1; norm_num [fourthP010Exponent2545])
  have hid : fourthCellTerm2544 ⟨10, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP010ExpUpper2545, fourthP010Frequency2545, fourthP010Upper2545]

def fourthP011Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP011Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP011Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP011ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP011Frequency2545 : ℝ := ((30428807318125 : ℝ) /
        1099511627776)

noncomputable def fourthP011Upper2545 : ℝ := ((75368610199749212552991 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP011Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP011ExpBound2545 :
    Real.exp fourthP011Exponent2545 ≤ fourthP011ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP011Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP011Input2545]
  have hc : (compactExp2542 fourthP011Input2545 5).1 = fourthP011Center2545 := by cbv
  have he : ((compactExp2542 fourthP011Input2545 5).2 : ℝ) = fourthP011Error2545 := by
    have hq : (compactExp2542 fourthP011Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP011Error2545]
  have h := compactExp_error2542 fourthP011Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP011Input2545 =
      (fourthP011Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP011Input2545, fourthP011Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP011Exponent2545 : ℂ)) (embedPair2542 fourthP011Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP011Center2545))).trans
  norm_num [fourthP011Error2545, fourthP011ExpUpper2545, pairMagnitude2542, fourthP011Center2545]

theorem fourthP011Bound2545 : fourthCellTerm2544 ⟨11, by omega⟩ ≤ fourthP011Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨11, by omega⟩)‖ ≤
      fourthP011Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP011Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP011Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP011ExpBound2545 using 1; norm_num [fourthP011Exponent2545])
  have hid : fourthCellTerm2544 ⟨11, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP011ExpUpper2545, fourthP011Frequency2545, fourthP011Upper2545]

def fourthP012Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP012Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP012Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP012ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP012Frequency2545 : ℝ := ((33457022090777 : ℝ) /
        1099511627776)

noncomputable def fourthP012Upper2545 : ℝ := ((26503564498030932648315 : ℝ) /
        316912650057057350374175801344)

noncomputable def fourthP012Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP012ExpBound2545 :
    Real.exp fourthP012Exponent2545 ≤ fourthP012ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP012Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP012Input2545]
  have hc : (compactExp2542 fourthP012Input2545 5).1 = fourthP012Center2545 := by cbv
  have he : ((compactExp2542 fourthP012Input2545 5).2 : ℝ) = fourthP012Error2545 := by
    have hq : (compactExp2542 fourthP012Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP012Error2545]
  have h := compactExp_error2542 fourthP012Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP012Input2545 =
      (fourthP012Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP012Input2545, fourthP012Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP012Exponent2545 : ℂ)) (embedPair2542 fourthP012Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP012Center2545))).trans
  norm_num [fourthP012Error2545, fourthP012ExpUpper2545, pairMagnitude2542, fourthP012Center2545]

theorem fourthP012Bound2545 : fourthCellTerm2544 ⟨12, by omega⟩ ≤ fourthP012Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨12, by omega⟩)‖ ≤
      fourthP012Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP012Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP012Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP012ExpBound2545 using 1; norm_num [fourthP012Exponent2545])
  have hid : fourthCellTerm2544 ⟨12, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP012ExpUpper2545, fourthP012Frequency2545, fourthP012Upper2545]

def fourthP013Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP013Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP013Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP013ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP013Frequency2545 : ℝ := ((36216655965407 : ℝ) /
        1099511627776)

noncomputable def fourthP013Upper2545 : ℝ := ((4417845766965233541579 : ℝ) /
        39614081257132168796771975168)

noncomputable def fourthP013Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP013ExpBound2545 :
    Real.exp fourthP013Exponent2545 ≤ fourthP013ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP013Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP013Input2545]
  have hc : (compactExp2542 fourthP013Input2545 5).1 = fourthP013Center2545 := by cbv
  have he : ((compactExp2542 fourthP013Input2545 5).2 : ℝ) = fourthP013Error2545 := by
    have hq : (compactExp2542 fourthP013Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP013Error2545]
  have h := compactExp_error2542 fourthP013Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP013Input2545 =
      (fourthP013Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP013Input2545, fourthP013Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP013Exponent2545 : ℂ)) (embedPair2542 fourthP013Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP013Center2545))).trans
  norm_num [fourthP013Error2545, fourthP013ExpUpper2545, pairMagnitude2542, fourthP013Center2545]

theorem fourthP013Bound2545 : fourthCellTerm2544 ⟨13, by omega⟩ ≤ fourthP013Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨13, by omega⟩)‖ ≤
      fourthP013Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP013Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP013Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP013ExpBound2545 using 1; norm_num [fourthP013Exponent2545])
  have hid : fourthCellTerm2544 ⟨13, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP013ExpUpper2545, fourthP013Frequency2545, fourthP013Upper2545]

def fourthP014Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP014Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP014Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP014ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP014Frequency2545 : ℝ := ((20665048201517 : ℝ) /
        549755813888)

noncomputable def fourthP014Upper2545 : ℝ := ((114769150901105881473703 : ℝ) /
        633825300114114700748351602688)

noncomputable def fourthP014Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP014ExpBound2545 :
    Real.exp fourthP014Exponent2545 ≤ fourthP014ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP014Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP014Input2545]
  have hc : (compactExp2542 fourthP014Input2545 5).1 = fourthP014Center2545 := by cbv
  have he : ((compactExp2542 fourthP014Input2545 5).2 : ℝ) = fourthP014Error2545 := by
    have hq : (compactExp2542 fourthP014Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP014Error2545]
  have h := compactExp_error2542 fourthP014Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP014Input2545 =
      (fourthP014Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP014Input2545, fourthP014Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP014Exponent2545 : ℂ)) (embedPair2542 fourthP014Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP014Center2545))).trans
  norm_num [fourthP014Error2545, fourthP014ExpUpper2545, pairMagnitude2542, fourthP014Center2545]

theorem fourthP014Bound2545 : fourthCellTerm2544 ⟨14, by omega⟩ ≤ fourthP014Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨14, by omega⟩)‖ ≤
      fourthP014Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP014Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP014Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP014ExpBound2545 using 1; norm_num [fourthP014Exponent2545])
  have hid : fourthCellTerm2544 ⟨14, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP014ExpUpper2545, fourthP014Frequency2545, fourthP014Upper2545]

def fourthP015Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP015Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP015Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP015ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP015Frequency2545 : ℝ := ((5624245756317 : ℝ) /
        137438953472)

noncomputable def fourthP015Upper2545 : ℝ := ((314443513590136502845365 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP015Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP015ExpBound2545 :
    Real.exp fourthP015Exponent2545 ≤ fourthP015ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP015Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP015Input2545]
  have hc : (compactExp2542 fourthP015Input2545 5).1 = fourthP015Center2545 := by cbv
  have he : ((compactExp2542 fourthP015Input2545 5).2 : ℝ) = fourthP015Error2545 := by
    have hq : (compactExp2542 fourthP015Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP015Error2545]
  have h := compactExp_error2542 fourthP015Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP015Input2545 =
      (fourthP015Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP015Input2545, fourthP015Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP015Exponent2545 : ℂ)) (embedPair2542 fourthP015Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP015Center2545))).trans
  norm_num [fourthP015Error2545, fourthP015ExpUpper2545, pairMagnitude2542, fourthP015Center2545]

theorem fourthP015Bound2545 : fourthCellTerm2544 ⟨15, by omega⟩ ≤ fourthP015Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨15, by omega⟩)‖ ≤
      fourthP015Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP015Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP015Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP015ExpBound2545 using 1; norm_num [fourthP015Exponent2545])
  have hid : fourthCellTerm2544 ⟨15, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP015ExpUpper2545, fourthP015Frequency2545, fourthP015Upper2545]

def fourthP016Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP016Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP016Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP016ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP016Frequency2545 : ℝ := ((11910448222669 : ℝ) /
        274877906944)

noncomputable def fourthP016Upper2545 : ℝ := ((389126529943904421979705 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP016Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP016ExpBound2545 :
    Real.exp fourthP016Exponent2545 ≤ fourthP016ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP016Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP016Input2545]
  have hc : (compactExp2542 fourthP016Input2545 5).1 = fourthP016Center2545 := by cbv
  have he : ((compactExp2542 fourthP016Input2545 5).2 : ℝ) = fourthP016Error2545 := by
    have hq : (compactExp2542 fourthP016Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP016Error2545]
  have h := compactExp_error2542 fourthP016Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP016Input2545 =
      (fourthP016Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP016Input2545, fourthP016Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP016Exponent2545 : ℂ)) (embedPair2542 fourthP016Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP016Center2545))).trans
  norm_num [fourthP016Error2545, fourthP016ExpUpper2545, pairMagnitude2542, fourthP016Center2545]

theorem fourthP016Bound2545 : fourthCellTerm2544 ⟨16, by omega⟩ ≤ fourthP016Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨16, by omega⟩)‖ ≤
      fourthP016Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP016Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP016Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP016ExpBound2545 using 1; norm_num [fourthP016Exponent2545])
  have hid : fourthCellTerm2544 ⟨16, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP016ExpUpper2545, fourthP016Frequency2545, fourthP016Upper2545]

def fourthP017Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP017Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP017Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP017ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP017Frequency2545 : ℝ := ((13196271128411 : ℝ) /
        274877906944)

noncomputable def fourthP017Upper2545 : ℝ := ((571464797606657364358429 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP017Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP017ExpBound2545 :
    Real.exp fourthP017Exponent2545 ≤ fourthP017ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP017Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP017Input2545]
  have hc : (compactExp2542 fourthP017Input2545 5).1 = fourthP017Center2545 := by cbv
  have he : ((compactExp2542 fourthP017Input2545 5).2 : ℝ) = fourthP017Error2545 := by
    have hq : (compactExp2542 fourthP017Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP017Error2545]
  have h := compactExp_error2542 fourthP017Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP017Input2545 =
      (fourthP017Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP017Input2545, fourthP017Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP017Exponent2545 : ℂ)) (embedPair2542 fourthP017Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP017Center2545))).trans
  norm_num [fourthP017Error2545, fourthP017ExpUpper2545, pairMagnitude2542, fourthP017Center2545]

theorem fourthP017Bound2545 : fourthCellTerm2544 ⟨17, by omega⟩ ≤ fourthP017Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨17, by omega⟩)‖ ≤
      fourthP017Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP017Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP017Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP017ExpBound2545 using 1; norm_num [fourthP017Exponent2545])
  have hid : fourthCellTerm2544 ⟨17, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP017ExpUpper2545, fourthP017Frequency2545, fourthP017Upper2545]

def fourthP018Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP018Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP018Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP018ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP018Frequency2545 : ℝ := ((54729668767777 : ℝ) /
        1099511627776)

noncomputable def fourthP018Upper2545 : ℝ := ((654884046984977010782495 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP018Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP018ExpBound2545 :
    Real.exp fourthP018Exponent2545 ≤ fourthP018ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP018Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP018Input2545]
  have hc : (compactExp2542 fourthP018Input2545 5).1 = fourthP018Center2545 := by cbv
  have he : ((compactExp2542 fourthP018Input2545 5).2 : ℝ) = fourthP018Error2545 := by
    have hq : (compactExp2542 fourthP018Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP018Error2545]
  have h := compactExp_error2542 fourthP018Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP018Input2545 =
      (fourthP018Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP018Input2545, fourthP018Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP018Exponent2545 : ℂ)) (embedPair2542 fourthP018Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP018Center2545))).trans
  norm_num [fourthP018Error2545, fourthP018ExpUpper2545, pairMagnitude2542, fourthP018Center2545]

theorem fourthP018Bound2545 : fourthCellTerm2544 ⟨18, by omega⟩ ≤ fourthP018Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨18, by omega⟩)‖ ≤
      fourthP018Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP018Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP018Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP018ExpBound2545 using 1; norm_num [fourthP018Exponent2545])
  have hid : fourthCellTerm2544 ⟨18, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP018ExpUpper2545, fourthP018Frequency2545, fourthP018Upper2545]

def fourthP019Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP019Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP019Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP019ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP019Frequency2545 : ℝ := ((14561019743679 : ℝ) /
        274877906944)

noncomputable def fourthP019Upper2545 : ℝ := ((828478058502365959263817 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP019Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP019ExpBound2545 :
    Real.exp fourthP019Exponent2545 ≤ fourthP019ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP019Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP019Input2545]
  have hc : (compactExp2542 fourthP019Input2545 5).1 = fourthP019Center2545 := by cbv
  have he : ((compactExp2542 fourthP019Input2545 5).2 : ℝ) = fourthP019Error2545 := by
    have hq : (compactExp2542 fourthP019Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP019Error2545]
  have h := compactExp_error2542 fourthP019Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP019Input2545 =
      (fourthP019Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP019Input2545, fourthP019Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP019Exponent2545 : ℂ)) (embedPair2542 fourthP019Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP019Center2545))).trans
  norm_num [fourthP019Error2545, fourthP019ExpUpper2545, pairMagnitude2542, fourthP019Center2545]

theorem fourthP019Bound2545 : fourthCellTerm2544 ⟨19, by omega⟩ ≤ fourthP019Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨19, by omega⟩)‖ ≤
      fourthP019Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP019Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP019Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP019ExpBound2545 using 1; norm_num [fourthP019Exponent2545])
  have hid : fourthCellTerm2544 ⟨19, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP019ExpUpper2545, fourthP019Frequency2545, fourthP019Upper2545]

def fourthP020Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP020Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP020Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP020ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP020Frequency2545 : ℝ := ((62065740503787 : ℝ) /
        1099511627776)

noncomputable def fourthP020Upper2545 : ℝ := ((1054256283122792160329897 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP020Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP020ExpBound2545 :
    Real.exp fourthP020Exponent2545 ≤ fourthP020ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP020Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP020Input2545]
  have hc : (compactExp2542 fourthP020Input2545 5).1 = fourthP020Center2545 := by cbv
  have he : ((compactExp2542 fourthP020Input2545 5).2 : ℝ) = fourthP020Error2545 := by
    have hq : (compactExp2542 fourthP020Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP020Error2545]
  have h := compactExp_error2542 fourthP020Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP020Input2545 =
      (fourthP020Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP020Input2545, fourthP020Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP020Exponent2545 : ℂ)) (embedPair2542 fourthP020Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP020Center2545))).trans
  norm_num [fourthP020Error2545, fourthP020ExpUpper2545, pairMagnitude2542, fourthP020Center2545]

theorem fourthP020Bound2545 : fourthCellTerm2544 ⟨20, by omega⟩ ≤ fourthP020Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨20, by omega⟩)‖ ≤
      fourthP020Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP020Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP020Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP020ExpBound2545 using 1; norm_num [fourthP020Exponent2545])
  have hid : fourthCellTerm2544 ⟨20, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP020ExpUpper2545, fourthP020Frequency2545, fourthP020Upper2545]

def fourthP021Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP021Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP021Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP021ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP021Frequency2545 : ℝ := ((32627540382807 : ℝ) /
        549755813888)

noncomputable def fourthP021Upper2545 : ℝ := ((637829934264275348400953 : ℝ) /
        633825300114114700748351602688)

noncomputable def fourthP021Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP021ExpBound2545 :
    Real.exp fourthP021Exponent2545 ≤ fourthP021ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP021Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP021Input2545]
  have hc : (compactExp2542 fourthP021Input2545 5).1 = fourthP021Center2545 := by cbv
  have he : ((compactExp2542 fourthP021Input2545 5).2 : ℝ) = fourthP021Error2545 := by
    have hq : (compactExp2542 fourthP021Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP021Error2545]
  have h := compactExp_error2542 fourthP021Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP021Input2545 =
      (fourthP021Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP021Input2545, fourthP021Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP021Exponent2545 : ℂ)) (embedPair2542 fourthP021Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP021Center2545))).trans
  norm_num [fourthP021Error2545, fourthP021ExpUpper2545, pairMagnitude2542, fourthP021Center2545]

theorem fourthP021Bound2545 : fourthCellTerm2544 ⟨21, by omega⟩ ≤ fourthP021Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨21, by omega⟩)‖ ≤
      fourthP021Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP021Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP021Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP021ExpBound2545 using 1; norm_num [fourthP021Exponent2545])
  have hid : fourthCellTerm2544 ⟨21, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP021ExpUpper2545, fourthP021Frequency2545, fourthP021Upper2545]

def fourthP022Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP022Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP022Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP022ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP022Frequency2545 : ℝ := ((66887507116159 : ℝ) /
        1099511627776)

noncomputable def fourthP022Upper2545 : ℝ := ((1401643080508148049939407 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP022Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP022ExpBound2545 :
    Real.exp fourthP022Exponent2545 ≤ fourthP022ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP022Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP022Input2545]
  have hc : (compactExp2542 fourthP022Input2545 5).1 = fourthP022Center2545 := by cbv
  have he : ((compactExp2542 fourthP022Input2545 5).2 : ℝ) = fourthP022Error2545 := by
    have hq : (compactExp2542 fourthP022Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP022Error2545]
  have h := compactExp_error2542 fourthP022Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP022Input2545 =
      (fourthP022Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP022Input2545, fourthP022Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP022Exponent2545 : ℂ)) (embedPair2542 fourthP022Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP022Center2545))).trans
  norm_num [fourthP022Error2545, fourthP022ExpUpper2545, pairMagnitude2542, fourthP022Center2545]

theorem fourthP022Bound2545 : fourthCellTerm2544 ⟨22, by omega⟩ ≤ fourthP022Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨22, by omega⟩)‖ ≤
      fourthP022Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP022Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP022Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP022ExpBound2545 using 1; norm_num [fourthP022Exponent2545])
  have hid : fourthCellTerm2544 ⟨22, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP022ExpUpper2545, fourthP022Frequency2545, fourthP022Upper2545]

def fourthP023Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP023Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP023Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP023ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP023Frequency2545 : ℝ := ((71594110054543 : ℝ) /
        1099511627776)

noncomputable def fourthP023Upper2545 : ℝ := ((1817476229525463923416321 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP023Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP023ExpBound2545 :
    Real.exp fourthP023Exponent2545 ≤ fourthP023ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP023Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP023Input2545]
  have hc : (compactExp2542 fourthP023Input2545 5).1 = fourthP023Center2545 := by cbv
  have he : ((compactExp2542 fourthP023Input2545 5).2 : ℝ) = fourthP023Error2545 := by
    have hq : (compactExp2542 fourthP023Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP023Error2545]
  have h := compactExp_error2542 fourthP023Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP023Input2545 =
      (fourthP023Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP023Input2545, fourthP023Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP023Exponent2545 : ℂ)) (embedPair2542 fourthP023Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP023Center2545))).trans
  norm_num [fourthP023Error2545, fourthP023ExpUpper2545, pairMagnitude2542, fourthP023Center2545]

theorem fourthP023Bound2545 : fourthCellTerm2544 ⟨23, by omega⟩ ≤ fourthP023Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨23, by omega⟩)‖ ≤
      fourthP023Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP023Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP023Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP023ExpBound2545 using 1; norm_num [fourthP023Exponent2545])
  have hid : fourthCellTerm2544 ⟨23, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP023ExpUpper2545, fourthP023Frequency2545, fourthP023Upper2545]

def fourthP024Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP024Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP024Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP024ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP024Frequency2545 : ℝ := ((36878540262379 : ℝ) /
        549755813888)

noncomputable def fourthP024Upper2545 : ℝ := ((2036907543114826263747987 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP024Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP024ExpBound2545 :
    Real.exp fourthP024Exponent2545 ≤ fourthP024ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP024Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP024Input2545]
  have hc : (compactExp2542 fourthP024Input2545 5).1 = fourthP024Center2545 := by cbv
  have he : ((compactExp2542 fourthP024Input2545 5).2 : ℝ) = fourthP024Error2545 := by
    have hq : (compactExp2542 fourthP024Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP024Error2545]
  have h := compactExp_error2542 fourthP024Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP024Input2545 =
      (fourthP024Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP024Input2545, fourthP024Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP024Exponent2545 : ℂ)) (embedPair2542 fourthP024Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP024Center2545))).trans
  norm_num [fourthP024Error2545, fourthP024ExpUpper2545, pairMagnitude2542, fourthP024Center2545]

theorem fourthP024Bound2545 : fourthCellTerm2544 ⟨24, by omega⟩ ≤ fourthP024Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨24, by omega⟩)‖ ≤
      fourthP024Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP024Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP024Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP024ExpBound2545 using 1; norm_num [fourthP024Exponent2545])
  have hid : fourthCellTerm2544 ⟨24, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP024ExpUpper2545, fourthP024Frequency2545, fourthP024Upper2545]

def fourthP025Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP025Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP025Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP025ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP025Frequency2545 : ℝ := ((19117263386339 : ℝ) /
        274877906944)

noncomputable def fourthP025Upper2545 : ℝ := ((584866558683931280231505 : ℝ) /
        316912650057057350374175801344)

noncomputable def fourthP025Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP025ExpBound2545 :
    Real.exp fourthP025Exponent2545 ≤ fourthP025ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP025Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP025Input2545]
  have hc : (compactExp2542 fourthP025Input2545 5).1 = fourthP025Center2545 := by cbv
  have he : ((compactExp2542 fourthP025Input2545 5).2 : ℝ) = fourthP025Error2545 := by
    have hq : (compactExp2542 fourthP025Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP025Error2545]
  have h := compactExp_error2542 fourthP025Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP025Input2545 =
      (fourthP025Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP025Input2545, fourthP025Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP025Exponent2545 : ℂ)) (embedPair2542 fourthP025Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP025Center2545))).trans
  norm_num [fourthP025Error2545, fourthP025ExpUpper2545, pairMagnitude2542, fourthP025Center2545]

theorem fourthP025Bound2545 : fourthCellTerm2544 ⟨25, by omega⟩ ≤ fourthP025Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨25, by omega⟩)‖ ≤
      fourthP025Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP025Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP025Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP025ExpBound2545 using 1; norm_num [fourthP025Exponent2545])
  have hid : fourthCellTerm2544 ⟨25, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP025ExpUpper2545, fourthP025Frequency2545, fourthP025Upper2545]

def fourthP026Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP026Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP026Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP026ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP026Frequency2545 : ℝ := ((39620292458215 : ℝ) /
        549755813888)

noncomputable def fourthP026Upper2545 : ℝ := ((2682327260219151680432401 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP026Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP026ExpBound2545 :
    Real.exp fourthP026Exponent2545 ≤ fourthP026ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP026Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP026Input2545]
  have hc : (compactExp2542 fourthP026Input2545 5).1 = fourthP026Center2545 := by cbv
  have he : ((compactExp2542 fourthP026Input2545 5).2 : ℝ) = fourthP026Error2545 := by
    have hq : (compactExp2542 fourthP026Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP026Error2545]
  have h := compactExp_error2542 fourthP026Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP026Input2545 =
      (fourthP026Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP026Input2545, fourthP026Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP026Exponent2545 : ℂ)) (embedPair2542 fourthP026Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP026Center2545))).trans
  norm_num [fourthP026Error2545, fourthP026ExpUpper2545, pairMagnitude2542, fourthP026Center2545]

theorem fourthP026Bound2545 : fourthCellTerm2544 ⟨26, by omega⟩ ≤ fourthP026Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨26, by omega⟩)‖ ≤
      fourthP026Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP026Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP026Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP026ExpBound2545 using 1; norm_num [fourthP026Exponent2545])
  have hid : fourthCellTerm2544 ⟨26, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP026ExpUpper2545, fourthP026Frequency2545, fourthP026Upper2545]

def fourthP027Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP027Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP027Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP027ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP027Frequency2545 : ℝ := ((2601250098205 : ℝ) /
        34359738368)

noncomputable def fourthP027Upper2545 : ℝ := ((3241929252451074336970057 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP027Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP027ExpBound2545 :
    Real.exp fourthP027Exponent2545 ≤ fourthP027ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP027Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP027Input2545]
  have hc : (compactExp2542 fourthP027Input2545 5).1 = fourthP027Center2545 := by cbv
  have he : ((compactExp2542 fourthP027Input2545 5).2 : ℝ) = fourthP027Error2545 := by
    have hq : (compactExp2542 fourthP027Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP027Error2545]
  have h := compactExp_error2542 fourthP027Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP027Input2545 =
      (fourthP027Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP027Input2545, fourthP027Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP027Exponent2545 : ℂ)) (embedPair2542 fourthP027Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP027Center2545))).trans
  norm_num [fourthP027Error2545, fourthP027ExpUpper2545, pairMagnitude2542, fourthP027Center2545]

theorem fourthP027Bound2545 : fourthCellTerm2544 ⟨27, by omega⟩ ≤ fourthP027Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨27, by omega⟩)‖ ≤
      fourthP027Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP027Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP027Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP027ExpBound2545 using 1; norm_num [fourthP027Exponent2545])
  have hid : fourthCellTerm2544 ⟨27, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP027ExpUpper2545, fourthP027Frequency2545, fourthP027Upper2545]

def fourthP028Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP028Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP028Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP028ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP028Frequency2545 : ℝ := ((1325366097347 : ℝ) /
        17179869184)

noncomputable def fourthP028Upper2545 : ℝ := ((3486098669134526911770655 : ℝ) /
        1267650600228229401496703205376)

noncomputable def fourthP028Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP028ExpBound2545 :
    Real.exp fourthP028Exponent2545 ≤ fourthP028ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP028Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP028Input2545]
  have hc : (compactExp2542 fourthP028Input2545 5).1 = fourthP028Center2545 := by cbv
  have he : ((compactExp2542 fourthP028Input2545 5).2 : ℝ) = fourthP028Error2545 := by
    have hq : (compactExp2542 fourthP028Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP028Error2545]
  have h := compactExp_error2542 fourthP028Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP028Input2545 =
      (fourthP028Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP028Input2545, fourthP028Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP028Exponent2545 : ℂ)) (embedPair2542 fourthP028Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP028Center2545))).trans
  norm_num [fourthP028Error2545, fourthP028ExpUpper2545, pairMagnitude2542, fourthP028Center2545]

theorem fourthP028Bound2545 : fourthCellTerm2544 ⟨28, by omega⟩ ≤ fourthP028Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨28, by omega⟩)‖ ≤
      fourthP028Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP028Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP028Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP028ExpBound2545 using 1; norm_num [fourthP028Exponent2545])
  have hid : fourthCellTerm2544 ⟨28, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP028ExpUpper2545, fourthP028Frequency2545, fourthP028Upper2545]

def fourthP029Input2545 : RatPair2542 := ((((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℚ) /
        ((16159 * 10^40
        + 1180248473989860208709902636296257920925) * 10^40
        + 3719576026736442154519941306777600000000)),
    ((0 : ℚ) /
        1))

def fourthP029Center2545 : RatPair2542 := (((85412476027508291 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fourthP029Error2545 : ℝ := ((2488050855901 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP029ExpUpper2545 : ℝ := ((23478002637346057285737328605 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

noncomputable def fourthP029Frequency2545 : ℝ := ((87234098670317 : ℝ) /
        1099511627776)

noncomputable def fourthP029Upper2545 : ℝ := ((485502573622048181610829 : ℝ) /
        158456325028528675187087900672)

noncomputable def fourthP029Exponent2545 : ℝ := (((-((15315 * 10^40
        + 310838909752541464827080003200700873279) * 10^40
        + 7578970689991452100174623233035798733453)) : ℝ) /
        ((504 * 10^40
        + 9724382764812183131522184457384258060028) * 10^40
        + 9178736750835513817328748165836800000000))

theorem fourthP029ExpBound2545 :
    Real.exp fourthP029Exponent2545 ≤ fourthP029ExpUpper2545 := by
  have hz : ‖embedPair2542 fourthP029Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fourthP029Input2545]
  have hc : (compactExp2542 fourthP029Input2545 5).1 = fourthP029Center2545 := by cbv
  have he : ((compactExp2542 fourthP029Input2545 5).2 : ℝ) = fourthP029Error2545 := by
    have hq : (compactExp2542 fourthP029Input2545 5).2 =
        ((2488050855901 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [fourthP029Error2545]
  have h := compactExp_error2542 fourthP029Input2545 hz 5
  rw [hc, he] at h
  have ha : (2 : ℂ)^5 * embedPair2542 fourthP029Input2545 =
      (fourthP029Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, fourthP029Input2545, fourthP029Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp (fourthP029Exponent2545 : ℂ)) (embedPair2542 fourthP029Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 fourthP029Center2545))).trans
  norm_num [fourthP029Error2545, fourthP029ExpUpper2545, pairMagnitude2542, fourthP029Center2545]

theorem fourthP029Bound2545 : fourthCellTerm2544 ⟨29, by omega⟩ ≤ fourthP029Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨29, by omega⟩)‖ ≤
      fourthP029Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [fourthP029Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, fourthP029Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
    ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000)
    (by norm_num) (by norm_num) hf
    (by convert fourthP029ExpBound2545 using 1; norm_num [fourthP029Exponent2545])
  have hid : fourthCellTerm2544 ⟨29, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
        ((15706697997067857697999130365369 : ℝ) /
        5070602400912917605986812821504) ((162259279305093441962338560086376448 : ℝ) /
        1227085781020926382656182059794453125) ((813831697764609294842354340433231872 : ℝ) /
        6135428905104631913280910298972265625) ((65536001 : ℝ) /
        160000000) ((21037056321 : ℝ) /
        51200000000) := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    fourthP029ExpUpper2545, fourthP029Frequency2545, fourthP029Upper2545]

noncomputable def fourthUpper2545 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => fourthP000Upper2545
  | 1 => fourthP001Upper2545
  | 2 => fourthP002Upper2545
  | 3 => fourthP003Upper2545
  | 4 => fourthP004Upper2545
  | 5 => fourthP005Upper2545
  | 6 => fourthP006Upper2545
  | 7 => fourthP007Upper2545
  | 8 => fourthP008Upper2545
  | 9 => fourthP009Upper2545
  | 10 => fourthP010Upper2545
  | 11 => fourthP011Upper2545
  | 12 => fourthP012Upper2545
  | 13 => fourthP013Upper2545
  | 14 => fourthP014Upper2545
  | 15 => fourthP015Upper2545
  | 16 => fourthP016Upper2545
  | 17 => fourthP017Upper2545
  | 18 => fourthP018Upper2545
  | 19 => fourthP019Upper2545
  | 20 => fourthP020Upper2545
  | 21 => fourthP021Upper2545
  | 22 => fourthP022Upper2545
  | 23 => fourthP023Upper2545
  | 24 => fourthP024Upper2545
  | 25 => fourthP025Upper2545
  | 26 => fourthP026Upper2545
  | 27 => fourthP027Upper2545
  | 28 => fourthP028Upper2545
  | 29 => fourthP029Upper2545
  | _ => 0

theorem fourthBound2545 (i : Fin 30) :
    fourthCellTerm2544 i ≤ fourthUpper2545 i := by
  fin_cases i
  · exact fourthP000Bound2545
  · exact fourthP001Bound2545
  · exact fourthP002Bound2545
  · exact fourthP003Bound2545
  · exact fourthP004Bound2545
  · exact fourthP005Bound2545
  · exact fourthP006Bound2545
  · exact fourthP007Bound2545
  · exact fourthP008Bound2545
  · exact fourthP009Bound2545
  · exact fourthP010Bound2545
  · exact fourthP011Bound2545
  · exact fourthP012Bound2545
  · exact fourthP013Bound2545
  · exact fourthP014Bound2545
  · exact fourthP015Bound2545
  · exact fourthP016Bound2545
  · exact fourthP017Bound2545
  · exact fourthP018Bound2545
  · exact fourthP019Bound2545
  · exact fourthP020Bound2545
  · exact fourthP021Bound2545
  · exact fourthP022Bound2545
  · exact fourthP023Bound2545
  · exact fourthP024Bound2545
  · exact fourthP025Bound2545
  · exact fourthP026Bound2545
  · exact fourthP027Bound2545
  · exact fourthP028Bound2545
  · exact fourthP029Bound2545

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.fourthP000Bound2545
#print axioms ConnesWeilRH.Dev.fourthP001Bound2545
#print axioms ConnesWeilRH.Dev.fourthP002Bound2545
#print axioms ConnesWeilRH.Dev.fourthP003Bound2545
#print axioms ConnesWeilRH.Dev.fourthP004Bound2545
#print axioms ConnesWeilRH.Dev.fourthP005Bound2545
#print axioms ConnesWeilRH.Dev.fourthP006Bound2545
#print axioms ConnesWeilRH.Dev.fourthP007Bound2545
#print axioms ConnesWeilRH.Dev.fourthP008Bound2545
#print axioms ConnesWeilRH.Dev.fourthP009Bound2545
#print axioms ConnesWeilRH.Dev.fourthP010Bound2545
#print axioms ConnesWeilRH.Dev.fourthP011Bound2545
#print axioms ConnesWeilRH.Dev.fourthP012Bound2545
#print axioms ConnesWeilRH.Dev.fourthP013Bound2545
#print axioms ConnesWeilRH.Dev.fourthP014Bound2545
#print axioms ConnesWeilRH.Dev.fourthP015Bound2545
#print axioms ConnesWeilRH.Dev.fourthP016Bound2545
#print axioms ConnesWeilRH.Dev.fourthP017Bound2545
#print axioms ConnesWeilRH.Dev.fourthP018Bound2545
#print axioms ConnesWeilRH.Dev.fourthP019Bound2545
#print axioms ConnesWeilRH.Dev.fourthP020Bound2545
#print axioms ConnesWeilRH.Dev.fourthP021Bound2545
#print axioms ConnesWeilRH.Dev.fourthP022Bound2545
#print axioms ConnesWeilRH.Dev.fourthP023Bound2545
#print axioms ConnesWeilRH.Dev.fourthP024Bound2545
#print axioms ConnesWeilRH.Dev.fourthP025Bound2545
#print axioms ConnesWeilRH.Dev.fourthP026Bound2545
#print axioms ConnesWeilRH.Dev.fourthP027Bound2545
#print axioms ConnesWeilRH.Dev.fourthP028Bound2545
#print axioms ConnesWeilRH.Dev.fourthP029Bound2545
#print axioms ConnesWeilRH.Dev.fourthBound2545
