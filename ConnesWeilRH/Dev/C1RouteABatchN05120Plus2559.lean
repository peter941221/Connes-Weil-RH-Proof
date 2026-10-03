import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchN05120PlusPosition2559 : ℝ := (0 : ℝ)

theorem batchN05120PlusZero2559 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchN05120PlusP000Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP000Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP000Factor2559 : RatPair2542 := ((((-((155175452522516 * 10^40
        + 8005920621061128656130427631747926652837) * 10^40
        + 6030055604327408168023319727974010987307)) : ℚ) /
        ((66749594872 * 10^40
        + 5284548962318506942727519268385883402748) * 10^40
        + 9243245659617614299098425149393110827008)),
    ((((288997825733588484041635653223 * 10^40
        + 8880385975327210189151690898088934134671) * 10^40
        + 2407646547413021258897709715996926200677) : ℚ) /
        ((4697085165547667498741381 * 10^40
        + 768356370682624855505680397540936739965) * 10^40
        + 5035374300336975828176891131879921549312)))

noncomputable def batchN05120PlusP000Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP000BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP000Center2559‖ ≤ batchN05120PlusP000Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP000Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP000Input2559]
  have hs : compactExp2547 batchN05120PlusP000Input2559 5 =
      (batchN05120PlusP000Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP000Input2559 5).2 : ℝ) = batchN05120PlusP000Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP000Error2559]
  have h := compactExp_error2547 batchN05120PlusP000Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP000Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP000Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP000DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP000Factor2559 * embedPair2542 batchN05120PlusP000Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP000Factor2559 : ℝ) * batchN05120PlusP000Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨0, by omega⟩)
      (storedWidth ⟨0, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP000Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP000Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨0, by omega⟩) (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP000BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP000Factor2559)

def batchN05120PlusP001Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP001Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP001Factor2559 : RatPair2542 := ((((-((7343648209 * 10^40
        + 7296219816687569500204037485569329848452) * 10^40
        + 2313749498296375885494117799621498780483)) : ℚ) /
        ((3166923 * 10^40
        + 2480745485820119688393717804490482891877) * 10^40
        + 9519575789540571155506509342424854167552)),
    ((((13608563574846369252639315 * 10^40
        + 7060034034782331204074363181650455896748) * 10^40
        + 3222640112173494129171507853003099966413) : ℚ) /
        ((222852411874054654029 * 10^40
        + 798394683043711214321071936433049776734) * 10^40
        + 4242328557780022611377966369085511958528)))

noncomputable def batchN05120PlusP001Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP001BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP001Center2559‖ ≤ batchN05120PlusP001Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP001Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP001Input2559]
  have hs : compactExp2547 batchN05120PlusP001Input2559 5 =
      (batchN05120PlusP001Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP001Input2559 5).2 : ℝ) = batchN05120PlusP001Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP001Error2559]
  have h := compactExp_error2547 batchN05120PlusP001Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP001Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP001Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP001DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP001Factor2559 * embedPair2542 batchN05120PlusP001Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP001Factor2559 : ℝ) * batchN05120PlusP001Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP001Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP001Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP001BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP001Factor2559)

def batchN05120PlusP002Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP002Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP002Factor2559 : RatPair2542 := ((((-((191621174407 * 10^40
        + 7720046500335919845003215794567860171265) * 10^40
        + 5341844722247106309978740341975635213123)) : ℚ) /
        ((82744582 * 10^40
        + 4285713991961083790309698831162746993042) * 10^40
        + 68380853929144664363454055114197696512)),
    (((-((354169934077038200400071173 * 10^40
        + 4839212518465404009864441155957972286881) * 10^40
        + 4064213190345030408396463287506278779853)) : ℚ) /
        ((5822632353003772568342 * 10^40
        + 4653870626868288772898629841042207295567) * 10^40
        + 191058025379009561569719051440481107968)))

noncomputable def batchN05120PlusP002Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP002BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP002Center2559‖ ≤ batchN05120PlusP002Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP002Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP002Input2559]
  have hs : compactExp2547 batchN05120PlusP002Input2559 5 =
      (batchN05120PlusP002Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP002Input2559 5).2 : ℝ) = batchN05120PlusP002Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP002Error2559]
  have h := compactExp_error2547 batchN05120PlusP002Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP002Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP002Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP002DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP002Factor2559 * embedPair2542 batchN05120PlusP002Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP002Factor2559 : ℝ) * batchN05120PlusP002Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP002Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP002Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP002BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP002Factor2559)

def batchN05120PlusP003Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP003Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP003Factor2559 : RatPair2542 := ((((-((136563719058505 * 10^40
        + 2621174333980303643208823996938667723593) * 10^40
        + 1329184652384828105583685950789302685759)) : ℚ) /
        ((59013400263 * 10^40
        + 7959682641732496360117201973035022670721) * 10^40
        + 6694259663965200624126852763484160000000)),
    (((-((252039097585822557230624137951 * 10^40
        + 3686340614949988693114435628309462109582) * 10^40
        + 1219084950876653496022097084824369567761)) : ℚ) /
        ((4152698866217147703480778 * 10^40
        + 6809706781428960658984687503718859550986) * 10^40
        + 2176566536129324182572466689802240000000)))

noncomputable def batchN05120PlusP003Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP003BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP003Center2559‖ ≤ batchN05120PlusP003Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP003Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP003Input2559]
  have hs : compactExp2547 batchN05120PlusP003Input2559 5 =
      (batchN05120PlusP003Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP003Input2559 5).2 : ℝ) = batchN05120PlusP003Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP003Error2559]
  have h := compactExp_error2547 batchN05120PlusP003Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP003Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP003Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP003DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP003Factor2559 * embedPair2542 batchN05120PlusP003Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP003Factor2559 : ℝ) * batchN05120PlusP003Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP003Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP003Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP003BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP003Factor2559)

def batchN05120PlusP004Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP004Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP004Factor2559 : RatPair2542 := ((((-((439178406381 * 10^40
        + 2454968239663664844823387841976159314947) * 10^40
        + 7567830036411663130242979719746743684963)) : ℚ) /
        ((189865514 * 10^40
        + 3040810437680367122075567542449953814707) * 10^40
        + 1601760584676454714869316797782999171072)),
    ((((809832076657048031175451999 * 10^40
        + 9050090287550541567197056821761902762848) * 10^40
        + 9415827171593266479036061446773928766893) : ℚ) /
        ((13360597804224483857486 * 10^40
        + 253439397105425803564660780183932186144) * 10^40
        + 2957174189597660633935782696538297335808)))

noncomputable def batchN05120PlusP004Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP004BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP004Center2559‖ ≤ batchN05120PlusP004Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP004Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP004Input2559]
  have hs : compactExp2547 batchN05120PlusP004Input2559 5 =
      (batchN05120PlusP004Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP004Input2559 5).2 : ℝ) = batchN05120PlusP004Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP004Error2559]
  have h := compactExp_error2547 batchN05120PlusP004Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP004Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP004Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP004DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP004Factor2559 * embedPair2542 batchN05120PlusP004Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP004Factor2559 : ℝ) * batchN05120PlusP004Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP004Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP004Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP004BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP004Factor2559)

def batchN05120PlusP005Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP005Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP005Factor2559 : RatPair2542 := ((((-(203412376354484902155777 * 10^40
        + 9707068767718705087748490222159881749511)) : ℚ) /
        (18205546485326824908745 * 10^40
        + 4169023363300186656668414021354432094152)),
    ((0 : ℚ) /
        1))

noncomputable def batchN05120PlusP005Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP005BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP005Center2559‖ ≤ batchN05120PlusP005Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP005Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP005Input2559]
  have hs : compactExp2547 batchN05120PlusP005Input2559 5 =
      (batchN05120PlusP005Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP005Input2559 5).2 : ℝ) = batchN05120PlusP005Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP005Error2559]
  have h := compactExp_error2547 batchN05120PlusP005Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP005Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP005Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP005DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP005Factor2559 * embedPair2542 batchN05120PlusP005Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP005Factor2559 : ℝ) * batchN05120PlusP005Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨5, by omega⟩)
      (storedWidth ⟨5, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP005Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP005Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨5, by omega⟩) (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP005BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP005Factor2559)

def batchN05120PlusP006Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP006Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP006Factor2559 : RatPair2542 := ((((-11) : ℚ) /
        2),
    ((0 : ℚ) /
        1))

noncomputable def batchN05120PlusP006Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP006BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP006Center2559‖ ≤ batchN05120PlusP006Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP006Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP006Input2559]
  have hs : compactExp2547 batchN05120PlusP006Input2559 5 =
      (batchN05120PlusP006Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP006Input2559 5).2 : ℝ) = batchN05120PlusP006Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP006Error2559]
  have h := compactExp_error2547 batchN05120PlusP006Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP006Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP006Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP006DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP006Factor2559 * embedPair2542 batchN05120PlusP006Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP006Factor2559 : ℝ) * batchN05120PlusP006Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP006Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP006Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP006BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP006Factor2559)

def batchN05120PlusP007Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP007Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP007Factor2559 : RatPair2542 := ((((-(355341448804545604478143 * 10^40
        + 7414336392923100082342379118938896792179)) : ℚ) /
        (119176612741806040053794 * 10^40
        + 5971341165704888586842371486029100625000)),
    ((0 : ℚ) /
        1))

noncomputable def batchN05120PlusP007Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP007BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP007Center2559‖ ≤ batchN05120PlusP007Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP007Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP007Input2559]
  have hs : compactExp2547 batchN05120PlusP007Input2559 5 =
      (batchN05120PlusP007Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP007Input2559 5).2 : ℝ) = batchN05120PlusP007Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP007Error2559]
  have h := compactExp_error2547 batchN05120PlusP007Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP007Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP007Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP007DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP007Factor2559 * embedPair2542 batchN05120PlusP007Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP007Factor2559 : ℝ) * batchN05120PlusP007Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP007Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP007Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP007BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP007Factor2559)

def batchN05120PlusP008Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP008Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP008Factor2559 : RatPair2542 := ((((-((120768628256164 * 10^40
        + 1620657511355483974805983392944297400878) * 10^40
        + 7405780327983057829714185355851869951603)) : ℚ) /
        ((390912327411 * 10^40
        + 4757616178921655044855870795510241976276) * 10^40
        + 394201525792727247164931419242540040192)),
    ((((169369172235849810335472735041 * 10^40
        + 7483669051169788316197189357896002734507) * 10^40
        + 7363316896033192350746386100547556527329) : ℚ) /
        ((55016019127026736537453818 * 10^40
        + 6521439416421591219992040308643527463118) * 10^40
        + 6481192025756917090699332654385097342976)))

noncomputable def batchN05120PlusP008Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP008BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP008Center2559‖ ≤ batchN05120PlusP008Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP008Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP008Input2559]
  have hs : compactExp2547 batchN05120PlusP008Input2559 5 =
      (batchN05120PlusP008Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP008Input2559 5).2 : ℝ) = batchN05120PlusP008Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP008Error2559]
  have h := compactExp_error2547 batchN05120PlusP008Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP008Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP008Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP008DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP008Factor2559 * embedPair2542 batchN05120PlusP008Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP008Factor2559 : ℝ) * batchN05120PlusP008Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP008Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP008Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP008BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP008Factor2559)

def batchN05120PlusP009Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP009Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP009Factor2559 : RatPair2542 := ((((-((262749370813838 * 10^40
        + 9730117312011247204182935065414499060706) * 10^40
        + 8476837332784946285280183771460201525299)) : ℚ) /
        ((390912327411 * 10^40
        + 4757616178921655044855870795510241976276) * 10^40
        + 394201525792727247164931419242540040192)),
    ((((531938115497788967697736952089 * 10^40
        + 3514461619645319019471330446803889948539) * 10^40
        + 1833429195671730664102663831862836527679) : ℚ) /
        ((55016019127026736537453818 * 10^40
        + 6521439416421591219992040308643527463118) * 10^40
        + 6481192025756917090699332654385097342976)))

noncomputable def batchN05120PlusP009Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP009BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP009Center2559‖ ≤ batchN05120PlusP009Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP009Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP009Input2559]
  have hs : compactExp2547 batchN05120PlusP009Input2559 5 =
      (batchN05120PlusP009Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP009Input2559 5).2 : ℝ) = batchN05120PlusP009Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP009Error2559]
  have h := compactExp_error2547 batchN05120PlusP009Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP009Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP009Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP009DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP009Factor2559 * embedPair2542 batchN05120PlusP009Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP009Factor2559 : ℝ) * batchN05120PlusP009Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP009Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP009Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP009BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP009Factor2559)

def batchN05120PlusP010Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP010Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP010Factor2559 : RatPair2542 := ((((-((92604125983586 * 10^40
        + 1052196969543503813860186806488855923032) * 10^40
        + 9534553764761366603226305014703922461667)) : ℚ) /
        ((97728081852 * 10^40
        + 8689404044730413761213967698877560494069) * 10^40
        + 98550381448181811791232854810635010048)),
    ((((110690858290140475962849454461 * 10^40
        + 2091670696514104547604044608112247904097) * 10^40
        + 4420964239660685464918514708520213710713) : ℚ) /
        ((6877002390878342067181727 * 10^40
        + 3315179927052698902499005038580440932889) * 10^40
        + 8310149003219614636337416581798137167872)))

noncomputable def batchN05120PlusP010Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP010BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP010Center2559‖ ≤ batchN05120PlusP010Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP010Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP010Input2559]
  have hs : compactExp2547 batchN05120PlusP010Input2559 5 =
      (batchN05120PlusP010Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP010Input2559 5).2 : ℝ) = batchN05120PlusP010Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP010Error2559]
  have h := compactExp_error2547 batchN05120PlusP010Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP010Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP010Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP010DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP010Factor2559 * embedPair2542 batchN05120PlusP010Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP010Factor2559 : ℝ) * batchN05120PlusP010Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP010Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP010Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP010BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP010Factor2559)

def batchN05120PlusP011Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP011Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP011Factor2559 : RatPair2542 := ((((-((113142227536922 * 10^40
        + 5247087955259975989041531443228998183354) * 10^40
        + 485519881950504222829637599924690842947)) : ℚ) /
        ((97728081852 * 10^40
        + 8689404044730413761213967698877560494069) * 10^40
        + 98550381448181811791232854810635010048)),
    ((((149121060541673824054281976386 * 10^40
        + 3113860903473375057612251665571716005147) * 10^40
        + 2547393241224179829995428711838575222313) : ℚ) /
        ((6877002390878342067181727 * 10^40
        + 3315179927052698902499005038580440932889) * 10^40
        + 8310149003219614636337416581798137167872)))

noncomputable def batchN05120PlusP011Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP011BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP011Center2559‖ ≤ batchN05120PlusP011Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP011Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP011Input2559]
  have hs : compactExp2547 batchN05120PlusP011Input2559 5 =
      (batchN05120PlusP011Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP011Input2559 5).2 : ℝ) = batchN05120PlusP011Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP011Error2559]
  have h := compactExp_error2547 batchN05120PlusP011Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP011Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP011Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP011DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP011Factor2559 * embedPair2542 batchN05120PlusP011Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP011Factor2559 : ℝ) * batchN05120PlusP011Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP011Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP011Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP011BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP011Factor2559)

def batchN05120PlusP012Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP012Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP012Factor2559 : RatPair2542 := ((((-((34150208260567 * 10^40
        + 6833405880399330099629602608709842191893) * 10^40
        + 7211586432385149273276857624959518453291)) : ℚ) /
        ((24432020463 * 10^40
        + 2172351011182603440303491924719390123517) * 10^40
        + 2524637595362045452947808213702658752512)),
    ((((24681068650718329193455865750 * 10^40
        + 832021864929282480772879244672913495231) * 10^40
        + 857501935675662443407532270663283467925) : ℚ) /
        ((859625298859792758397715 * 10^40
        + 9164397490881587362812375629822555116611) * 10^40
        + 2288768625402451829542177072724767145984)))

noncomputable def batchN05120PlusP012Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP012BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP012Center2559‖ ≤ batchN05120PlusP012Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP012Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP012Input2559]
  have hs : compactExp2547 batchN05120PlusP012Input2559 5 =
      (batchN05120PlusP012Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP012Input2559 5).2 : ℝ) = batchN05120PlusP012Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP012Error2559]
  have h := compactExp_error2547 batchN05120PlusP012Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP012Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP012Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP012DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP012Factor2559 * embedPair2542 batchN05120PlusP012Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP012Factor2559 : ℝ) * batchN05120PlusP012Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP012Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP012Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP012BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP012Factor2559)

def batchN05120PlusP013Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP013Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP013Factor2559 : RatPair2542 := ((((-((159915605723965 * 10^40
        + 8900097830395917154078017231113873535930) * 10^40
        + 1533688913340305766239812730215283028739)) : ℚ) /
        ((97728081852 * 10^40
        + 8689404044730413761213967698877560494069) * 10^40
        + 98550381448181811791232854810635010048)),
    ((((249761780200912406906167895154 * 10^40
        + 32877492458203755971463052259600483616) * 10^40
        + 7722149640314557282715237074149337772535) : ℚ) /
        ((6877002390878342067181727 * 10^40
        + 3315179927052698902499005038580440932889) * 10^40
        + 8310149003219614636337416581798137167872)))

noncomputable def batchN05120PlusP013Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP013BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP013Center2559‖ ≤ batchN05120PlusP013Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP013Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP013Input2559]
  have hs : compactExp2547 batchN05120PlusP013Input2559 5 =
      (batchN05120PlusP013Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP013Input2559 5).2 : ℝ) = batchN05120PlusP013Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP013Error2559]
  have h := compactExp_error2547 batchN05120PlusP013Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP013Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP013Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP013DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP013Factor2559 * embedPair2542 batchN05120PlusP013Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP013Factor2559 : ℝ) * batchN05120PlusP013Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP013Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP013Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP013BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP013Factor2559)

def batchN05120PlusP014Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP014Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP014Factor2559 : RatPair2542 := ((((-((207998189472536 * 10^40
        + 3539667049628394699579678195178314687564) * 10^40
        + 8900296663092708337412534677562880316107)) : ℚ) /
        ((97728081852 * 10^40
        + 8689404044730413761213967698877560494069) * 10^40
        + 98550381448181811791232854810635010048)),
    ((((369815510585701894285690720256 * 10^40
        + 9440006509907226775770339457461531899692) * 10^40
        + 8787763542394657113414379279215428639963) : ℚ) /
        ((6877002390878342067181727 * 10^40
        + 3315179927052698902499005038580440932889) * 10^40
        + 8310149003219614636337416581798137167872)))

noncomputable def batchN05120PlusP014Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP014BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP014Center2559‖ ≤ batchN05120PlusP014Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP014Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP014Input2559]
  have hs : compactExp2547 batchN05120PlusP014Input2559 5 =
      (batchN05120PlusP014Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP014Input2559 5).2 : ℝ) = batchN05120PlusP014Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP014Error2559]
  have h := compactExp_error2547 batchN05120PlusP014Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP014Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP014Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP014DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP014Factor2559 * embedPair2542 batchN05120PlusP014Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP014Factor2559 : ℝ) * batchN05120PlusP014Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP014Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP014Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP014BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP014Factor2559)

def batchN05120PlusP015Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP015Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP015Factor2559 : RatPair2542 := ((((-((246349734537324 * 10^40
        + 1409038746020086141276892786531420772128) * 10^40
        + 6628679628029677360631685408678617608611)) : ℚ) /
        ((97728081852 * 10^40
        + 8689404044730413761213967698877560494069) * 10^40
        + 98550381448181811791232854810635010048)),
    ((((476224429575398316801074005035 * 10^40
        + 9187045055985911462973619649312831582705) * 10^40
        + 4990782440562676102247937574050887764647) : ℚ) /
        ((6877002390878342067181727 * 10^40
        + 3315179927052698902499005038580440932889) * 10^40
        + 8310149003219614636337416581798137167872)))

noncomputable def batchN05120PlusP015Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP015BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP015Center2559‖ ≤ batchN05120PlusP015Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP015Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP015Input2559]
  have hs : compactExp2547 batchN05120PlusP015Input2559 5 =
      (batchN05120PlusP015Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP015Input2559 5).2 : ℝ) = batchN05120PlusP015Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP015Error2559]
  have h := compactExp_error2547 batchN05120PlusP015Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP015Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP015Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP015DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP015Factor2559 * embedPair2542 batchN05120PlusP015Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP015Factor2559 : ℝ) * batchN05120PlusP015Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP015Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP015Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP015BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP015Factor2559)

def batchN05120PlusP016Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP016Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP016Factor2559 : RatPair2542 := ((((-((69023088674271 * 10^40
        + 9121555257564512272441665184177460760133) * 10^40
        + 8806963709893583280615409347698211643939)) : ℚ) /
        ((24432020463 * 10^40
        + 2172351011182603440303491924719390123517) * 10^40
        + 2524637595362045452947808213702658752512)),
    ((((70588484296328475587766535554 * 10^40
        + 2754429791201988115423398033862359130936) * 10^40
        + 3684561823066605091113032611327730033561) : ℚ) /
        ((859625298859792758397715 * 10^40
        + 9164397490881587362812375629822555116611) * 10^40
        + 2288768625402451829542177072724767145984)))

noncomputable def batchN05120PlusP016Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP016BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP016Center2559‖ ≤ batchN05120PlusP016Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP016Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP016Input2559]
  have hs : compactExp2547 batchN05120PlusP016Input2559 5 =
      (batchN05120PlusP016Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP016Input2559 5).2 : ℝ) = batchN05120PlusP016Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP016Error2559]
  have h := compactExp_error2547 batchN05120PlusP016Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP016Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP016Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP016DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP016Factor2559 * embedPair2542 batchN05120PlusP016Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP016Factor2559 : ℝ) * batchN05120PlusP016Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP016Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP016Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP016BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP016Factor2559)

def batchN05120PlusP017Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP017Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP017Factor2559 : RatPair2542 := ((((-((338725192497984 * 10^40
        + 261667391148827285932248876494777938209) * 10^40
        + 7439254991265509308956150601778445467771)) : ℚ) /
        ((97728081852 * 10^40
        + 8689404044730413761213967698877560494069) * 10^40
        + 98550381448181811791232854810635010048)),
    ((((766731827972529680782771480867 * 10^40
        + 249518546482908257864462590862212010607) * 10^40
        + 6693445749538066041481625170923198808067) : ℚ) /
        ((6877002390878342067181727 * 10^40
        + 3315179927052698902499005038580440932889) * 10^40
        + 8310149003219614636337416581798137167872)))

noncomputable def batchN05120PlusP017Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP017BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP017Center2559‖ ≤ batchN05120PlusP017Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP017Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP017Input2559]
  have hs : compactExp2547 batchN05120PlusP017Input2559 5 =
      (batchN05120PlusP017Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP017Input2559 5).2 : ℝ) = batchN05120PlusP017Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP017Error2559]
  have h := compactExp_error2547 batchN05120PlusP017Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP017Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP017Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP017DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP017Factor2559 * embedPair2542 batchN05120PlusP017Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP017Factor2559 : ℝ) * batchN05120PlusP017Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP017Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP017Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP017BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP017Factor2559)

def batchN05120PlusP018Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP018Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP018Factor2559 : RatPair2542 := ((((-((22754801115659 * 10^40
        + 2610858486468067063977853789166514513898) * 10^40
        + 612791663025077185194453892757457155531)) : ℚ) /
        ((6108005115 * 10^40
        + 8043087752795650860075872981179847530879) * 10^40
        + 3131159398840511363236952053425664688128)),
    ((((13346521742767281119796296747 * 10^40
        + 1926118657994423843347769481174910853741) * 10^40
        + 4015395464458204458399081398963156326053) : ℚ) /
        ((107453162357474094799714 * 10^40
        + 4895549686360198420351546953727819389576) * 10^40
        + 4036096078175306478692772134090595893248)))

noncomputable def batchN05120PlusP018Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP018BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP018Center2559‖ ≤ batchN05120PlusP018Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP018Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP018Input2559]
  have hs : compactExp2547 batchN05120PlusP018Input2559 5 =
      (batchN05120PlusP018Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP018Input2559 5).2 : ℝ) = batchN05120PlusP018Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP018Error2559]
  have h := compactExp_error2547 batchN05120PlusP018Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP018Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP018Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP018DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP018Factor2559 * embedPair2542 batchN05120PlusP018Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP018Factor2559 : ℝ) * batchN05120PlusP018Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP018Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP018Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP018BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP018Factor2559)

def batchN05120PlusP019Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP019Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP019Factor2559 : RatPair2542 := ((((-((25763792787681 * 10^40
        + 3092317963817578828600513284100549780024) * 10^40
        + 742893916244652982565050608723501257179)) : ℚ) /
        ((6108005115 * 10^40
        + 8043087752795650860075872981179847530879) * 10^40
        + 3131159398840511363236952053425664688128)),
    ((((16072952492555897294885271951 * 10^40
        + 1842292664494128886697274278975053814569) * 10^40
        + 9589672087346828595655032676169820399635) : ℚ) /
        ((107453162357474094799714 * 10^40
        + 4895549686360198420351546953727819389576) * 10^40
        + 4036096078175306478692772134090595893248)))

noncomputable def batchN05120PlusP019Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP019BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP019Center2559‖ ≤ batchN05120PlusP019Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP019Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP019Input2559]
  have hs : compactExp2547 batchN05120PlusP019Input2559 5 =
      (batchN05120PlusP019Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP019Input2559 5).2 : ℝ) = batchN05120PlusP019Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP019Error2559]
  have h := compactExp_error2547 batchN05120PlusP019Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP019Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP019Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP019DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP019Factor2559 * embedPair2542 batchN05120PlusP019Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP019Factor2559 : ℝ) * batchN05120PlusP019Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP019Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP019Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP019BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP019Factor2559)

def batchN05120PlusP020Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP020Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP020Factor2559 : RatPair2542 := ((((-((467973175617778 * 10^40
        + 7371635715753198435323339987553531585106) * 10^40
        + 1034554708789408408052297170793302017627)) : ℚ) /
        ((97728081852 * 10^40
        + 8689404044730413761213967698877560494069) * 10^40
        + 98550381448181811791232854810635010048)),
    ((((1243804995917849197590785664526 * 10^40
        + 4409289538197749036903180990719746188994) * 10^40
        + 7422400962955196869186964300370188799187) : ℚ) /
        ((6877002390878342067181727 * 10^40
        + 3315179927052698902499005038580440932889) * 10^40
        + 8310149003219614636337416581798137167872)))

noncomputable def batchN05120PlusP020Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP020BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP020Center2559‖ ≤ batchN05120PlusP020Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP020Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP020Input2559]
  have hs : compactExp2547 batchN05120PlusP020Input2559 5 =
      (batchN05120PlusP020Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP020Input2559 5).2 : ℝ) = batchN05120PlusP020Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP020Error2559]
  have h := compactExp_error2547 batchN05120PlusP020Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP020Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP020Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP020DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP020Factor2559 * embedPair2542 batchN05120PlusP020Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP020Factor2559 : ℝ) * batchN05120PlusP020Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP020Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP020Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP020BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP020Factor2559)

def batchN05120PlusP021Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP021Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP021Factor2559 : RatPair2542 := ((((-((517212407272309 * 10^40
        + 4463283416531860538428093295664265660307) * 10^40
        + 9562698765608301153058172137729710424091)) : ℚ) /
        ((97728081852 * 10^40
        + 8689404044730413761213967698877560494069) * 10^40
        + 98550381448181811791232854810635010048)),
    ((((1444812485238800097950309150505 * 10^40
        + 8675350417621519269568689235401561244522) * 10^40
        + 8732601942805713036946734478411830625907) : ℚ) /
        ((6877002390878342067181727 * 10^40
        + 3315179927052698902499005038580440932889) * 10^40
        + 8310149003219614636337416581798137167872)))

noncomputable def batchN05120PlusP021Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP021BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP021Center2559‖ ≤ batchN05120PlusP021Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP021Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP021Input2559]
  have hs : compactExp2547 batchN05120PlusP021Input2559 5 =
      (batchN05120PlusP021Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP021Input2559 5).2 : ℝ) = batchN05120PlusP021Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP021Error2559]
  have h := compactExp_error2547 batchN05120PlusP021Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP021Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP021Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP021DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP021Factor2559 * embedPair2542 batchN05120PlusP021Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP021Factor2559 : ℝ) * batchN05120PlusP021Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP021Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP021Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP021BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP021Factor2559)

def batchN05120PlusP022Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP022Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP022Factor2559 : RatPair2542 := ((((-((543369374305640 * 10^40
        + 65184680257140623005366044322176599193) * 10^40
        + 7775111851158987530117042800955175195339)) : ℚ) /
        ((97728081852 * 10^40
        + 8689404044730413761213967698877560494069) * 10^40
        + 98550381448181811791232854810635010048)),
    ((((1555604547629649648111407169782 * 10^40
        + 2995943739619347963257418425803365582598) * 10^40
        + 249000314442198889589824825261779559205) : ℚ) /
        ((6877002390878342067181727 * 10^40
        + 3315179927052698902499005038580440932889) * 10^40
        + 8310149003219614636337416581798137167872)))

noncomputable def batchN05120PlusP022Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP022BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP022Center2559‖ ≤ batchN05120PlusP022Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP022Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP022Input2559]
  have hs : compactExp2547 batchN05120PlusP022Input2559 5 =
      (batchN05120PlusP022Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP022Input2559 5).2 : ℝ) = batchN05120PlusP022Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP022Error2559]
  have h := compactExp_error2547 batchN05120PlusP022Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP022Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP022Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP022DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP022Factor2559 * embedPair2542 batchN05120PlusP022Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP022Factor2559 : ℝ) * batchN05120PlusP022Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP022Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP022Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP022BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP022Factor2559)

def batchN05120PlusP023Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP023Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP023Factor2559 : RatPair2542 := ((((-((155600693725060 * 10^40
        + 4056371413723861597708960336543385859627) * 10^40
        + 2868967617302485156093109359407289865803)) : ℚ) /
        ((24432020463 * 10^40
        + 2172351011182603440303491924719390123517) * 10^40
        + 2524637595362045452947808213702658752512)),
    ((((238311010151598580324111573499 * 10^40
        + 9428319954158177110412522706475250918291) * 10^40
        + 7521312485123187842483872360243747813861) : ℚ) /
        ((859625298859792758397715 * 10^40
        + 9164397490881587362812375629822555116611) * 10^40
        + 2288768625402451829542177072724767145984)))

noncomputable def batchN05120PlusP023Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP023BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP023Center2559‖ ≤ batchN05120PlusP023Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP023Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP023Input2559]
  have hs : compactExp2547 batchN05120PlusP023Input2559 5 =
      (batchN05120PlusP023Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP023Input2559 5).2 : ℝ) = batchN05120PlusP023Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP023Error2559]
  have h := compactExp_error2547 batchN05120PlusP023Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP023Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP023Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP023DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP023Factor2559 * embedPair2542 batchN05120PlusP023Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP023Factor2559 : ℝ) * batchN05120PlusP023Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP023Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP023Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP023BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP023Factor2559)

def batchN05120PlusP024Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP024Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP024Factor2559 : RatPair2542 := ((((-((165131292202015 * 10^40
        + 8348159281957861185861885020196528171159) * 10^40
        + 5493649873734713141928370877860107047563)) : ℚ) /
        ((24432020463 * 10^40
        + 2172351011182603440303491924719390123517) * 10^40
        + 2524637595362045452947808213702658752512)),
    ((((260507009555349783590172069218 * 10^40
        + 3457438586601656964061337030967839570710) * 10^40
        + 53595966167261996434955089018958396539) : ℚ) /
        ((859625298859792758397715 * 10^40
        + 9164397490881587362812375629822555116611) * 10^40
        + 2288768625402451829542177072724767145984)))

noncomputable def batchN05120PlusP024Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP024BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP024Center2559‖ ≤ batchN05120PlusP024Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP024Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP024Input2559]
  have hs : compactExp2547 batchN05120PlusP024Input2559 5 =
      (batchN05120PlusP024Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP024Input2559 5).2 : ℝ) = batchN05120PlusP024Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP024Error2559]
  have h := compactExp_error2547 batchN05120PlusP024Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP024Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP024Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP024DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP024Factor2559 * embedPair2542 batchN05120PlusP024Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP024Factor2559 : ℝ) * batchN05120PlusP024Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP024Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP024Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP024BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP024Factor2559)

def batchN05120PlusP025Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP025Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP025Factor2559 : RatPair2542 := ((((-((173321987862 * 10^40
        + 9358429972209552793389131361369408690350) * 10^40
        + 343289764251142153441218088028402843571)) : ℚ) /
        ((23859394 * 10^40
        + 9836105811534358011172171378832733779417) * 10^40
        + 4973168591401720747512644343958694002688)),
    ((((8857218242242067137389217 * 10^40
        + 9300406635718329985799467402001564252911) * 10^40
        + 6432729581501141608667953485583365869953) : ℚ) /
        ((26233682216180198925 * 10^40
        + 7115453015060146532817468639392999955905) * 10^40
        + 6583016625019085768183274602571799461888)))

noncomputable def batchN05120PlusP025Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP025BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP025Center2559‖ ≤ batchN05120PlusP025Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP025Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP025Input2559]
  have hs : compactExp2547 batchN05120PlusP025Input2559 5 =
      (batchN05120PlusP025Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP025Input2559 5).2 : ℝ) = batchN05120PlusP025Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP025Error2559]
  have h := compactExp_error2547 batchN05120PlusP025Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP025Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP025Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP025DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP025Factor2559 * embedPair2542 batchN05120PlusP025Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP025Factor2559 : ℝ) * batchN05120PlusP025Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP025Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP025Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP025BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP025Factor2559)

def batchN05120PlusP026Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP026Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP026Factor2559 : RatPair2542 := ((((-((744390942395 * 10^40
        + 5759859734710972139032667518761994028783) * 10^40
        + 9703828873598311159769920281264510378763)) : ℚ) /
        ((95437579 * 10^40
        + 9344423246137432044688685515330935117669) * 10^40
        + 9892674365606882990050577375834776010752)),
    ((((78825143700386822972068628 * 10^40
        + 2458791651468112754477540039667123424188) * 10^40
        + 9613644918475151947556049239528974771909) : ℚ) /
        ((209869457729441591405 * 10^40
        + 6923624120481172262539749115143999647245) * 10^40
        + 2664133000152686145466196820574395695104)))

noncomputable def batchN05120PlusP026Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP026BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP026Center2559‖ ≤ batchN05120PlusP026Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP026Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP026Input2559]
  have hs : compactExp2547 batchN05120PlusP026Input2559 5 =
      (batchN05120PlusP026Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP026Input2559 5).2 : ℝ) = batchN05120PlusP026Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP026Error2559]
  have h := compactExp_error2547 batchN05120PlusP026Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP026Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP026Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP026DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP026Factor2559 * embedPair2542 batchN05120PlusP026Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP026Factor2559 : ℝ) * batchN05120PlusP026Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP026Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP026Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP026BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP026Factor2559)

def batchN05120PlusP027Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP027Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP027Factor2559 : RatPair2542 := ((((-((3285364268233 * 10^40
        + 8313797629581981345977454858069502777739) * 10^40
        + 1744004875182945721197979481108258790251)) : ℚ) /
        ((381750319 * 10^40
        + 7377692984549728178754742061323740470679) * 10^40
        + 9570697462427531960202309503339104043008)),
    ((((730752261127031722744581748 * 10^40
        + 9857129809094806008406077447310983968161) * 10^40
        + 8274725400819728831784421084569504073547) : ℚ) /
        ((1678955661835532731245 * 10^40
        + 5388992963849378100317992921151997177962) * 10^40
        + 1313064001221489163729574564595165560832)))

noncomputable def batchN05120PlusP027Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP027BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP027Center2559‖ ≤ batchN05120PlusP027Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP027Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP027Input2559]
  have hs : compactExp2547 batchN05120PlusP027Input2559 5 =
      (batchN05120PlusP027Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP027Input2559 5).2 : ℝ) = batchN05120PlusP027Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP027Error2559]
  have h := compactExp_error2547 batchN05120PlusP027Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP027Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP027Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP027DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP027Factor2559 * embedPair2542 batchN05120PlusP027Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP027Factor2559 : ℝ) * batchN05120PlusP027Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP027Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP027Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP027BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP027Factor2559)

def batchN05120PlusP028Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP028Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP028Factor2559 : RatPair2542 := ((((-((54582625816775 * 10^40
        + 7074135089481486644966148092170334791651) * 10^40
        + 1720791653496674435405171466626560932611)) : ℚ) /
        ((6108005115 * 10^40
        + 8043087752795650860075872981179847530879) * 10^40
        + 3131159398840511363236952053425664688128)),
    ((((49482553195820388965152188096 * 10^40
        + 1841079229203388570071602507638164951718) * 10^40
        + 2083000853550215929708130624128531017207) : ℚ) /
        ((107453162357474094799714 * 10^40
        + 4895549686360198420351546953727819389576) * 10^40
        + 4036096078175306478692772134090595893248)))

noncomputable def batchN05120PlusP028Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP028BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP028Center2559‖ ≤ batchN05120PlusP028Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP028Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP028Input2559]
  have hs : compactExp2547 batchN05120PlusP028Input2559 5 =
      (batchN05120PlusP028Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP028Input2559 5).2 : ℝ) = batchN05120PlusP028Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP028Error2559]
  have h := compactExp_error2547 batchN05120PlusP028Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP028Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP028Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP028DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP028Factor2559 * embedPair2542 batchN05120PlusP028Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP028Factor2559 : ℝ) * batchN05120PlusP028Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP028Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP028Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP028BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP028Factor2559)

def batchN05120PlusP029Input2559 : RatPair2542 := ((((-15) : ℚ) /
        16),
    ((0 : ℚ) /
        1))

def batchN05120PlusP029Center2559 : RatPair2542 := (((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05120PlusP029Factor2559 : RatPair2542 := ((((-((57726044003819 * 10^40
        + 2637691385421174757949550258297989421091) * 10^40
        + 4355837550188510335917227144324168256827)) : ℚ) /
        ((6108005115 * 10^40
        + 8043087752795650860075872981179847530879) * 10^40
        + 3131159398840511363236952053425664688128)),
    ((((53813781044893508320063458771 * 10^40
        + 679272573137265958593699400609975072256) * 10^40
        + 8304873829728929247503066314395796959267) : ℚ) /
        ((107453162357474094799714 * 10^40
        + 4895549686360198420351546953727819389576) * 10^40
        + 4036096078175306478692772134090595893248)))

noncomputable def batchN05120PlusP029Error2559 : ℝ := ((12287562243733755928524809515635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05120PlusP029BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP029Center2559‖ ≤ batchN05120PlusP029Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05120PlusP029Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05120PlusP029Input2559]
  have hs : compactExp2547 batchN05120PlusP029Input2559 5 =
      (batchN05120PlusP029Center2559, ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05120PlusP029Input2559 5).2 : ℝ) = batchN05120PlusP029Error2559
      := by
    rw [hs]
    norm_num [batchN05120PlusP029Error2559]
  have h := compactExp_error2547 batchN05120PlusP029Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      batchN05120PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05120PlusP029Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05120PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05120PlusP029Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05120PlusP029DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05120PlusPosition2559 -
      embedPair2542 batchN05120PlusP029Factor2559 * embedPair2542 batchN05120PlusP029Center2559‖ ≤
        (pairMagnitude2542 batchN05120PlusP029Factor2559 : ℝ) * batchN05120PlusP029Error2559 := by
  have hx : |batchN05120PlusPosition2559| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchN05120PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchN05120PlusPosition2559 = embedPair2542
          batchN05120PlusP029Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05120PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05120PlusP029Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05120PlusP029BaseError2559
    (embedPair_magnitude2542 batchN05120PlusP029Factor2559)

theorem batchN05120PlusGrid2559 :
    -stripRadius2303 + (5120 : ℝ) * (2 * stripRadius2303 / 10240) =
      batchN05120PlusPosition2559 := by
  norm_num [stripRadius2303, batchN05120PlusPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchN05120PlusP000DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP001DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP002DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP003DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP004DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP005DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP006DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP007DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP008DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP009DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP010DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP011DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP012DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP013DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP014DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP015DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP016DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP017DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP018DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP019DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP020DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP021DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP022DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP023DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP024DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP025DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP026DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP027DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP028DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusP029DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05120PlusGrid2559
