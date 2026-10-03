import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def pairedN10239MinusPosition2553 : ℝ := ((335478789119 : ℝ) /
        51200000000)

theorem pairedN10239MinusZero2553 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def pairedN10239MinusP000Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP000Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP000Error2553 : ℝ := 0

theorem pairedN10239MinusP000Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem pairedN10239MinusP000BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP000Center2553‖ ≤ pairedN10239MinusP000Error2553 := by
  rw [pairedN10239MinusP000Exterior2553]
  norm_num [pairedN10239MinusP000Center2553, pairedN10239MinusP000Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP000DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP000Factor2553 * embedPair2542
          pairedN10239MinusP000Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP000Factor2553 : ℝ) * pairedN10239MinusP000Error2553
            := by
  rw [pairedN10239MinusP000Exterior2553]
  norm_num [pairedN10239MinusP000Factor2553, pairedN10239MinusP000Center2553,
      pairedN10239MinusP000Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP001Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP001Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP001Error2553 : ℝ := 0

theorem pairedN10239MinusP001Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨1, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨1, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
    (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx

theorem pairedN10239MinusP001BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP001Center2553‖ ≤ pairedN10239MinusP001Error2553 := by
  rw [pairedN10239MinusP001Exterior2553]
  norm_num [pairedN10239MinusP001Center2553, pairedN10239MinusP001Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP001DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP001Factor2553 * embedPair2542
          pairedN10239MinusP001Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP001Factor2553 : ℝ) * pairedN10239MinusP001Error2553
            := by
  rw [pairedN10239MinusP001Exterior2553]
  norm_num [pairedN10239MinusP001Factor2553, pairedN10239MinusP001Center2553,
      pairedN10239MinusP001Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP002Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP002Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP002Error2553 : ℝ := 0

theorem pairedN10239MinusP002Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨2, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨2, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
    (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx

theorem pairedN10239MinusP002BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP002Center2553‖ ≤ pairedN10239MinusP002Error2553 := by
  rw [pairedN10239MinusP002Exterior2553]
  norm_num [pairedN10239MinusP002Center2553, pairedN10239MinusP002Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP002DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP002Factor2553 * embedPair2542
          pairedN10239MinusP002Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP002Factor2553 : ℝ) * pairedN10239MinusP002Error2553
            := by
  rw [pairedN10239MinusP002Exterior2553]
  norm_num [pairedN10239MinusP002Factor2553, pairedN10239MinusP002Center2553,
      pairedN10239MinusP002Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP003Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP003Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP003Error2553 : ℝ := 0

theorem pairedN10239MinusP003Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨3, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨3, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
    (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx

theorem pairedN10239MinusP003BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP003Center2553‖ ≤ pairedN10239MinusP003Error2553 := by
  rw [pairedN10239MinusP003Exterior2553]
  norm_num [pairedN10239MinusP003Center2553, pairedN10239MinusP003Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP003DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP003Factor2553 * embedPair2542
          pairedN10239MinusP003Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP003Factor2553 : ℝ) * pairedN10239MinusP003Error2553
            := by
  rw [pairedN10239MinusP003Exterior2553]
  norm_num [pairedN10239MinusP003Factor2553, pairedN10239MinusP003Center2553,
      pairedN10239MinusP003Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP004Input2553 : RatPair2542 := ((((-((20220 * 10^40
        + 8223985760775046352662199539254491013811) * 10^40
        + 5561935562252393339501278847130390888639)) : ℚ) /
        ((34502 * 10^40
        + 6667990208777211291311779003017294650045) * 10^40
        + 2705343650009835671246640827596800000000)),
    (((-1853282464048842856447326451) : ℚ) /
        944473296573929042739200000000))

def pairedN10239MinusP004Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN10239MinusP004Factor2553 : RatPair2542 := ((((-(((((((((((24701859142610917329898 *
    10^40
        + 8113153862163605420322101366561276097687) * 10^40
        + 5041621772943458667926632824860582084589) * 10^40
        + 9562397648906585625835362607592444003349) * 10^40
        + 1364816794420600566562765046312371597991) * 10^40
        + 5698205966386754623879186109448432974089) * 10^40
        + 4921216440365569057408840399355766721213) * 10^40
        + 8161131707210761680168482811790669235726) * 10^40
        + 1495354881319691575256402761636107431726) * 10^40
        + 7234805620158104904554549345912735865625) * 10^40
        + 4169128456592876195633789957530963043296) * 10^40
        + 3068154326289732952598317167088122369413)) : ℚ) /
        ((((((((((1143158039863674476126421177796511280715 * 10^40
        + 2518245648065294406590519722165000561983) * 10^40
        + 2729366868835894476452854088286893794542) * 10^40
        + 6933043838265201340888224941243372737548) * 10^40
        + 6968487974526081506018856782207159858168) * 10^40
        + 9585019889148560268581955774679170490761) * 10^40
        + 5043527813363289336229219265843214949890) * 10^40
        + 5781292754243583729787890738031881263319) * 10^40
        + 6970802176002876745437976340378707848292) * 10^40
        + 1391127677730106215824621039132229349579) * 10^40
        + 4851222834670817162945674109297841143808)),
    (((-((((((((51619691886934 * 10^40
        + 8136397308094832091978209979481014120670) * 10^40
        + 5459902283201349443236840729477603167260) * 10^40
        + 7632227827958639690713014329935772457973) * 10^40
        + 4665423273911243115447520566554186107003) * 10^40
        + 400104537125744953818814200560574039821) * 10^40
        + 2825721238577931963822121239060925089421) * 10^40
        + 7785114693167693313314686505210204821080) * 10^40
        + 7628076101793482899165242897293411138923)) : ℚ) /
        (((((((1217308104115513119604376131045405684 * 10^40
        + 7414425181400613386230271978902089736372) * 10^40
        + 4607535991806235193780522107116660793201) * 10^40
        + 4718238591207537483169899846049339239955) * 10^40
        + 3968345537406587287975742847290213879555) * 10^40
        + 2066285933213707091867349581299728465159) * 10^40
        + 4137474666863446899770604309607374511162) * 10^40
        + 6083070446892797437003240783227746516992)))

noncomputable def pairedN10239MinusP004Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN10239MinusP004BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP004Center2553‖ ≤ pairedN10239MinusP004Error2553 := by
  have hx : |pairedN10239MinusPosition2553| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [pairedN10239MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN10239MinusP004Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN10239MinusP004Input2553]
  have hs : compactExp2547 pairedN10239MinusP004Input2553 17 =
      (pairedN10239MinusP004Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN10239MinusP004Input2553 17).2 : ℝ) =
      pairedN10239MinusP004Error2553 := by
    rw [hs]
    norm_num [pairedN10239MinusP004Error2553]
  have h := compactExp_error2547 pairedN10239MinusP004Input2553 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      pairedN10239MinusPosition2553 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          pairedN10239MinusP004Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN10239MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN10239MinusP004Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN10239MinusP004DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP004Factor2553 * embedPair2542
          pairedN10239MinusP004Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP004Factor2553 : ℝ) * pairedN10239MinusP004Error2553
            := by
  have hx : |pairedN10239MinusPosition2553| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [pairedN10239MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) pairedN10239MinusPosition2553 = embedPair2542
          pairedN10239MinusP004Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN10239MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN10239MinusP004Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN10239MinusP004BaseError2553
    (embedPair_magnitude2542 pairedN10239MinusP004Factor2553)

def pairedN10239MinusP005Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP005Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP005Error2553 : ℝ := 0

theorem pairedN10239MinusP005Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem pairedN10239MinusP005BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP005Center2553‖ ≤ pairedN10239MinusP005Error2553 := by
  rw [pairedN10239MinusP005Exterior2553]
  norm_num [pairedN10239MinusP005Center2553, pairedN10239MinusP005Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP005DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP005Factor2553 * embedPair2542
          pairedN10239MinusP005Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP005Factor2553 : ℝ) * pairedN10239MinusP005Error2553
            := by
  rw [pairedN10239MinusP005Exterior2553]
  norm_num [pairedN10239MinusP005Factor2553, pairedN10239MinusP005Center2553,
      pairedN10239MinusP005Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP006Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP006Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP006Error2553 : ℝ := 0

theorem pairedN10239MinusP006Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨6, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨6, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx

theorem pairedN10239MinusP006BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP006Center2553‖ ≤ pairedN10239MinusP006Error2553 := by
  rw [pairedN10239MinusP006Exterior2553]
  norm_num [pairedN10239MinusP006Center2553, pairedN10239MinusP006Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP006DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP006Factor2553 * embedPair2542
          pairedN10239MinusP006Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP006Factor2553 : ℝ) * pairedN10239MinusP006Error2553
            := by
  rw [pairedN10239MinusP006Exterior2553]
  norm_num [pairedN10239MinusP006Factor2553, pairedN10239MinusP006Center2553,
      pairedN10239MinusP006Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP007Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP007Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP007Error2553 : ℝ := 0

theorem pairedN10239MinusP007Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨7, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨7, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
    (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx

theorem pairedN10239MinusP007BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP007Center2553‖ ≤ pairedN10239MinusP007Error2553 := by
  rw [pairedN10239MinusP007Exterior2553]
  norm_num [pairedN10239MinusP007Center2553, pairedN10239MinusP007Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP007DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP007Factor2553 * embedPair2542
          pairedN10239MinusP007Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP007Factor2553 : ℝ) * pairedN10239MinusP007Error2553
            := by
  rw [pairedN10239MinusP007Exterior2553]
  norm_num [pairedN10239MinusP007Factor2553, pairedN10239MinusP007Center2553,
      pairedN10239MinusP007Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP008Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP008Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP008Error2553 : ℝ := 0

theorem pairedN10239MinusP008Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨8, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
    (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx

theorem pairedN10239MinusP008BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP008Center2553‖ ≤ pairedN10239MinusP008Error2553 := by
  rw [pairedN10239MinusP008Exterior2553]
  norm_num [pairedN10239MinusP008Center2553, pairedN10239MinusP008Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP008DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP008Factor2553 * embedPair2542
          pairedN10239MinusP008Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP008Factor2553 : ℝ) * pairedN10239MinusP008Error2553
            := by
  rw [pairedN10239MinusP008Exterior2553]
  norm_num [pairedN10239MinusP008Factor2553, pairedN10239MinusP008Center2553,
      pairedN10239MinusP008Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP009Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP009Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP009Error2553 : ℝ := 0

theorem pairedN10239MinusP009Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨9, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
    (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx

theorem pairedN10239MinusP009BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP009Center2553‖ ≤ pairedN10239MinusP009Error2553 := by
  rw [pairedN10239MinusP009Exterior2553]
  norm_num [pairedN10239MinusP009Center2553, pairedN10239MinusP009Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP009DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN10239MinusPosition2553 -
      embedPair2542 pairedN10239MinusP009Factor2553 * embedPair2542
          pairedN10239MinusP009Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP009Factor2553 : ℝ) * pairedN10239MinusP009Error2553
            := by
  rw [pairedN10239MinusP009Exterior2553]
  norm_num [pairedN10239MinusP009Factor2553, pairedN10239MinusP009Center2553,
      pairedN10239MinusP009Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP010Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP010Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP010Error2553 : ℝ := 0

theorem pairedN10239MinusP010Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨10, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
    (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx

theorem pairedN10239MinusP010BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP010Center2553‖ ≤ pairedN10239MinusP010Error2553 := by
  rw [pairedN10239MinusP010Exterior2553]
  norm_num [pairedN10239MinusP010Center2553, pairedN10239MinusP010Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP010DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP010Factor2553 * embedPair2542
          pairedN10239MinusP010Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP010Factor2553 : ℝ) * pairedN10239MinusP010Error2553
            := by
  rw [pairedN10239MinusP010Exterior2553]
  norm_num [pairedN10239MinusP010Factor2553, pairedN10239MinusP010Center2553,
      pairedN10239MinusP010Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP011Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP011Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP011Error2553 : ℝ := 0

theorem pairedN10239MinusP011Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨11, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
    (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx

theorem pairedN10239MinusP011BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP011Center2553‖ ≤ pairedN10239MinusP011Error2553 := by
  rw [pairedN10239MinusP011Exterior2553]
  norm_num [pairedN10239MinusP011Center2553, pairedN10239MinusP011Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP011DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP011Factor2553 * embedPair2542
          pairedN10239MinusP011Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP011Factor2553 : ℝ) * pairedN10239MinusP011Error2553
            := by
  rw [pairedN10239MinusP011Exterior2553]
  norm_num [pairedN10239MinusP011Factor2553, pairedN10239MinusP011Center2553,
      pairedN10239MinusP011Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP012Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP012Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP012Error2553 : ℝ := 0

theorem pairedN10239MinusP012Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨12, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
    (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx

theorem pairedN10239MinusP012BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP012Center2553‖ ≤ pairedN10239MinusP012Error2553 := by
  rw [pairedN10239MinusP012Exterior2553]
  norm_num [pairedN10239MinusP012Center2553, pairedN10239MinusP012Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP012DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP012Factor2553 * embedPair2542
          pairedN10239MinusP012Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP012Factor2553 : ℝ) * pairedN10239MinusP012Error2553
            := by
  rw [pairedN10239MinusP012Exterior2553]
  norm_num [pairedN10239MinusP012Factor2553, pairedN10239MinusP012Center2553,
      pairedN10239MinusP012Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP013Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP013Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP013Error2553 : ℝ := 0

theorem pairedN10239MinusP013Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨13, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
    (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx

theorem pairedN10239MinusP013BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP013Center2553‖ ≤ pairedN10239MinusP013Error2553 := by
  rw [pairedN10239MinusP013Exterior2553]
  norm_num [pairedN10239MinusP013Center2553, pairedN10239MinusP013Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP013DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP013Factor2553 * embedPair2542
          pairedN10239MinusP013Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP013Factor2553 : ℝ) * pairedN10239MinusP013Error2553
            := by
  rw [pairedN10239MinusP013Exterior2553]
  norm_num [pairedN10239MinusP013Factor2553, pairedN10239MinusP013Center2553,
      pairedN10239MinusP013Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP014Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP014Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP014Error2553 : ℝ := 0

theorem pairedN10239MinusP014Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨14, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
    (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx

theorem pairedN10239MinusP014BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP014Center2553‖ ≤ pairedN10239MinusP014Error2553 := by
  rw [pairedN10239MinusP014Exterior2553]
  norm_num [pairedN10239MinusP014Center2553, pairedN10239MinusP014Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP014DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP014Factor2553 * embedPair2542
          pairedN10239MinusP014Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP014Factor2553 : ℝ) * pairedN10239MinusP014Error2553
            := by
  rw [pairedN10239MinusP014Exterior2553]
  norm_num [pairedN10239MinusP014Factor2553, pairedN10239MinusP014Center2553,
      pairedN10239MinusP014Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP015Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP015Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP015Error2553 : ℝ := 0

theorem pairedN10239MinusP015Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨15, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
    (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx

theorem pairedN10239MinusP015BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP015Center2553‖ ≤ pairedN10239MinusP015Error2553 := by
  rw [pairedN10239MinusP015Exterior2553]
  norm_num [pairedN10239MinusP015Center2553, pairedN10239MinusP015Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP015DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP015Factor2553 * embedPair2542
          pairedN10239MinusP015Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP015Factor2553 : ℝ) * pairedN10239MinusP015Error2553
            := by
  rw [pairedN10239MinusP015Exterior2553]
  norm_num [pairedN10239MinusP015Factor2553, pairedN10239MinusP015Center2553,
      pairedN10239MinusP015Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP016Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP016Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP016Error2553 : ℝ := 0

theorem pairedN10239MinusP016Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨16, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
    (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx

theorem pairedN10239MinusP016BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP016Center2553‖ ≤ pairedN10239MinusP016Error2553 := by
  rw [pairedN10239MinusP016Exterior2553]
  norm_num [pairedN10239MinusP016Center2553, pairedN10239MinusP016Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP016DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP016Factor2553 * embedPair2542
          pairedN10239MinusP016Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP016Factor2553 : ℝ) * pairedN10239MinusP016Error2553
            := by
  rw [pairedN10239MinusP016Exterior2553]
  norm_num [pairedN10239MinusP016Factor2553, pairedN10239MinusP016Center2553,
      pairedN10239MinusP016Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP017Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP017Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP017Error2553 : ℝ := 0

theorem pairedN10239MinusP017Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨17, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
    (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx

theorem pairedN10239MinusP017BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP017Center2553‖ ≤ pairedN10239MinusP017Error2553 := by
  rw [pairedN10239MinusP017Exterior2553]
  norm_num [pairedN10239MinusP017Center2553, pairedN10239MinusP017Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP017DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP017Factor2553 * embedPair2542
          pairedN10239MinusP017Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP017Factor2553 : ℝ) * pairedN10239MinusP017Error2553
            := by
  rw [pairedN10239MinusP017Exterior2553]
  norm_num [pairedN10239MinusP017Factor2553, pairedN10239MinusP017Center2553,
      pairedN10239MinusP017Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP018Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP018Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP018Error2553 : ℝ := 0

theorem pairedN10239MinusP018Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨18, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
    (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx

theorem pairedN10239MinusP018BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP018Center2553‖ ≤ pairedN10239MinusP018Error2553 := by
  rw [pairedN10239MinusP018Exterior2553]
  norm_num [pairedN10239MinusP018Center2553, pairedN10239MinusP018Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP018DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP018Factor2553 * embedPair2542
          pairedN10239MinusP018Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP018Factor2553 : ℝ) * pairedN10239MinusP018Error2553
            := by
  rw [pairedN10239MinusP018Exterior2553]
  norm_num [pairedN10239MinusP018Factor2553, pairedN10239MinusP018Center2553,
      pairedN10239MinusP018Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP019Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP019Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP019Error2553 : ℝ := 0

theorem pairedN10239MinusP019Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨19, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
    (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx

theorem pairedN10239MinusP019BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP019Center2553‖ ≤ pairedN10239MinusP019Error2553 := by
  rw [pairedN10239MinusP019Exterior2553]
  norm_num [pairedN10239MinusP019Center2553, pairedN10239MinusP019Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP019DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP019Factor2553 * embedPair2542
          pairedN10239MinusP019Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP019Factor2553 : ℝ) * pairedN10239MinusP019Error2553
            := by
  rw [pairedN10239MinusP019Exterior2553]
  norm_num [pairedN10239MinusP019Factor2553, pairedN10239MinusP019Center2553,
      pairedN10239MinusP019Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP020Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP020Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP020Error2553 : ℝ := 0

theorem pairedN10239MinusP020Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨20, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
    (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx

theorem pairedN10239MinusP020BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP020Center2553‖ ≤ pairedN10239MinusP020Error2553 := by
  rw [pairedN10239MinusP020Exterior2553]
  norm_num [pairedN10239MinusP020Center2553, pairedN10239MinusP020Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP020DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP020Factor2553 * embedPair2542
          pairedN10239MinusP020Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP020Factor2553 : ℝ) * pairedN10239MinusP020Error2553
            := by
  rw [pairedN10239MinusP020Exterior2553]
  norm_num [pairedN10239MinusP020Factor2553, pairedN10239MinusP020Center2553,
      pairedN10239MinusP020Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP021Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP021Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP021Error2553 : ℝ := 0

theorem pairedN10239MinusP021Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨21, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
    (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx

theorem pairedN10239MinusP021BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP021Center2553‖ ≤ pairedN10239MinusP021Error2553 := by
  rw [pairedN10239MinusP021Exterior2553]
  norm_num [pairedN10239MinusP021Center2553, pairedN10239MinusP021Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP021DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP021Factor2553 * embedPair2542
          pairedN10239MinusP021Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP021Factor2553 : ℝ) * pairedN10239MinusP021Error2553
            := by
  rw [pairedN10239MinusP021Exterior2553]
  norm_num [pairedN10239MinusP021Factor2553, pairedN10239MinusP021Center2553,
      pairedN10239MinusP021Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP022Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP022Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP022Error2553 : ℝ := 0

theorem pairedN10239MinusP022Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨22, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
    (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx

theorem pairedN10239MinusP022BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP022Center2553‖ ≤ pairedN10239MinusP022Error2553 := by
  rw [pairedN10239MinusP022Exterior2553]
  norm_num [pairedN10239MinusP022Center2553, pairedN10239MinusP022Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP022DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP022Factor2553 * embedPair2542
          pairedN10239MinusP022Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP022Factor2553 : ℝ) * pairedN10239MinusP022Error2553
            := by
  rw [pairedN10239MinusP022Exterior2553]
  norm_num [pairedN10239MinusP022Factor2553, pairedN10239MinusP022Center2553,
      pairedN10239MinusP022Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP023Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP023Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP023Error2553 : ℝ := 0

theorem pairedN10239MinusP023Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨23, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
    (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx

theorem pairedN10239MinusP023BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP023Center2553‖ ≤ pairedN10239MinusP023Error2553 := by
  rw [pairedN10239MinusP023Exterior2553]
  norm_num [pairedN10239MinusP023Center2553, pairedN10239MinusP023Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP023DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP023Factor2553 * embedPair2542
          pairedN10239MinusP023Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP023Factor2553 : ℝ) * pairedN10239MinusP023Error2553
            := by
  rw [pairedN10239MinusP023Exterior2553]
  norm_num [pairedN10239MinusP023Factor2553, pairedN10239MinusP023Center2553,
      pairedN10239MinusP023Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP024Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP024Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP024Error2553 : ℝ := 0

theorem pairedN10239MinusP024Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨24, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
    (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx

theorem pairedN10239MinusP024BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP024Center2553‖ ≤ pairedN10239MinusP024Error2553 := by
  rw [pairedN10239MinusP024Exterior2553]
  norm_num [pairedN10239MinusP024Center2553, pairedN10239MinusP024Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP024DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP024Factor2553 * embedPair2542
          pairedN10239MinusP024Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP024Factor2553 : ℝ) * pairedN10239MinusP024Error2553
            := by
  rw [pairedN10239MinusP024Exterior2553]
  norm_num [pairedN10239MinusP024Factor2553, pairedN10239MinusP024Center2553,
      pairedN10239MinusP024Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP025Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP025Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP025Error2553 : ℝ := 0

theorem pairedN10239MinusP025Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨25, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
    (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx

theorem pairedN10239MinusP025BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP025Center2553‖ ≤ pairedN10239MinusP025Error2553 := by
  rw [pairedN10239MinusP025Exterior2553]
  norm_num [pairedN10239MinusP025Center2553, pairedN10239MinusP025Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP025DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP025Factor2553 * embedPair2542
          pairedN10239MinusP025Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP025Factor2553 : ℝ) * pairedN10239MinusP025Error2553
            := by
  rw [pairedN10239MinusP025Exterior2553]
  norm_num [pairedN10239MinusP025Factor2553, pairedN10239MinusP025Center2553,
      pairedN10239MinusP025Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP026Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP026Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP026Error2553 : ℝ := 0

theorem pairedN10239MinusP026Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨26, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
    (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx

theorem pairedN10239MinusP026BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP026Center2553‖ ≤ pairedN10239MinusP026Error2553 := by
  rw [pairedN10239MinusP026Exterior2553]
  norm_num [pairedN10239MinusP026Center2553, pairedN10239MinusP026Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP026DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP026Factor2553 * embedPair2542
          pairedN10239MinusP026Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP026Factor2553 : ℝ) * pairedN10239MinusP026Error2553
            := by
  rw [pairedN10239MinusP026Exterior2553]
  norm_num [pairedN10239MinusP026Factor2553, pairedN10239MinusP026Center2553,
      pairedN10239MinusP026Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP027Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP027Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP027Error2553 : ℝ := 0

theorem pairedN10239MinusP027Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨27, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
    (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx

theorem pairedN10239MinusP027BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP027Center2553‖ ≤ pairedN10239MinusP027Error2553 := by
  rw [pairedN10239MinusP027Exterior2553]
  norm_num [pairedN10239MinusP027Center2553, pairedN10239MinusP027Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP027DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP027Factor2553 * embedPair2542
          pairedN10239MinusP027Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP027Factor2553 : ℝ) * pairedN10239MinusP027Error2553
            := by
  rw [pairedN10239MinusP027Exterior2553]
  norm_num [pairedN10239MinusP027Factor2553, pairedN10239MinusP027Center2553,
      pairedN10239MinusP027Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP028Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP028Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP028Error2553 : ℝ := 0

theorem pairedN10239MinusP028Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨28, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
    (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx

theorem pairedN10239MinusP028BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP028Center2553‖ ≤ pairedN10239MinusP028Error2553 := by
  rw [pairedN10239MinusP028Exterior2553]
  norm_num [pairedN10239MinusP028Center2553, pairedN10239MinusP028Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP028DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP028Factor2553 * embedPair2542
          pairedN10239MinusP028Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP028Factor2553 : ℝ) * pairedN10239MinusP028Error2553
            := by
  rw [pairedN10239MinusP028Exterior2553]
  norm_num [pairedN10239MinusP028Factor2553, pairedN10239MinusP028Center2553,
      pairedN10239MinusP028Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

def pairedN10239MinusP029Center2553 : RatPair2542 := (0, 0)

def pairedN10239MinusP029Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239MinusP029Error2553 : ℝ := 0

theorem pairedN10239MinusP029Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN10239MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨29, by omega⟩ ^ 2 ≤ |pairedN10239MinusPosition2553| := by
    norm_num [storedWidth, pairedN10239MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
    (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx

theorem pairedN10239MinusP029BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP029Center2553‖ ≤ pairedN10239MinusP029Error2553 := by
  rw [pairedN10239MinusP029Exterior2553]
  norm_num [pairedN10239MinusP029Center2553, pairedN10239MinusP029Error2553,
      pairedN10239MinusZero2553]

theorem pairedN10239MinusP029DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN10239MinusPosition2553
        -
      embedPair2542 pairedN10239MinusP029Factor2553 * embedPair2542
          pairedN10239MinusP029Center2553‖ ≤
        (pairMagnitude2542 pairedN10239MinusP029Factor2553 : ℝ) * pairedN10239MinusP029Error2553
            := by
  rw [pairedN10239MinusP029Exterior2553]
  norm_num [pairedN10239MinusP029Factor2553, pairedN10239MinusP029Center2553,
      pairedN10239MinusP029Error2553, pairedN10239MinusZero2553, pairMagnitude2542]

theorem pairedN10239MinusGrid2553 :
    -stripRadius2303 + (10239 : ℝ) * (2 * stripRadius2303 / 10240) =
      pairedN10239MinusPosition2553 := by
  norm_num [stripRadius2303, pairedN10239MinusPosition2553]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.pairedN10239MinusP000DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP001DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP002DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP003DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP004DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP005DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP006DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP007DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP008DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP009DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP010DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP011DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP012DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP013DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP014DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP015DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP016DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP017DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP018DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP019DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP020DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP021DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP022DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP023DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP024DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP025DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP026DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP027DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP028DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusP029DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239MinusGrid2553
