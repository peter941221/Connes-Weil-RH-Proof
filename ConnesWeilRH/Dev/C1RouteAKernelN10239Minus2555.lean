import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def kernelN10239MinusPosition2555 : ℝ := ((335478789119 : ℝ) /
        51200000000)

theorem kernelN10239MinusZero2555 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def kernelN10239MinusP000Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP000Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP000Error2555 : ℝ := 0

theorem kernelN10239MinusP000Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem kernelN10239MinusP000BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP000Center2555‖ ≤ kernelN10239MinusP000Error2555 := by
  rw [kernelN10239MinusP000Exterior2555]
  norm_num [kernelN10239MinusP000Center2555, kernelN10239MinusP000Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP000DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP000Factor2555 * embedPair2542
          kernelN10239MinusP000Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP000Factor2555 : ℝ) * kernelN10239MinusP000Error2555
            := by
  rw [kernelN10239MinusP000Exterior2555]
  norm_num [kernelN10239MinusP000Factor2555, kernelN10239MinusP000Center2555,
      kernelN10239MinusP000Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP001Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP001Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP001Error2555 : ℝ := 0

theorem kernelN10239MinusP001Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨1, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨1, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
    (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx

theorem kernelN10239MinusP001BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP001Center2555‖ ≤ kernelN10239MinusP001Error2555 := by
  rw [kernelN10239MinusP001Exterior2555]
  norm_num [kernelN10239MinusP001Center2555, kernelN10239MinusP001Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP001DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP001Factor2555 * embedPair2542
          kernelN10239MinusP001Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP001Factor2555 : ℝ) * kernelN10239MinusP001Error2555
            := by
  rw [kernelN10239MinusP001Exterior2555]
  norm_num [kernelN10239MinusP001Factor2555, kernelN10239MinusP001Center2555,
      kernelN10239MinusP001Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP002Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP002Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP002Error2555 : ℝ := 0

theorem kernelN10239MinusP002Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨2, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨2, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
    (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx

theorem kernelN10239MinusP002BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP002Center2555‖ ≤ kernelN10239MinusP002Error2555 := by
  rw [kernelN10239MinusP002Exterior2555]
  norm_num [kernelN10239MinusP002Center2555, kernelN10239MinusP002Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP002DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP002Factor2555 * embedPair2542
          kernelN10239MinusP002Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP002Factor2555 : ℝ) * kernelN10239MinusP002Error2555
            := by
  rw [kernelN10239MinusP002Exterior2555]
  norm_num [kernelN10239MinusP002Factor2555, kernelN10239MinusP002Center2555,
      kernelN10239MinusP002Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP003Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP003Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP003Error2555 : ℝ := 0

theorem kernelN10239MinusP003Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨3, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨3, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
    (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx

theorem kernelN10239MinusP003BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP003Center2555‖ ≤ kernelN10239MinusP003Error2555 := by
  rw [kernelN10239MinusP003Exterior2555]
  norm_num [kernelN10239MinusP003Center2555, kernelN10239MinusP003Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP003DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP003Factor2555 * embedPair2542
          kernelN10239MinusP003Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP003Factor2555 : ℝ) * kernelN10239MinusP003Error2555
            := by
  rw [kernelN10239MinusP003Exterior2555]
  norm_num [kernelN10239MinusP003Factor2555, kernelN10239MinusP003Center2555,
      kernelN10239MinusP003Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP004Input2555 : RatPair2542 := ((((-((20220 * 10^40
        + 8223985760775046352662199539254491013811) * 10^40
        + 5561935562252393339501278847130390888639)) : ℚ) /
        ((34502 * 10^40
        + 6667990208777211291311779003017294650045) * 10^40
        + 2705343650009835671246640827596800000000)),
    (((-1853282464048842856447326451) : ℚ) /
        944473296573929042739200000000))

def kernelN10239MinusP004Center2555 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def kernelN10239MinusP004Factor2555 : RatPair2542 := ((((-(((((((((((24701859142610917329898 *
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

noncomputable def kernelN10239MinusP004Error2555 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem kernelN10239MinusP004BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP004Center2555‖ ≤ kernelN10239MinusP004Error2555 := by
  have hx : |kernelN10239MinusPosition2555| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [kernelN10239MinusPosition2555, storedWidth]
  have hz : ‖embedPair2542 kernelN10239MinusP004Input2555‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, kernelN10239MinusP004Input2555]
  have hs : compactExp2547 kernelN10239MinusP004Input2555 17 =
      (kernelN10239MinusP004Center2555, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 kernelN10239MinusP004Input2555 17).2 : ℝ) =
      kernelN10239MinusP004Error2555 := by
    rw [hs]
    norm_num [kernelN10239MinusP004Error2555]
  have h := compactExp_error2547 kernelN10239MinusP004Input2555 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      kernelN10239MinusPosition2555 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          kernelN10239MinusP004Input2555) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [kernelN10239MinusPosition2555, storedWidth,
        nodeModulation2541,
      embedPair2542, kernelN10239MinusP004Input2555, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem kernelN10239MinusP004DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP004Factor2555 * embedPair2542
          kernelN10239MinusP004Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP004Factor2555 : ℝ) * kernelN10239MinusP004Error2555
            := by
  have hx : |kernelN10239MinusPosition2555| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [kernelN10239MinusPosition2555, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) kernelN10239MinusPosition2555 = embedPair2542
          kernelN10239MinusP004Factor2555 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      kernelN10239MinusPosition2555, storedWidth, nodeModulation2541, embedPair2542,
      kernelN10239MinusP004Factor2555, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ kernelN10239MinusP004BaseError2555
    (embedPair_magnitude2542 kernelN10239MinusP004Factor2555)

def kernelN10239MinusP005Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP005Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP005Error2555 : ℝ := 0

theorem kernelN10239MinusP005Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem kernelN10239MinusP005BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP005Center2555‖ ≤ kernelN10239MinusP005Error2555 := by
  rw [kernelN10239MinusP005Exterior2555]
  norm_num [kernelN10239MinusP005Center2555, kernelN10239MinusP005Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP005DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP005Factor2555 * embedPair2542
          kernelN10239MinusP005Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP005Factor2555 : ℝ) * kernelN10239MinusP005Error2555
            := by
  rw [kernelN10239MinusP005Exterior2555]
  norm_num [kernelN10239MinusP005Factor2555, kernelN10239MinusP005Center2555,
      kernelN10239MinusP005Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP006Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP006Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP006Error2555 : ℝ := 0

theorem kernelN10239MinusP006Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨6, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨6, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx

theorem kernelN10239MinusP006BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP006Center2555‖ ≤ kernelN10239MinusP006Error2555 := by
  rw [kernelN10239MinusP006Exterior2555]
  norm_num [kernelN10239MinusP006Center2555, kernelN10239MinusP006Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP006DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP006Factor2555 * embedPair2542
          kernelN10239MinusP006Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP006Factor2555 : ℝ) * kernelN10239MinusP006Error2555
            := by
  rw [kernelN10239MinusP006Exterior2555]
  norm_num [kernelN10239MinusP006Factor2555, kernelN10239MinusP006Center2555,
      kernelN10239MinusP006Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP007Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP007Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP007Error2555 : ℝ := 0

theorem kernelN10239MinusP007Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨7, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨7, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
    (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx

theorem kernelN10239MinusP007BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP007Center2555‖ ≤ kernelN10239MinusP007Error2555 := by
  rw [kernelN10239MinusP007Exterior2555]
  norm_num [kernelN10239MinusP007Center2555, kernelN10239MinusP007Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP007DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP007Factor2555 * embedPair2542
          kernelN10239MinusP007Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP007Factor2555 : ℝ) * kernelN10239MinusP007Error2555
            := by
  rw [kernelN10239MinusP007Exterior2555]
  norm_num [kernelN10239MinusP007Factor2555, kernelN10239MinusP007Center2555,
      kernelN10239MinusP007Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP008Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP008Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP008Error2555 : ℝ := 0

theorem kernelN10239MinusP008Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨8, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
    (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx

theorem kernelN10239MinusP008BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP008Center2555‖ ≤ kernelN10239MinusP008Error2555 := by
  rw [kernelN10239MinusP008Exterior2555]
  norm_num [kernelN10239MinusP008Center2555, kernelN10239MinusP008Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP008DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP008Factor2555 * embedPair2542
          kernelN10239MinusP008Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP008Factor2555 : ℝ) * kernelN10239MinusP008Error2555
            := by
  rw [kernelN10239MinusP008Exterior2555]
  norm_num [kernelN10239MinusP008Factor2555, kernelN10239MinusP008Center2555,
      kernelN10239MinusP008Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP009Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP009Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP009Error2555 : ℝ := 0

theorem kernelN10239MinusP009Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨9, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
    (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx

theorem kernelN10239MinusP009BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP009Center2555‖ ≤ kernelN10239MinusP009Error2555 := by
  rw [kernelN10239MinusP009Exterior2555]
  norm_num [kernelN10239MinusP009Center2555, kernelN10239MinusP009Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP009DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN10239MinusPosition2555 -
      embedPair2542 kernelN10239MinusP009Factor2555 * embedPair2542
          kernelN10239MinusP009Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP009Factor2555 : ℝ) * kernelN10239MinusP009Error2555
            := by
  rw [kernelN10239MinusP009Exterior2555]
  norm_num [kernelN10239MinusP009Factor2555, kernelN10239MinusP009Center2555,
      kernelN10239MinusP009Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP010Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP010Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP010Error2555 : ℝ := 0

theorem kernelN10239MinusP010Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨10, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
    (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx

theorem kernelN10239MinusP010BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP010Center2555‖ ≤ kernelN10239MinusP010Error2555 := by
  rw [kernelN10239MinusP010Exterior2555]
  norm_num [kernelN10239MinusP010Center2555, kernelN10239MinusP010Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP010DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP010Factor2555 * embedPair2542
          kernelN10239MinusP010Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP010Factor2555 : ℝ) * kernelN10239MinusP010Error2555
            := by
  rw [kernelN10239MinusP010Exterior2555]
  norm_num [kernelN10239MinusP010Factor2555, kernelN10239MinusP010Center2555,
      kernelN10239MinusP010Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP011Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP011Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP011Error2555 : ℝ := 0

theorem kernelN10239MinusP011Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨11, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
    (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx

theorem kernelN10239MinusP011BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP011Center2555‖ ≤ kernelN10239MinusP011Error2555 := by
  rw [kernelN10239MinusP011Exterior2555]
  norm_num [kernelN10239MinusP011Center2555, kernelN10239MinusP011Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP011DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP011Factor2555 * embedPair2542
          kernelN10239MinusP011Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP011Factor2555 : ℝ) * kernelN10239MinusP011Error2555
            := by
  rw [kernelN10239MinusP011Exterior2555]
  norm_num [kernelN10239MinusP011Factor2555, kernelN10239MinusP011Center2555,
      kernelN10239MinusP011Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP012Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP012Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP012Error2555 : ℝ := 0

theorem kernelN10239MinusP012Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨12, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
    (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx

theorem kernelN10239MinusP012BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP012Center2555‖ ≤ kernelN10239MinusP012Error2555 := by
  rw [kernelN10239MinusP012Exterior2555]
  norm_num [kernelN10239MinusP012Center2555, kernelN10239MinusP012Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP012DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP012Factor2555 * embedPair2542
          kernelN10239MinusP012Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP012Factor2555 : ℝ) * kernelN10239MinusP012Error2555
            := by
  rw [kernelN10239MinusP012Exterior2555]
  norm_num [kernelN10239MinusP012Factor2555, kernelN10239MinusP012Center2555,
      kernelN10239MinusP012Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP013Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP013Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP013Error2555 : ℝ := 0

theorem kernelN10239MinusP013Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨13, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
    (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx

theorem kernelN10239MinusP013BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP013Center2555‖ ≤ kernelN10239MinusP013Error2555 := by
  rw [kernelN10239MinusP013Exterior2555]
  norm_num [kernelN10239MinusP013Center2555, kernelN10239MinusP013Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP013DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP013Factor2555 * embedPair2542
          kernelN10239MinusP013Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP013Factor2555 : ℝ) * kernelN10239MinusP013Error2555
            := by
  rw [kernelN10239MinusP013Exterior2555]
  norm_num [kernelN10239MinusP013Factor2555, kernelN10239MinusP013Center2555,
      kernelN10239MinusP013Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP014Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP014Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP014Error2555 : ℝ := 0

theorem kernelN10239MinusP014Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨14, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
    (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx

theorem kernelN10239MinusP014BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP014Center2555‖ ≤ kernelN10239MinusP014Error2555 := by
  rw [kernelN10239MinusP014Exterior2555]
  norm_num [kernelN10239MinusP014Center2555, kernelN10239MinusP014Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP014DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP014Factor2555 * embedPair2542
          kernelN10239MinusP014Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP014Factor2555 : ℝ) * kernelN10239MinusP014Error2555
            := by
  rw [kernelN10239MinusP014Exterior2555]
  norm_num [kernelN10239MinusP014Factor2555, kernelN10239MinusP014Center2555,
      kernelN10239MinusP014Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP015Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP015Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP015Error2555 : ℝ := 0

theorem kernelN10239MinusP015Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨15, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
    (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx

theorem kernelN10239MinusP015BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP015Center2555‖ ≤ kernelN10239MinusP015Error2555 := by
  rw [kernelN10239MinusP015Exterior2555]
  norm_num [kernelN10239MinusP015Center2555, kernelN10239MinusP015Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP015DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP015Factor2555 * embedPair2542
          kernelN10239MinusP015Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP015Factor2555 : ℝ) * kernelN10239MinusP015Error2555
            := by
  rw [kernelN10239MinusP015Exterior2555]
  norm_num [kernelN10239MinusP015Factor2555, kernelN10239MinusP015Center2555,
      kernelN10239MinusP015Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP016Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP016Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP016Error2555 : ℝ := 0

theorem kernelN10239MinusP016Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨16, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
    (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx

theorem kernelN10239MinusP016BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP016Center2555‖ ≤ kernelN10239MinusP016Error2555 := by
  rw [kernelN10239MinusP016Exterior2555]
  norm_num [kernelN10239MinusP016Center2555, kernelN10239MinusP016Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP016DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP016Factor2555 * embedPair2542
          kernelN10239MinusP016Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP016Factor2555 : ℝ) * kernelN10239MinusP016Error2555
            := by
  rw [kernelN10239MinusP016Exterior2555]
  norm_num [kernelN10239MinusP016Factor2555, kernelN10239MinusP016Center2555,
      kernelN10239MinusP016Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP017Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP017Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP017Error2555 : ℝ := 0

theorem kernelN10239MinusP017Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨17, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
    (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx

theorem kernelN10239MinusP017BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP017Center2555‖ ≤ kernelN10239MinusP017Error2555 := by
  rw [kernelN10239MinusP017Exterior2555]
  norm_num [kernelN10239MinusP017Center2555, kernelN10239MinusP017Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP017DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP017Factor2555 * embedPair2542
          kernelN10239MinusP017Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP017Factor2555 : ℝ) * kernelN10239MinusP017Error2555
            := by
  rw [kernelN10239MinusP017Exterior2555]
  norm_num [kernelN10239MinusP017Factor2555, kernelN10239MinusP017Center2555,
      kernelN10239MinusP017Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP018Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP018Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP018Error2555 : ℝ := 0

theorem kernelN10239MinusP018Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨18, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
    (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx

theorem kernelN10239MinusP018BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP018Center2555‖ ≤ kernelN10239MinusP018Error2555 := by
  rw [kernelN10239MinusP018Exterior2555]
  norm_num [kernelN10239MinusP018Center2555, kernelN10239MinusP018Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP018DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP018Factor2555 * embedPair2542
          kernelN10239MinusP018Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP018Factor2555 : ℝ) * kernelN10239MinusP018Error2555
            := by
  rw [kernelN10239MinusP018Exterior2555]
  norm_num [kernelN10239MinusP018Factor2555, kernelN10239MinusP018Center2555,
      kernelN10239MinusP018Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP019Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP019Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP019Error2555 : ℝ := 0

theorem kernelN10239MinusP019Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨19, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
    (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx

theorem kernelN10239MinusP019BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP019Center2555‖ ≤ kernelN10239MinusP019Error2555 := by
  rw [kernelN10239MinusP019Exterior2555]
  norm_num [kernelN10239MinusP019Center2555, kernelN10239MinusP019Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP019DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP019Factor2555 * embedPair2542
          kernelN10239MinusP019Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP019Factor2555 : ℝ) * kernelN10239MinusP019Error2555
            := by
  rw [kernelN10239MinusP019Exterior2555]
  norm_num [kernelN10239MinusP019Factor2555, kernelN10239MinusP019Center2555,
      kernelN10239MinusP019Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP020Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP020Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP020Error2555 : ℝ := 0

theorem kernelN10239MinusP020Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨20, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
    (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx

theorem kernelN10239MinusP020BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP020Center2555‖ ≤ kernelN10239MinusP020Error2555 := by
  rw [kernelN10239MinusP020Exterior2555]
  norm_num [kernelN10239MinusP020Center2555, kernelN10239MinusP020Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP020DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP020Factor2555 * embedPair2542
          kernelN10239MinusP020Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP020Factor2555 : ℝ) * kernelN10239MinusP020Error2555
            := by
  rw [kernelN10239MinusP020Exterior2555]
  norm_num [kernelN10239MinusP020Factor2555, kernelN10239MinusP020Center2555,
      kernelN10239MinusP020Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP021Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP021Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP021Error2555 : ℝ := 0

theorem kernelN10239MinusP021Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨21, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
    (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx

theorem kernelN10239MinusP021BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP021Center2555‖ ≤ kernelN10239MinusP021Error2555 := by
  rw [kernelN10239MinusP021Exterior2555]
  norm_num [kernelN10239MinusP021Center2555, kernelN10239MinusP021Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP021DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP021Factor2555 * embedPair2542
          kernelN10239MinusP021Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP021Factor2555 : ℝ) * kernelN10239MinusP021Error2555
            := by
  rw [kernelN10239MinusP021Exterior2555]
  norm_num [kernelN10239MinusP021Factor2555, kernelN10239MinusP021Center2555,
      kernelN10239MinusP021Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP022Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP022Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP022Error2555 : ℝ := 0

theorem kernelN10239MinusP022Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨22, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
    (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx

theorem kernelN10239MinusP022BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP022Center2555‖ ≤ kernelN10239MinusP022Error2555 := by
  rw [kernelN10239MinusP022Exterior2555]
  norm_num [kernelN10239MinusP022Center2555, kernelN10239MinusP022Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP022DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP022Factor2555 * embedPair2542
          kernelN10239MinusP022Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP022Factor2555 : ℝ) * kernelN10239MinusP022Error2555
            := by
  rw [kernelN10239MinusP022Exterior2555]
  norm_num [kernelN10239MinusP022Factor2555, kernelN10239MinusP022Center2555,
      kernelN10239MinusP022Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP023Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP023Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP023Error2555 : ℝ := 0

theorem kernelN10239MinusP023Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨23, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
    (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx

theorem kernelN10239MinusP023BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP023Center2555‖ ≤ kernelN10239MinusP023Error2555 := by
  rw [kernelN10239MinusP023Exterior2555]
  norm_num [kernelN10239MinusP023Center2555, kernelN10239MinusP023Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP023DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP023Factor2555 * embedPair2542
          kernelN10239MinusP023Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP023Factor2555 : ℝ) * kernelN10239MinusP023Error2555
            := by
  rw [kernelN10239MinusP023Exterior2555]
  norm_num [kernelN10239MinusP023Factor2555, kernelN10239MinusP023Center2555,
      kernelN10239MinusP023Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP024Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP024Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP024Error2555 : ℝ := 0

theorem kernelN10239MinusP024Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨24, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
    (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx

theorem kernelN10239MinusP024BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP024Center2555‖ ≤ kernelN10239MinusP024Error2555 := by
  rw [kernelN10239MinusP024Exterior2555]
  norm_num [kernelN10239MinusP024Center2555, kernelN10239MinusP024Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP024DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP024Factor2555 * embedPair2542
          kernelN10239MinusP024Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP024Factor2555 : ℝ) * kernelN10239MinusP024Error2555
            := by
  rw [kernelN10239MinusP024Exterior2555]
  norm_num [kernelN10239MinusP024Factor2555, kernelN10239MinusP024Center2555,
      kernelN10239MinusP024Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP025Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP025Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP025Error2555 : ℝ := 0

theorem kernelN10239MinusP025Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨25, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
    (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx

theorem kernelN10239MinusP025BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP025Center2555‖ ≤ kernelN10239MinusP025Error2555 := by
  rw [kernelN10239MinusP025Exterior2555]
  norm_num [kernelN10239MinusP025Center2555, kernelN10239MinusP025Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP025DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP025Factor2555 * embedPair2542
          kernelN10239MinusP025Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP025Factor2555 : ℝ) * kernelN10239MinusP025Error2555
            := by
  rw [kernelN10239MinusP025Exterior2555]
  norm_num [kernelN10239MinusP025Factor2555, kernelN10239MinusP025Center2555,
      kernelN10239MinusP025Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP026Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP026Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP026Error2555 : ℝ := 0

theorem kernelN10239MinusP026Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨26, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
    (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx

theorem kernelN10239MinusP026BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP026Center2555‖ ≤ kernelN10239MinusP026Error2555 := by
  rw [kernelN10239MinusP026Exterior2555]
  norm_num [kernelN10239MinusP026Center2555, kernelN10239MinusP026Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP026DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP026Factor2555 * embedPair2542
          kernelN10239MinusP026Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP026Factor2555 : ℝ) * kernelN10239MinusP026Error2555
            := by
  rw [kernelN10239MinusP026Exterior2555]
  norm_num [kernelN10239MinusP026Factor2555, kernelN10239MinusP026Center2555,
      kernelN10239MinusP026Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP027Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP027Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP027Error2555 : ℝ := 0

theorem kernelN10239MinusP027Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨27, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
    (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx

theorem kernelN10239MinusP027BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP027Center2555‖ ≤ kernelN10239MinusP027Error2555 := by
  rw [kernelN10239MinusP027Exterior2555]
  norm_num [kernelN10239MinusP027Center2555, kernelN10239MinusP027Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP027DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP027Factor2555 * embedPair2542
          kernelN10239MinusP027Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP027Factor2555 : ℝ) * kernelN10239MinusP027Error2555
            := by
  rw [kernelN10239MinusP027Exterior2555]
  norm_num [kernelN10239MinusP027Factor2555, kernelN10239MinusP027Center2555,
      kernelN10239MinusP027Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP028Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP028Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP028Error2555 : ℝ := 0

theorem kernelN10239MinusP028Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨28, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
    (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx

theorem kernelN10239MinusP028BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP028Center2555‖ ≤ kernelN10239MinusP028Error2555 := by
  rw [kernelN10239MinusP028Exterior2555]
  norm_num [kernelN10239MinusP028Center2555, kernelN10239MinusP028Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP028DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP028Factor2555 * embedPair2542
          kernelN10239MinusP028Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP028Factor2555 : ℝ) * kernelN10239MinusP028Error2555
            := by
  rw [kernelN10239MinusP028Exterior2555]
  norm_num [kernelN10239MinusP028Factor2555, kernelN10239MinusP028Center2555,
      kernelN10239MinusP028Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

def kernelN10239MinusP029Center2555 : RatPair2542 := (0, 0)

def kernelN10239MinusP029Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN10239MinusP029Error2555 : ℝ := 0

theorem kernelN10239MinusP029Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN10239MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨29, by omega⟩ ^ 2 ≤ |kernelN10239MinusPosition2555| := by
    norm_num [storedWidth, kernelN10239MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
    (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx

theorem kernelN10239MinusP029BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP029Center2555‖ ≤ kernelN10239MinusP029Error2555 := by
  rw [kernelN10239MinusP029Exterior2555]
  norm_num [kernelN10239MinusP029Center2555, kernelN10239MinusP029Error2555,
      kernelN10239MinusZero2555]

theorem kernelN10239MinusP029DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN10239MinusPosition2555
        -
      embedPair2542 kernelN10239MinusP029Factor2555 * embedPair2542
          kernelN10239MinusP029Center2555‖ ≤
        (pairMagnitude2542 kernelN10239MinusP029Factor2555 : ℝ) * kernelN10239MinusP029Error2555
            := by
  rw [kernelN10239MinusP029Exterior2555]
  norm_num [kernelN10239MinusP029Factor2555, kernelN10239MinusP029Center2555,
      kernelN10239MinusP029Error2555, kernelN10239MinusZero2555, pairMagnitude2542]

theorem kernelN10239MinusGrid2555 :
    -stripRadius2303 + (10239 : ℝ) * (2 * stripRadius2303 / 10240) =
      kernelN10239MinusPosition2555 := by
  norm_num [stripRadius2303, kernelN10239MinusPosition2555]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.kernelN10239MinusP000DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP001DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP002DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP003DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP004DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP005DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP006DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP007DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP008DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP009DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP010DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP011DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP012DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP013DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP014DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP015DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP016DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP017DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP018DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP019DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP020DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP021DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP022DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP023DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP024DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP025DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP026DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP027DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP028DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusP029DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN10239MinusGrid2555
