import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def pairedN10239PlusPosition2553 : ℝ := ((335478789119 : ℝ) /
        51200000000)

theorem pairedN10239PlusZero2553 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def pairedN10239PlusP000Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP000Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP000Error2553 : ℝ := 0

theorem pairedN10239PlusP000Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN10239PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem pairedN10239PlusP000BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP000Center2553‖ ≤ pairedN10239PlusP000Error2553 := by
  rw [pairedN10239PlusP000Exterior2553]
  norm_num [pairedN10239PlusP000Center2553, pairedN10239PlusP000Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP000DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP000Factor2553 * embedPair2542 pairedN10239PlusP000Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP000Factor2553 : ℝ) * pairedN10239PlusP000Error2553 :=
            by
  rw [pairedN10239PlusP000Exterior2553]
  norm_num [pairedN10239PlusP000Factor2553, pairedN10239PlusP000Center2553,
      pairedN10239PlusP000Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP001Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP001Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP001Error2553 : ℝ := 0

theorem pairedN10239PlusP001Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨1, by omega⟩ pairedN10239PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨1, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨1, by omega⟩)
    (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx

theorem pairedN10239PlusP001BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP001Center2553‖ ≤ pairedN10239PlusP001Error2553 := by
  rw [pairedN10239PlusP001Exterior2553]
  norm_num [pairedN10239PlusP001Center2553, pairedN10239PlusP001Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP001DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP001Factor2553 * embedPair2542 pairedN10239PlusP001Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP001Factor2553 : ℝ) * pairedN10239PlusP001Error2553 :=
            by
  rw [pairedN10239PlusP001Exterior2553]
  norm_num [pairedN10239PlusP001Factor2553, pairedN10239PlusP001Center2553,
      pairedN10239PlusP001Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP002Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP002Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP002Error2553 : ℝ := 0

theorem pairedN10239PlusP002Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨2, by omega⟩ pairedN10239PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨2, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨2, by omega⟩)
    (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx

theorem pairedN10239PlusP002BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP002Center2553‖ ≤ pairedN10239PlusP002Error2553 := by
  rw [pairedN10239PlusP002Exterior2553]
  norm_num [pairedN10239PlusP002Center2553, pairedN10239PlusP002Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP002DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP002Factor2553 * embedPair2542 pairedN10239PlusP002Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP002Factor2553 : ℝ) * pairedN10239PlusP002Error2553 :=
            by
  rw [pairedN10239PlusP002Exterior2553]
  norm_num [pairedN10239PlusP002Factor2553, pairedN10239PlusP002Center2553,
      pairedN10239PlusP002Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP003Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP003Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP003Error2553 : ℝ := 0

theorem pairedN10239PlusP003Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨3, by omega⟩ pairedN10239PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨3, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨3, by omega⟩)
    (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx

theorem pairedN10239PlusP003BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP003Center2553‖ ≤ pairedN10239PlusP003Error2553 := by
  rw [pairedN10239PlusP003Exterior2553]
  norm_num [pairedN10239PlusP003Center2553, pairedN10239PlusP003Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP003DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP003Factor2553 * embedPair2542 pairedN10239PlusP003Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP003Factor2553 : ℝ) * pairedN10239PlusP003Error2553 :=
            by
  rw [pairedN10239PlusP003Exterior2553]
  norm_num [pairedN10239PlusP003Factor2553, pairedN10239PlusP003Center2553,
      pairedN10239PlusP003Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP004Input2553 : RatPair2542 := ((((-((20219 * 10^40
        + 976021499136154964655743210328250514336) * 10^40
        + 4626464180407007597998721152869609111361)) : ℚ) /
        ((34502 * 10^40
        + 6667990208777211291311779003017294650045) * 10^40
        + 2705343650009835671246640827596800000000)),
    (((-1853282464048842856447326451) : ℚ) /
        944473296573929042739200000000))

def pairedN10239PlusP004Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN10239PlusP004Factor2553 : RatPair2542 := ((((-(((((((((((24701857907646600878347 *
    10^40
        + 6897541664568968614030363266189346716521) * 10^40
        + 6257040340458582286247427258620577620051) * 10^40
        + 1427383318266281023795949864745146131278) * 10^40
        + 2921636375013895717251208564550073269428) * 10^40
        + 2745792613060032007967839855838513744564) * 10^40
        + 1388461426569835055893717109581682840987) * 10^40
        + 2857906186026867804326091297482474785128) * 10^40
        + 1318478523795018115055431753165290907698) * 10^40
        + 5729840962038129717693382791118448344080) * 10^40
        + 318845752683448179324906975119173247900) * 10^40
        + 4440946771489467047401682832911877630587)) : ℚ) /
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
    (((-((((((((51619690166502 * 10^40
        + 4197887989629939796766874382495355592277) * 10^40
        + 9987015181610795602576195594291721778650) * 10^40
        + 3852100732948153127167068313085285943355) * 10^40
        + 1755361455589358847858290773098676908987) * 10^40
        + 8353111843995234490298817326211724443469) * 10^40
        + 5504585527762778535028548406575492508222) * 10^40
        + 9845001809579880032366577524118142732892) * 10^40
        + 3992315636610762899165242897293411138923)) : ℚ) /
        (((((((1217308104115513119604376131045405684 * 10^40
        + 7414425181400613386230271978902089736372) * 10^40
        + 4607535991806235193780522107116660793201) * 10^40
        + 4718238591207537483169899846049339239955) * 10^40
        + 3968345537406587287975742847290213879555) * 10^40
        + 2066285933213707091867349581299728465159) * 10^40
        + 4137474666863446899770604309607374511162) * 10^40
        + 6083070446892797437003240783227746516992)))

noncomputable def pairedN10239PlusP004Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN10239PlusP004BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP004Center2553‖ ≤ pairedN10239PlusP004Error2553 := by
  have hx : |pairedN10239PlusPosition2553| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [pairedN10239PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN10239PlusP004Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN10239PlusP004Input2553]
  have hs : compactExp2547 pairedN10239PlusP004Input2553 17 =
      (pairedN10239PlusP004Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN10239PlusP004Input2553 17).2 : ℝ) =
      pairedN10239PlusP004Error2553
      := by
    rw [hs]
    norm_num [pairedN10239PlusP004Error2553]
  have h := compactExp_error2547 pairedN10239PlusP004Input2553 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      pairedN10239PlusPosition2553 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          pairedN10239PlusP004Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN10239PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN10239PlusP004Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN10239PlusP004DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP004Factor2553 * embedPair2542 pairedN10239PlusP004Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP004Factor2553 : ℝ) * pairedN10239PlusP004Error2553 :=
            by
  have hx : |pairedN10239PlusPosition2553| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [pairedN10239PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) pairedN10239PlusPosition2553 = embedPair2542
          pairedN10239PlusP004Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN10239PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN10239PlusP004Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN10239PlusP004BaseError2553
    (embedPair_magnitude2542 pairedN10239PlusP004Factor2553)

def pairedN10239PlusP005Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP005Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP005Error2553 : ℝ := 0

theorem pairedN10239PlusP005Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN10239PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem pairedN10239PlusP005BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP005Center2553‖ ≤ pairedN10239PlusP005Error2553 := by
  rw [pairedN10239PlusP005Exterior2553]
  norm_num [pairedN10239PlusP005Center2553, pairedN10239PlusP005Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP005DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP005Factor2553 * embedPair2542 pairedN10239PlusP005Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP005Factor2553 : ℝ) * pairedN10239PlusP005Error2553 :=
            by
  rw [pairedN10239PlusP005Exterior2553]
  norm_num [pairedN10239PlusP005Factor2553, pairedN10239PlusP005Center2553,
      pairedN10239PlusP005Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP006Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP006Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP006Error2553 : ℝ := 0

theorem pairedN10239PlusP006Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨6, by omega⟩ pairedN10239PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨6, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨6, by omega⟩)
    (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx

theorem pairedN10239PlusP006BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP006Center2553‖ ≤ pairedN10239PlusP006Error2553 := by
  rw [pairedN10239PlusP006Exterior2553]
  norm_num [pairedN10239PlusP006Center2553, pairedN10239PlusP006Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP006DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP006Factor2553 * embedPair2542 pairedN10239PlusP006Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP006Factor2553 : ℝ) * pairedN10239PlusP006Error2553 :=
            by
  rw [pairedN10239PlusP006Exterior2553]
  norm_num [pairedN10239PlusP006Factor2553, pairedN10239PlusP006Center2553,
      pairedN10239PlusP006Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP007Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP007Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP007Error2553 : ℝ := 0

theorem pairedN10239PlusP007Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨7, by omega⟩ pairedN10239PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨7, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨7, by omega⟩)
    (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx

theorem pairedN10239PlusP007BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP007Center2553‖ ≤ pairedN10239PlusP007Error2553 := by
  rw [pairedN10239PlusP007Exterior2553]
  norm_num [pairedN10239PlusP007Center2553, pairedN10239PlusP007Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP007DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP007Factor2553 * embedPair2542 pairedN10239PlusP007Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP007Factor2553 : ℝ) * pairedN10239PlusP007Error2553 :=
            by
  rw [pairedN10239PlusP007Exterior2553]
  norm_num [pairedN10239PlusP007Factor2553, pairedN10239PlusP007Center2553,
      pairedN10239PlusP007Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP008Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP008Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP008Error2553 : ℝ := 0

theorem pairedN10239PlusP008Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN10239PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨8, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨8, by omega⟩)
    (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx

theorem pairedN10239PlusP008BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP008Center2553‖ ≤ pairedN10239PlusP008Error2553 := by
  rw [pairedN10239PlusP008Exterior2553]
  norm_num [pairedN10239PlusP008Center2553, pairedN10239PlusP008Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP008DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP008Factor2553 * embedPair2542 pairedN10239PlusP008Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP008Factor2553 : ℝ) * pairedN10239PlusP008Error2553 :=
            by
  rw [pairedN10239PlusP008Exterior2553]
  norm_num [pairedN10239PlusP008Factor2553, pairedN10239PlusP008Center2553,
      pairedN10239PlusP008Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP009Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP009Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP009Error2553 : ℝ := 0

theorem pairedN10239PlusP009Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN10239PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨9, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨9, by omega⟩)
    (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx

theorem pairedN10239PlusP009BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP009Center2553‖ ≤ pairedN10239PlusP009Error2553 := by
  rw [pairedN10239PlusP009Exterior2553]
  norm_num [pairedN10239PlusP009Center2553, pairedN10239PlusP009Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP009DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP009Factor2553 * embedPair2542 pairedN10239PlusP009Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP009Factor2553 : ℝ) * pairedN10239PlusP009Error2553 :=
            by
  rw [pairedN10239PlusP009Exterior2553]
  norm_num [pairedN10239PlusP009Factor2553, pairedN10239PlusP009Center2553,
      pairedN10239PlusP009Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP010Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP010Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP010Error2553 : ℝ := 0

theorem pairedN10239PlusP010Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨10, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨10, by omega⟩)
    (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx

theorem pairedN10239PlusP010BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP010Center2553‖ ≤ pairedN10239PlusP010Error2553 := by
  rw [pairedN10239PlusP010Exterior2553]
  norm_num [pairedN10239PlusP010Center2553, pairedN10239PlusP010Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP010DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP010Factor2553 * embedPair2542 pairedN10239PlusP010Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP010Factor2553 : ℝ) * pairedN10239PlusP010Error2553 :=
            by
  rw [pairedN10239PlusP010Exterior2553]
  norm_num [pairedN10239PlusP010Factor2553, pairedN10239PlusP010Center2553,
      pairedN10239PlusP010Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP011Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP011Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP011Error2553 : ℝ := 0

theorem pairedN10239PlusP011Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨11, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨11, by omega⟩)
    (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx

theorem pairedN10239PlusP011BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP011Center2553‖ ≤ pairedN10239PlusP011Error2553 := by
  rw [pairedN10239PlusP011Exterior2553]
  norm_num [pairedN10239PlusP011Center2553, pairedN10239PlusP011Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP011DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP011Factor2553 * embedPair2542 pairedN10239PlusP011Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP011Factor2553 : ℝ) * pairedN10239PlusP011Error2553 :=
            by
  rw [pairedN10239PlusP011Exterior2553]
  norm_num [pairedN10239PlusP011Factor2553, pairedN10239PlusP011Center2553,
      pairedN10239PlusP011Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP012Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP012Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP012Error2553 : ℝ := 0

theorem pairedN10239PlusP012Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨12, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨12, by omega⟩)
    (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx

theorem pairedN10239PlusP012BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP012Center2553‖ ≤ pairedN10239PlusP012Error2553 := by
  rw [pairedN10239PlusP012Exterior2553]
  norm_num [pairedN10239PlusP012Center2553, pairedN10239PlusP012Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP012DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP012Factor2553 * embedPair2542 pairedN10239PlusP012Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP012Factor2553 : ℝ) * pairedN10239PlusP012Error2553 :=
            by
  rw [pairedN10239PlusP012Exterior2553]
  norm_num [pairedN10239PlusP012Factor2553, pairedN10239PlusP012Center2553,
      pairedN10239PlusP012Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP013Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP013Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP013Error2553 : ℝ := 0

theorem pairedN10239PlusP013Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨13, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨13, by omega⟩)
    (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx

theorem pairedN10239PlusP013BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP013Center2553‖ ≤ pairedN10239PlusP013Error2553 := by
  rw [pairedN10239PlusP013Exterior2553]
  norm_num [pairedN10239PlusP013Center2553, pairedN10239PlusP013Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP013DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP013Factor2553 * embedPair2542 pairedN10239PlusP013Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP013Factor2553 : ℝ) * pairedN10239PlusP013Error2553 :=
            by
  rw [pairedN10239PlusP013Exterior2553]
  norm_num [pairedN10239PlusP013Factor2553, pairedN10239PlusP013Center2553,
      pairedN10239PlusP013Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP014Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP014Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP014Error2553 : ℝ := 0

theorem pairedN10239PlusP014Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨14, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨14, by omega⟩)
    (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx

theorem pairedN10239PlusP014BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP014Center2553‖ ≤ pairedN10239PlusP014Error2553 := by
  rw [pairedN10239PlusP014Exterior2553]
  norm_num [pairedN10239PlusP014Center2553, pairedN10239PlusP014Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP014DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP014Factor2553 * embedPair2542 pairedN10239PlusP014Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP014Factor2553 : ℝ) * pairedN10239PlusP014Error2553 :=
            by
  rw [pairedN10239PlusP014Exterior2553]
  norm_num [pairedN10239PlusP014Factor2553, pairedN10239PlusP014Center2553,
      pairedN10239PlusP014Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP015Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP015Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP015Error2553 : ℝ := 0

theorem pairedN10239PlusP015Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨15, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨15, by omega⟩)
    (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx

theorem pairedN10239PlusP015BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP015Center2553‖ ≤ pairedN10239PlusP015Error2553 := by
  rw [pairedN10239PlusP015Exterior2553]
  norm_num [pairedN10239PlusP015Center2553, pairedN10239PlusP015Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP015DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP015Factor2553 * embedPair2542 pairedN10239PlusP015Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP015Factor2553 : ℝ) * pairedN10239PlusP015Error2553 :=
            by
  rw [pairedN10239PlusP015Exterior2553]
  norm_num [pairedN10239PlusP015Factor2553, pairedN10239PlusP015Center2553,
      pairedN10239PlusP015Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP016Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP016Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP016Error2553 : ℝ := 0

theorem pairedN10239PlusP016Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨16, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨16, by omega⟩)
    (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx

theorem pairedN10239PlusP016BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP016Center2553‖ ≤ pairedN10239PlusP016Error2553 := by
  rw [pairedN10239PlusP016Exterior2553]
  norm_num [pairedN10239PlusP016Center2553, pairedN10239PlusP016Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP016DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP016Factor2553 * embedPair2542 pairedN10239PlusP016Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP016Factor2553 : ℝ) * pairedN10239PlusP016Error2553 :=
            by
  rw [pairedN10239PlusP016Exterior2553]
  norm_num [pairedN10239PlusP016Factor2553, pairedN10239PlusP016Center2553,
      pairedN10239PlusP016Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP017Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP017Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP017Error2553 : ℝ := 0

theorem pairedN10239PlusP017Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨17, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨17, by omega⟩)
    (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx

theorem pairedN10239PlusP017BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP017Center2553‖ ≤ pairedN10239PlusP017Error2553 := by
  rw [pairedN10239PlusP017Exterior2553]
  norm_num [pairedN10239PlusP017Center2553, pairedN10239PlusP017Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP017DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP017Factor2553 * embedPair2542 pairedN10239PlusP017Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP017Factor2553 : ℝ) * pairedN10239PlusP017Error2553 :=
            by
  rw [pairedN10239PlusP017Exterior2553]
  norm_num [pairedN10239PlusP017Factor2553, pairedN10239PlusP017Center2553,
      pairedN10239PlusP017Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP018Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP018Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP018Error2553 : ℝ := 0

theorem pairedN10239PlusP018Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨18, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨18, by omega⟩)
    (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx

theorem pairedN10239PlusP018BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP018Center2553‖ ≤ pairedN10239PlusP018Error2553 := by
  rw [pairedN10239PlusP018Exterior2553]
  norm_num [pairedN10239PlusP018Center2553, pairedN10239PlusP018Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP018DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP018Factor2553 * embedPair2542 pairedN10239PlusP018Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP018Factor2553 : ℝ) * pairedN10239PlusP018Error2553 :=
            by
  rw [pairedN10239PlusP018Exterior2553]
  norm_num [pairedN10239PlusP018Factor2553, pairedN10239PlusP018Center2553,
      pairedN10239PlusP018Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP019Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP019Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP019Error2553 : ℝ := 0

theorem pairedN10239PlusP019Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨19, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨19, by omega⟩)
    (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx

theorem pairedN10239PlusP019BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP019Center2553‖ ≤ pairedN10239PlusP019Error2553 := by
  rw [pairedN10239PlusP019Exterior2553]
  norm_num [pairedN10239PlusP019Center2553, pairedN10239PlusP019Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP019DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP019Factor2553 * embedPair2542 pairedN10239PlusP019Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP019Factor2553 : ℝ) * pairedN10239PlusP019Error2553 :=
            by
  rw [pairedN10239PlusP019Exterior2553]
  norm_num [pairedN10239PlusP019Factor2553, pairedN10239PlusP019Center2553,
      pairedN10239PlusP019Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP020Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP020Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP020Error2553 : ℝ := 0

theorem pairedN10239PlusP020Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨20, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨20, by omega⟩)
    (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx

theorem pairedN10239PlusP020BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP020Center2553‖ ≤ pairedN10239PlusP020Error2553 := by
  rw [pairedN10239PlusP020Exterior2553]
  norm_num [pairedN10239PlusP020Center2553, pairedN10239PlusP020Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP020DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP020Factor2553 * embedPair2542 pairedN10239PlusP020Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP020Factor2553 : ℝ) * pairedN10239PlusP020Error2553 :=
            by
  rw [pairedN10239PlusP020Exterior2553]
  norm_num [pairedN10239PlusP020Factor2553, pairedN10239PlusP020Center2553,
      pairedN10239PlusP020Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP021Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP021Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP021Error2553 : ℝ := 0

theorem pairedN10239PlusP021Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨21, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨21, by omega⟩)
    (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx

theorem pairedN10239PlusP021BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP021Center2553‖ ≤ pairedN10239PlusP021Error2553 := by
  rw [pairedN10239PlusP021Exterior2553]
  norm_num [pairedN10239PlusP021Center2553, pairedN10239PlusP021Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP021DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP021Factor2553 * embedPair2542 pairedN10239PlusP021Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP021Factor2553 : ℝ) * pairedN10239PlusP021Error2553 :=
            by
  rw [pairedN10239PlusP021Exterior2553]
  norm_num [pairedN10239PlusP021Factor2553, pairedN10239PlusP021Center2553,
      pairedN10239PlusP021Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP022Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP022Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP022Error2553 : ℝ := 0

theorem pairedN10239PlusP022Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨22, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨22, by omega⟩)
    (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx

theorem pairedN10239PlusP022BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP022Center2553‖ ≤ pairedN10239PlusP022Error2553 := by
  rw [pairedN10239PlusP022Exterior2553]
  norm_num [pairedN10239PlusP022Center2553, pairedN10239PlusP022Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP022DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP022Factor2553 * embedPair2542 pairedN10239PlusP022Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP022Factor2553 : ℝ) * pairedN10239PlusP022Error2553 :=
            by
  rw [pairedN10239PlusP022Exterior2553]
  norm_num [pairedN10239PlusP022Factor2553, pairedN10239PlusP022Center2553,
      pairedN10239PlusP022Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP023Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP023Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP023Error2553 : ℝ := 0

theorem pairedN10239PlusP023Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨23, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨23, by omega⟩)
    (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx

theorem pairedN10239PlusP023BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP023Center2553‖ ≤ pairedN10239PlusP023Error2553 := by
  rw [pairedN10239PlusP023Exterior2553]
  norm_num [pairedN10239PlusP023Center2553, pairedN10239PlusP023Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP023DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP023Factor2553 * embedPair2542 pairedN10239PlusP023Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP023Factor2553 : ℝ) * pairedN10239PlusP023Error2553 :=
            by
  rw [pairedN10239PlusP023Exterior2553]
  norm_num [pairedN10239PlusP023Factor2553, pairedN10239PlusP023Center2553,
      pairedN10239PlusP023Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP024Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP024Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP024Error2553 : ℝ := 0

theorem pairedN10239PlusP024Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨24, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨24, by omega⟩)
    (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx

theorem pairedN10239PlusP024BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP024Center2553‖ ≤ pairedN10239PlusP024Error2553 := by
  rw [pairedN10239PlusP024Exterior2553]
  norm_num [pairedN10239PlusP024Center2553, pairedN10239PlusP024Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP024DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP024Factor2553 * embedPair2542 pairedN10239PlusP024Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP024Factor2553 : ℝ) * pairedN10239PlusP024Error2553 :=
            by
  rw [pairedN10239PlusP024Exterior2553]
  norm_num [pairedN10239PlusP024Factor2553, pairedN10239PlusP024Center2553,
      pairedN10239PlusP024Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP025Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP025Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP025Error2553 : ℝ := 0

theorem pairedN10239PlusP025Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨25, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨25, by omega⟩)
    (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx

theorem pairedN10239PlusP025BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP025Center2553‖ ≤ pairedN10239PlusP025Error2553 := by
  rw [pairedN10239PlusP025Exterior2553]
  norm_num [pairedN10239PlusP025Center2553, pairedN10239PlusP025Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP025DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP025Factor2553 * embedPair2542 pairedN10239PlusP025Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP025Factor2553 : ℝ) * pairedN10239PlusP025Error2553 :=
            by
  rw [pairedN10239PlusP025Exterior2553]
  norm_num [pairedN10239PlusP025Factor2553, pairedN10239PlusP025Center2553,
      pairedN10239PlusP025Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP026Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP026Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP026Error2553 : ℝ := 0

theorem pairedN10239PlusP026Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨26, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨26, by omega⟩)
    (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx

theorem pairedN10239PlusP026BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP026Center2553‖ ≤ pairedN10239PlusP026Error2553 := by
  rw [pairedN10239PlusP026Exterior2553]
  norm_num [pairedN10239PlusP026Center2553, pairedN10239PlusP026Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP026DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP026Factor2553 * embedPair2542 pairedN10239PlusP026Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP026Factor2553 : ℝ) * pairedN10239PlusP026Error2553 :=
            by
  rw [pairedN10239PlusP026Exterior2553]
  norm_num [pairedN10239PlusP026Factor2553, pairedN10239PlusP026Center2553,
      pairedN10239PlusP026Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP027Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP027Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP027Error2553 : ℝ := 0

theorem pairedN10239PlusP027Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨27, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨27, by omega⟩)
    (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx

theorem pairedN10239PlusP027BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP027Center2553‖ ≤ pairedN10239PlusP027Error2553 := by
  rw [pairedN10239PlusP027Exterior2553]
  norm_num [pairedN10239PlusP027Center2553, pairedN10239PlusP027Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP027DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP027Factor2553 * embedPair2542 pairedN10239PlusP027Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP027Factor2553 : ℝ) * pairedN10239PlusP027Error2553 :=
            by
  rw [pairedN10239PlusP027Exterior2553]
  norm_num [pairedN10239PlusP027Factor2553, pairedN10239PlusP027Center2553,
      pairedN10239PlusP027Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP028Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP028Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP028Error2553 : ℝ := 0

theorem pairedN10239PlusP028Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨28, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨28, by omega⟩)
    (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx

theorem pairedN10239PlusP028BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP028Center2553‖ ≤ pairedN10239PlusP028Error2553 := by
  rw [pairedN10239PlusP028Exterior2553]
  norm_num [pairedN10239PlusP028Center2553, pairedN10239PlusP028Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP028DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP028Factor2553 * embedPair2542 pairedN10239PlusP028Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP028Factor2553 : ℝ) * pairedN10239PlusP028Error2553 :=
            by
  rw [pairedN10239PlusP028Exterior2553]
  norm_num [pairedN10239PlusP028Factor2553, pairedN10239PlusP028Center2553,
      pairedN10239PlusP028Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

def pairedN10239PlusP029Center2553 : RatPair2542 := (0, 0)

def pairedN10239PlusP029Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN10239PlusP029Error2553 : ℝ := 0

theorem pairedN10239PlusP029Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN10239PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨29, by omega⟩ ^ 2 ≤ |pairedN10239PlusPosition2553| := by
    norm_num [storedWidth, pairedN10239PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨29, by omega⟩)
    (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx

theorem pairedN10239PlusP029BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP029Center2553‖ ≤ pairedN10239PlusP029Error2553 := by
  rw [pairedN10239PlusP029Exterior2553]
  norm_num [pairedN10239PlusP029Center2553, pairedN10239PlusP029Error2553,
      pairedN10239PlusZero2553]

theorem pairedN10239PlusP029DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN10239PlusPosition2553 -
      embedPair2542 pairedN10239PlusP029Factor2553 * embedPair2542 pairedN10239PlusP029Center2553‖
          ≤
        (pairMagnitude2542 pairedN10239PlusP029Factor2553 : ℝ) * pairedN10239PlusP029Error2553 :=
            by
  rw [pairedN10239PlusP029Exterior2553]
  norm_num [pairedN10239PlusP029Factor2553, pairedN10239PlusP029Center2553,
      pairedN10239PlusP029Error2553, pairedN10239PlusZero2553, pairMagnitude2542]

theorem pairedN10239PlusGrid2553 :
    -stripRadius2303 + (10239 : ℝ) * (2 * stripRadius2303 / 10240) =
      pairedN10239PlusPosition2553 := by
  norm_num [stripRadius2303, pairedN10239PlusPosition2553]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.pairedN10239PlusP000DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP001DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP002DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP003DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP004DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP005DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP006DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP007DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP008DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP009DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP010DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP011DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP012DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP013DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP014DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP015DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP016DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP017DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP018DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP019DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP020DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP021DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP022DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP023DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP024DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP025DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP026DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP027DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP028DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusP029DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN10239PlusGrid2553
