import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def corrC02700MinusMidpointPosition2570 : ℝ := (((-317128708839) : ℝ) /
        102400000000)

theorem corrC02700MinusMidpointZero2570 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def corrC02700MinusMidpointP000Center2570 : RatPair2542 := (0, 0)

def corrC02700MinusMidpointP000Factor2570 : RatPair2542 := (0, 0)

noncomputable def corrC02700MinusMidpointP000Error2570 : ℝ := 0

theorem corrC02700MinusMidpointP000Exterior2570 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02700MinusMidpointPosition2570 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |corrC02700MinusMidpointPosition2570| := by
    norm_num [storedWidth, corrC02700MinusMidpointPosition2570]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem corrC02700MinusMidpointP000BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP000Center2570‖ ≤
          corrC02700MinusMidpointP000Error2570 := by
  rw [corrC02700MinusMidpointP000Exterior2570]
  norm_num [corrC02700MinusMidpointP000Center2570, corrC02700MinusMidpointP000Error2570,
      corrC02700MinusMidpointZero2570]

theorem corrC02700MinusMidpointP000DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP000Factor2570 * embedPair2542
          corrC02700MinusMidpointP000Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP000Factor2570 : ℝ) *
            corrC02700MinusMidpointP000Error2570 := by
  rw [corrC02700MinusMidpointP000Exterior2570]
  norm_num [corrC02700MinusMidpointP000Factor2570, corrC02700MinusMidpointP000Center2570,
      corrC02700MinusMidpointP000Error2570,
      corrC02700MinusMidpointZero2570, pairMagnitude2542]

def corrC02700MinusMidpointP001Input2570 : RatPair2542 := ((((-((74 * 10^40
        + 3163554082308786923030623187936917919547) * 10^40
        + 6189645194398852582143451811084217740401)) : ℚ) /
        ((208 * 10^40
        + 8043940912794372598641292711490528776820) * 10^40
        + 5100987153752063079186153183641600000000)),
    ((1751911280236833479653958331 : ℚ) /
        7378697629483820646400000000))

def corrC02700MinusMidpointP001Center2570 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP001Factor2570 : RatPair2542 := ((((((((((1132763226209463238456819139
    * 10^40
        + 8119391114167269652476082976088842914012) * 10^40
        + 7856481772649195506408251399506414144088) * 10^40
        + 7866010397092998199076805976569982043983) * 10^40
        + 4258929802937423270093458999732433948387) * 10^40
        + 9742797506922861728728352279368102469510) * 10^40
        + 5996829485580677810209469267843528061587) * 10^40
        + 1664934739003216640789739530530616564855) : ℚ) /
        (((((((3114429284045443776614 * 10^40
        + 9680444835455280460140749335584001093358) * 10^40
        + 1911666244245281745966243066311980061204) * 10^40
        + 528329653512445415592798536726260464355) * 10^40
        + 1801406946283238328514682425762387519584) * 10^40
        + 3490628447045898579670805122056367448802) * 10^40
        + 9889831084762471402572093792358697720904) * 10^40
        + 1848635307526357013279069283978496180224)),
    (((-(((266306062171405471405165029984807320 * 10^40
        + 9682629607746112831653135508097926908624) * 10^40
        + 1745608980219792639380634346889746461562) * 10^40
        + 3795471575732483257973729707370645078851)) : ℚ) /
        (((5580707198953770389983466974217 * 10^40
        + 9009587017588522182642900543038828648160) * 10^40
        + 1385716774918519770136509599163173339651) * 10^40
        + 717525258581434384188834601649116807168)))

noncomputable def corrC02700MinusMidpointP001Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP001BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP001Center2570‖ ≤
          corrC02700MinusMidpointP001Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP001Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP001Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP001Input2570 9 =
      (corrC02700MinusMidpointP001Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP001Input2570 9).2 : ℝ) =
      corrC02700MinusMidpointP001Error2570 := by
    rw [hs]
    norm_num [corrC02700MinusMidpointP001Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP001Input2570 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          corrC02700MinusMidpointP001Input2570)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP001Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP001DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP001Factor2570 * embedPair2542
          corrC02700MinusMidpointP001Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP001Factor2570 : ℝ) *
            corrC02700MinusMidpointP001Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP001Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP001Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP001BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP001Factor2570)

def corrC02700MinusMidpointP002Input2570 : RatPair2542 := ((((-((1908 * 10^40
        + 9356477313226526661601126851044270189063) * 10^40
        + 5191776234307827898306730134726634237041)) : ℚ) /
        ((8147 * 10^40
        + 6895918656149932623563298325318453465194) * 10^40
        + 9452298146475584633489225469132800000000)),
    (((-1751911280236833479653958331) : ℚ) /
        3689348814741910323200000000))

def corrC02700MinusMidpointP002Center2570 : RatPair2542 := ((((-7510330962121851658113) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-167206057629782703065) : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)))

def corrC02700MinusMidpointP002Factor2570 : RatPair2542 :=
    ((((((((((10534369830769823946654412651471 * 10^40
        + 7554884173720066135864938810368621282048) * 10^40
        + 3789086745289024086286208019072012494471) * 10^40
        + 8337973569641228182859912612327044976075) * 10^40
        + 9453104086129071045660551543060973502797) * 10^40
        + 303525591534081656094381108027484829831) * 10^40
        + 453200870101343002555780730813487124852) * 10^40
        + 4839333591394096063559176378504528321655) : ℚ) /
        (((((((115525490748260174715076203586 * 10^40
        + 9841353533651885412466610413671356681188) * 10^40
        + 7642562632268933197074993551067893033088) * 10^40
        + 7944740562176547541096260135886068737629) * 10^40
        + 3285334223738111778445965844867044888674) * 10^40
        + 5575446764899759210915261339522269986558) * 10^40
        + 2997495251739314740075027225728645103699) * 10^40
        + 5374814466683858103126194814725667160064)),
    (((((110085078351733313650421521724417526388 * 10^40
        + 3811853848663388576075215587906880428348) * 10^40
        + 7828300702435659698791544541217039537203) * 10^40
        + 1669426527034140158068549501405403857731) : ℚ) /
        (((33989040990922379173162885590005531 * 10^40
        + 7367314092441466677914319666200769647378) * 10^40
        + 7700021938458516116839260266589107341797) * 10^40
        + 6043262579466265220719258022173902635008)))

noncomputable def corrC02700MinusMidpointP002Error2570 : ℝ := ((47917824040196111573 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP002BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP002Center2570‖ ≤
          corrC02700MinusMidpointP002Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP002Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP002Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP002Input2570 8 =
      (corrC02700MinusMidpointP002Center2570, ((47917824040196111573 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP002Input2570 8).2 : ℝ) =
      corrC02700MinusMidpointP002Error2570 := by
    rw [hs]
    norm_num [corrC02700MinusMidpointP002Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP002Input2570 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          corrC02700MinusMidpointP002Input2570)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP002Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP002DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP002Factor2570 * embedPair2542
          corrC02700MinusMidpointP002Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP002Factor2570 : ℝ) *
            corrC02700MinusMidpointP002Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP002Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP002Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP002BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP002Factor2570)

def corrC02700MinusMidpointP003Input2570 : RatPair2542 := ((((-((6741898 * 10^40
        + 8650175576592174173380311150688129946428) * 10^40
        + 2573857778485855228570792044839354408089)) : ℚ) /
        ((39860431 * 10^40
        + 3525369205518296877772896888819194996209) * 10^40
        + 8027785848626107559175480881971200000000)),
    (((-1751911280236833479653958331) : ℚ) /
        3689348814741910323200000000))

def corrC02700MinusMidpointP003Center2570 : RatPair2542 := ((((-16457100312752944049586069821) :
    ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    (((-187592818628376015785955978523) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def corrC02700MinusMidpointP003Factor2570 : RatPair2542 := ((((-((((((((9021010 * 10^40
        + 7538576777924895246672287281380819574593) * 10^40
        + 3484211894904830467420276272133095308933) * 10^40
        + 4259686595679535391560114053491786929667) * 10^40
        + 4059046284294308427693871647239196034358) * 10^40
        + 8671524274456012512110087396662955631266) * 10^40
        + 2670232904475845291238865679232671160965) * 10^40
        + 2449828312399297487403933784528843040487) * 10^40
        + 3046874937560542599225785784716002507945)) : ℚ) /
        ((((((((6617 * 10^40
        + 7125422076468304010688842754536356362659) * 10^40
        + 5386377453594199918208717244286697190680) * 10^40
        + 8071597337658982165835423313409578778727) * 10^40
        + 5691218389018228563362915437783942818555) * 10^40
        + 5492133941841779868889048247305091618183) * 10^40
        + 5000432551886719187743182772291576826294) * 10^40
        + 3387671642793116577989155749696368425591) * 10^40
        + 1234362302035428370555877184122948419584)),
    ((((((88349 * 10^40
        + 5377399852460610504648317607317891726760) * 10^40
        + 523864966544541843462082781805162416279) * 10^40
        + 3171159756559074893608582035160038959234) * 10^40
        + 1540950655181157192517822730013073385971) : ℚ) /
        ((((81 * 10^40
        + 3493241656477858559825274349299360270924) * 10^40
        + 1698071194914685148847557874921996951747) * 10^40
        + 5087744417512963469373459473366349438543) * 10^40
        + 6929975997517327555611596299530118627328)))

noncomputable def corrC02700MinusMidpointP003Error2570 : ℝ := ((787019084893669535021784089 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP003BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP003Center2570‖ ≤
          corrC02700MinusMidpointP003Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP003Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP003Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP003Input2570 8 =
      (corrC02700MinusMidpointP003Center2570, ((787019084893669535021784089 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP003Input2570 8).2 : ℝ) =
      corrC02700MinusMidpointP003Error2570 := by
    rw [hs]
    norm_num [corrC02700MinusMidpointP003Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP003Input2570 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          corrC02700MinusMidpointP003Input2570)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP003Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP003DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP003Factor2570 * embedPair2542
          corrC02700MinusMidpointP003Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP003Factor2570 : ℝ) *
            corrC02700MinusMidpointP003Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP003Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP003Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP003BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP003Factor2570)

def corrC02700MinusMidpointP004Input2570 : RatPair2542 := ((((-((4313 * 10^40
        + 1891010053817582509092773862775633242315) * 10^40
        + 9610172859229760383941744954062571737041)) : ℚ) /
        ((29780 * 10^40
        + 5895054484312759971766663273404887092534) * 10^40
        + 1331668037402944633489225469132800000000)),
    ((1751911280236833479653958331 : ℚ) /
        3689348814741910323200000000))

def corrC02700MinusMidpointP004Center2570 : RatPair2542 := ((((-66328937998152592934425233428247)
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((23627401317734783120891400711731 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def corrC02700MinusMidpointP004Factor2570 : RatPair2542 :=
    ((((-(((((((30954040959361306274257992769388445 *
    10^40
        + 3307788811975284394444063995289067116743) * 10^40
        + 7193140843212060122927895909232673150817) * 10^40
        + 6089987060683235084406791062865815509534) * 10^40
        + 3586682692887691428707533436520674691821) * 10^40
        + 7917032855818946551845104660800600791198) * 10^40
        + 5360061266028496545586726560021466101848) * 10^40
        + 4318710567744100768830453992589221678345)) : ℚ) /
        (((((((20619260398185266867770268076303 * 10^40
        + 810658110180138412392108416437618619019) * 10^40
        + 986181953701573507156749035082291902121) * 10^40
        + 3051596691796931788383473745700259187266) * 10^40
        + 8089028926060019584365844952163407895982) * 10^40
        + 9107592919862370423145459969197768349176) * 10^40
        + 2345231521801162654220189886828470833514) * 10^40
        + 2599327465781412486793394814725667160064)),
    (((-(((237838370127615280510618320352744437695 * 10^40
        + 471219523567470894230849512947328949599) * 10^40
        + 4294915038852773613808671551188729571958) * 10^40
        + 3563884917910234040135338417421028857731)) : ℚ) /
        (((454084357781516923150618442898949233 * 10^40
        + 7351628418167286031113461605381744134575) * 10^40
        + 430352166525634131497045575473615820870) * 10^40
        + 4011403570180837345698458022173902635008)))

noncomputable def corrC02700MinusMidpointP004Error2570 : ℝ := ((386980696826640705426490371081 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP004BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP004Center2570‖ ≤
          corrC02700MinusMidpointP004Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP004Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP004Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP004Input2570 8 =
      (corrC02700MinusMidpointP004Center2570, ((386980696826640705426490371081 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP004Input2570 8).2 : ℝ) =
      corrC02700MinusMidpointP004Error2570 := by
    rw [hs]
    norm_num [corrC02700MinusMidpointP004Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP004Input2570 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          corrC02700MinusMidpointP004Input2570)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP004Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP004DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP004Factor2570 * embedPair2542
          corrC02700MinusMidpointP004Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP004Factor2570 : ℝ) *
            corrC02700MinusMidpointP004Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP004Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP004Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP004BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP004Factor2570)

def corrC02700MinusMidpointP005Center2570 : RatPair2542 := (0, 0)

def corrC02700MinusMidpointP005Factor2570 : RatPair2542 := (0, 0)

noncomputable def corrC02700MinusMidpointP005Error2570 : ℝ := 0

theorem corrC02700MinusMidpointP005Exterior2570 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02700MinusMidpointPosition2570 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |corrC02700MinusMidpointPosition2570| := by
    norm_num [storedWidth, corrC02700MinusMidpointPosition2570]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem corrC02700MinusMidpointP005BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP005Center2570‖ ≤
          corrC02700MinusMidpointP005Error2570 := by
  rw [corrC02700MinusMidpointP005Exterior2570]
  norm_num [corrC02700MinusMidpointP005Center2570, corrC02700MinusMidpointP005Error2570,
      corrC02700MinusMidpointZero2570]

theorem corrC02700MinusMidpointP005DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP005Factor2570 * embedPair2542
          corrC02700MinusMidpointP005Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP005Factor2570 : ℝ) *
            corrC02700MinusMidpointP005Error2570 := by
  rw [corrC02700MinusMidpointP005Exterior2570]
  norm_num [corrC02700MinusMidpointP005Factor2570, corrC02700MinusMidpointP005Center2570,
      corrC02700MinusMidpointP005Error2570,
      corrC02700MinusMidpointZero2570, pairMagnitude2542]

def corrC02700MinusMidpointP006Input2570 : RatPair2542 :=
    ((((-1009480612784001817040786481870793719) : ℚ) /
        1761648103394083163919587737600000000),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP006Center2570 : RatPair2542 := (((2552935579348625 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP006Factor2570 : RatPair2542 := (((((4082326832474695 * 10^40
        + 7295768440799001721422882221693915474629) * 10^40
        + 7325624647884538795578102645424357382081) : ℚ) /
        ((815787311011 * 10^40
        + 6853265494000320941081736296179322639449) * 10^40
        + 1419175634369515182312410581697429528324)),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP006Error2570 : ℝ := ((3648537530399 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem corrC02700MinusMidpointP006BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP006Center2570‖ ≤
          corrC02700MinusMidpointP006Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP006Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP006Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP006Input2570 7 =
      (corrC02700MinusMidpointP006Center2570, ((3648537530399 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP006Input2570 7).2 : ℝ) =
      corrC02700MinusMidpointP006Error2570 := by
    rw [hs]
    norm_num [corrC02700MinusMidpointP006Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP006Input2570 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          corrC02700MinusMidpointP006Input2570)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP006Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP006DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP006Factor2570 * embedPair2542
          corrC02700MinusMidpointP006Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP006Factor2570 : ℝ) *
            corrC02700MinusMidpointP006Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP006Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP006Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP006BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP006Factor2570)

def corrC02700MinusMidpointP007Input2570 : RatPair2542 := ((((-((6741898 * 10^40
        + 8650175576592174173380311150688129946428) * 10^40
        + 2573857778485855228570792044839354408089)) : ℚ) /
        ((9965107 * 10^40
        + 8381342301379574219443224222204798749052) * 10^40
        + 4506946462156526889793870220492800000000)),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP007Center2570 : RatPair2542 := (((57295603695874659276408122021 : ℚ)
    /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP007Factor2570 : RatPair2542 := ((((((((((2373420851507845458 * 10^40
        + 19829720076737538422299602769622667422) * 10^40
        + 108703650287152184729614805266045974106) * 10^40
        + 89269913041115318692350019267859828171) * 10^40
        + 6209953821447454654869806245400071886612) * 10^40
        + 5903360112075628255786335697602699210518) * 10^40
        + 1291550549799090741640929109183310185761) * 10^40
        + 4637359871814986214583906702064787648001) : ℚ) /
        (((((((13364364048738220 * 10^40
        + 9873912850285142990661540865378025809024) * 10^40
        + 8058317841536651428348183510313302560340) * 10^40
        + 8900892847096286742881735348576158253580) * 10^40
        + 3091263491405380678350393930446011388549) * 10^40
        + 5174230682592482482358913241606013835824) * 10^40
        + 7057316303657026652629616144636228850203) * 10^40
        + 8242495487259944858335626808259150592004)),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP007Error2570 : ℝ := ((31723657183144844024517521 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP007BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP007Center2570‖ ≤
          corrC02700MinusMidpointP007Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP007Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP007Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP007Input2570 6 =
      (corrC02700MinusMidpointP007Center2570, ((31723657183144844024517521 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP007Input2570 6).2 : ℝ) =
      corrC02700MinusMidpointP007Error2570 := by
    rw [hs]
    norm_num [corrC02700MinusMidpointP007Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP007Input2570 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          corrC02700MinusMidpointP007Input2570)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP007Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP007DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP007Factor2570 * embedPair2542
          corrC02700MinusMidpointP007Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP007Factor2570 : ℝ) *
            corrC02700MinusMidpointP007Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP007Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP007Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP007BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP007Factor2570)

def corrC02700MinusMidpointP008Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1261719220645415482412484183 : ℚ) /
        3777893186295716170956800000000))

def corrC02700MinusMidpointP008Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP008Factor2570 : RatPair2542 := (((((((((((596622 * 10^40
        + 1937259399003170384770412399083337058667) * 10^40
        + 5774253684706216891521115264014076821272) * 10^40
        + 2200149675538378146373182107183704940158) * 10^40
        + 8421888864443038816151022379858157919477) * 10^40
        + 4142021641192420227786810031905908979479) * 10^40
        + 5668354998588492972601292619882462408542) * 10^40
        + 2384553503329382057822077845980161208747) * 10^40
        + 3948099862950697238388571285480029785375) : ℚ) /
        (((((((463521426468943547866548407699 * 10^40
        + 4022210258990202806204528313208470673748) * 10^40
        + 5052517913323581257129016392834856567500) * 10^40
        + 1217118767789225576675830556285333770449) * 10^40
        + 6522660495321192774480747347690463506678) * 10^40
        + 33069778495902451305013714364284200809) * 10^40
        + 5734242227401081649106548566981470429641) * 10^40
        + 2336703859004563560370068736491793678336)),
    (((-((((3119 * 10^40
        + 4282969964872324122186132689803073234783) * 10^40
        + 3211946083986421795824603072855146374638) * 10^40
        + 9710871902203743010708557311973161709387) * 10^40
        + 4176830769536333337437578262961301241529)) : ℚ) /
        (((9726058270618054800691549816849239 * 10^40
        + 9798539442483679798469515274174623128282) * 10^40
        + 1964437166481223132393969267753061294625) * 10^40
        + 5904135280119133576510010371294319607808)))

noncomputable def corrC02700MinusMidpointP008Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP008BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP008Center2570‖ ≤
          corrC02700MinusMidpointP008Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP008Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP008Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP008Input2570 17 =
      (corrC02700MinusMidpointP008Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP008Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP008Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP008Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP008Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP008Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP008Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP008DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP008Factor2570 * embedPair2542
          corrC02700MinusMidpointP008Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP008Factor2570 : ℝ) *
            corrC02700MinusMidpointP008Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP008Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP008Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP008BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP008Factor2570)

def corrC02700MinusMidpointP009Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1876507056447276098253971529 : ℚ) /
        3777893186295716170956800000000))

def corrC02700MinusMidpointP009Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP009Factor2570 : RatPair2542 := (((((((((((596622 * 10^40
        + 1937259286768087295529544815160936451889) * 10^40
        + 9511759479963489922529874740244131434848) * 10^40
        + 6789321966415170105160084108378982534995) * 10^40
        + 9535128148211780212598936567938608343327) * 10^40
        + 3558658570130671265914081244065935619791) * 10^40
        + 2129655794847143803283398162904611169385) * 10^40
        + 7590973423788861119331733843801419881375) * 10^40
        + 6642492777692311511177316463541014980063) : ℚ) /
        (((((((463521426468943547866548407699 * 10^40
        + 4022210258990202806204528313208470673748) * 10^40
        + 5052517913323581257129016392834856567500) * 10^40
        + 1217118767789225576675830556285333770449) * 10^40
        + 6522660495321192774480747347690463506678) * 10^40
        + 33069778495902451305013714364284200809) * 10^40
        + 5734242227401081649106548566981470429641) * 10^40
        + 2336703859004563560370068736491793678336)),
    (((-((((1047 * 10^40
        + 6080729012344005486511862532492093797287) * 10^40
        + 4536826450480060665993189868243731120002) * 10^40
        + 4705097490212891692248103074015738186224) * 10^40
        + 4150136564658909585843917954403662480719)) : ℚ) /
        (((2196206706268593019510995119933699 * 10^40
        + 3502896003141476083525374416749108448321) * 10^40
        + 7862937424689308449250251124976497711689) * 10^40
        + 6494482160026901130179679761260007653376)))

noncomputable def corrC02700MinusMidpointP009Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP009BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP009Center2570‖ ≤
          corrC02700MinusMidpointP009Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP009Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP009Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP009Input2570 17 =
      (corrC02700MinusMidpointP009Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP009Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP009Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP009Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP009Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP009Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP009Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP009DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP009Factor2570 * embedPair2542
          corrC02700MinusMidpointP009Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP009Factor2570 : ℝ) *
            corrC02700MinusMidpointP009Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP009Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP009Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP009BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP009Factor2570)

def corrC02700MinusMidpointP010Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1116282043593459096767143119 : ℚ) /
        1888946593147858085478400000000))

def corrC02700MinusMidpointP010Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP010Factor2570 : RatPair2542 := (((((((((((149155 * 10^40
        + 5484314800414436191359786531006662174673) * 10^40
        + 8765272050207869707717933392967353942521) * 10^40
        + 8305685594178232434495595506241778260809) * 10^40
        + 9124304186671060863706365634546982372351) * 10^40
        + 5929779413277157299804369754773775901201) * 10^40
        + 1378916803959539065591250944646609873683) * 10^40
        + 4685176984406205998721741592544936099717) * 10^40
        + 8268565143801447887839525465247470501455) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((19318 * 10^40
        + 9833052022045670792753232055162336532954) * 10^40
        + 8456767823520742600547862099506724230432) * 10^40
        + 6829461034473689155658828212360292771023) * 10^40
        + 3921888087324517064325093837536392753479)) : ℚ) /
        (((34041203947163191802420424358972339 * 10^40
        + 9294888048692879294643303459611180948987) * 10^40
        + 6875530082684280963378892437135714531189) * 10^40
        + 5664473480416967517785036299530118627328)))

noncomputable def corrC02700MinusMidpointP010Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP010BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP010Center2570‖ ≤
          corrC02700MinusMidpointP010Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP010Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP010Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP010Input2570 17 =
      (corrC02700MinusMidpointP010Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP010Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP010Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP010Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP010Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP010Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP010Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP010DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP010Factor2570 * embedPair2542
          corrC02700MinusMidpointP010Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP010Factor2570 : ℝ) *
            corrC02700MinusMidpointP010Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP010Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP010Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP010BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP010Factor2570)

def corrC02700MinusMidpointP011Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1234978985119947335660559039 : ℚ) /
        1888946593147858085478400000000))

def corrC02700MinusMidpointP011Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP011Factor2570 : RatPair2542 := (((((((((((149155 * 10^40
        + 5484314784179167289328133154870689355880) * 10^40
        + 4524427695010756540762989544453885861608) * 10^40
        + 219370726778775959156332892582392889632) * 10^40
        + 1333560098615298677385217043188814100153) * 10^40
        + 6100316331431309835102499696366603665402) * 10^40
        + 6051134577892834345961460417537846630690) * 10^40
        + 2014994096920802314679869531326827299677) * 10^40
        + 7268997505855382219501709978594881493295) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((21373 * 10^40
        + 2170402061142100222070826907453260305901) * 10^40
        + 584107925711802853916302597100803208869) * 10^40
        + 5932834989597173620020736822445847687127) * 10^40
        + 5804282673382319287556768200358773014199)) : ℚ) /
        (((34041203947163191802420424358972339 * 10^40
        + 9294888048692879294643303459611180948987) * 10^40
        + 6875530082684280963378892437135714531189) * 10^40
        + 5664473480416967517785036299530118627328)))

noncomputable def corrC02700MinusMidpointP011Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP011BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP011Center2570‖ ≤
          corrC02700MinusMidpointP011Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP011Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP011Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP011Input2570 17 =
      (corrC02700MinusMidpointP011Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP011Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP011Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP011Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP011Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP011Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP011Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP011DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP011Factor2570 * embedPair2542
          corrC02700MinusMidpointP011Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP011Factor2570 : ℝ) *
            corrC02700MinusMidpointP011Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP011Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP011Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP011BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP011Factor2570)

def corrC02700MinusMidpointP012Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((27158399338384035222570051 : ℚ) /
        37778931862957161709568000000))

def corrC02700MinusMidpointP012Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP012Factor2570 : RatPair2542 := (((((((((((37288 * 10^40
        + 8871078691408813571653137921782299276749) * 10^40
        + 8139374980466032585339859362757579504544) * 10^40
        + 8083512710889539753531212288513153539862) * 10^40
        + 7320477455893760027416162213895109892047) * 10^40
        + 9197423090111036570111308886173399222942) * 10^40
        + 3648778365265355639615730389053633050787) * 10^40
        + 2891855900158004154761790976469930838871) * 10^40
        + 1872693550500214966922152411978591100599) : ℚ) /
        (((((((28970089154308971741659275481 * 10^40
        + 2126388141186887675387783019575529417109) * 10^40
        + 2815782369582723828570563524552178535468) * 10^40
        + 7576069922986826598542239409767833360653) * 10^40
        + 1032666280957574548405046709230653969167) * 10^40
        + 3752066861155993903206563357147767762550) * 10^40
        + 5983390139212567603069159285436341901852) * 10^40
        + 5771043991187785222523129296030737104896)),
    (((-((((11750 * 10^40
        + 4502205657918915384876395382527670500374) * 10^40
        + 4133578315044065626970324880208718314470) * 10^40
        + 3399970888783619761870820697505080761871) * 10^40
        + 3764638111120839279469732160153727362275)) : ℚ) /
        (((17020601973581595901210212179486169 * 10^40
        + 9647444024346439647321651729805590474493) * 10^40
        + 8437765041342140481689446218567857265594) * 10^40
        + 7832236740208483758892518149765059313664)))

noncomputable def corrC02700MinusMidpointP012Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP012BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP012Center2570‖ ≤
          corrC02700MinusMidpointP012Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP012Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP012Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP012Input2570 17 =
      (corrC02700MinusMidpointP012Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP012Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP012Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP012Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP012Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP012Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP012Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP012DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP012Factor2570 * embedPair2542
          corrC02700MinusMidpointP012Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP012Factor2570 : ℝ) *
            corrC02700MinusMidpointP012Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP012Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP012Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP012BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP012Factor2570)

def corrC02700MinusMidpointP013Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((293990861666597709724015149 : ℚ) /
        377789318629571617095680000000))

def corrC02700MinusMidpointP013Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP013Factor2570 : RatPair2542 := (((((((((((149155 * 10^40
        + 5484314747205040428040429283475149198475) * 10^40
        + 2451146637936778258109100975550672792678) * 10^40
        + 2693780268261011283327301701683389168343) * 10^40
        + 1463625398694083566090973153535224675265) * 10^40
        + 8914018816254621694885371984294552393758) * 10^40
        + 7045440200889349682854204124038269886962) * 10^40
        + 635268386521244725995536926590934703783) * 10^40
        + 805078400999538778955244213156974437871) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((25439 * 10^40
        + 8276000911738366360744325306974639173163) * 10^40
        + 1124608579982435969141070773664172344931) * 10^40
        + 2948467275346882549730679549932068975797) * 10^40
        + 8241465685048324256558000206247926893545)) : ℚ) /
        (((34041203947163191802420424358972339 * 10^40
        + 9294888048692879294643303459611180948987) * 10^40
        + 6875530082684280963378892437135714531189) * 10^40
        + 5664473480416967517785036299530118627328)))

noncomputable def corrC02700MinusMidpointP013Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP013BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP013Center2570‖ ≤
          corrC02700MinusMidpointP013Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP013Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP013Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP013Input2570 17 =
      (corrC02700MinusMidpointP013Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP013Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP013Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP013Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP013Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP013Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP013Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP013DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP013Factor2570 * embedPair2542
          corrC02700MinusMidpointP013Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP013Factor2570 : ℝ) *
            corrC02700MinusMidpointP013Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP013Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP013Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP013BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP013Factor2570)

def corrC02700MinusMidpointP014Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1677542468568059149194008229 : ℚ) /
        1888946593147858085478400000000))

def corrC02700MinusMidpointP014Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP014Factor2570 : RatPair2542 := (((((((((((149155 * 10^40
        + 5484314709195992968846982563002403231597) * 10^40
        + 517815767462440751664983796282235882865) * 10^40
        + 4889411760225453906466381548495774046293) * 10^40
        + 8937031699080902870781063048068275697026) * 10^40
        + 2368150820368523406634837742707372433336) * 10^40
        + 5259597863876643978104015361706447576607) * 10^40
        + 1419219732383516325698922215156903594287) * 10^40
        + 786231859536197778243338374348670818775) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((29032 * 10^40
        + 4610433641550573821166785115980498600968) * 10^40
        + 7840831480227799494123258572747545096219) * 10^40
        + 3654118326271782013759907939432414113140) * 10^40
        + 8794634247341859457514785705032686486989)) : ℚ) /
        (((34041203947163191802420424358972339 * 10^40
        + 9294888048692879294643303459611180948987) * 10^40
        + 6875530082684280963378892437135714531189) * 10^40
        + 5664473480416967517785036299530118627328)))

noncomputable def corrC02700MinusMidpointP014Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP014BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP014Center2570‖ ≤
          corrC02700MinusMidpointP014Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP014Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP014Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP014Input2570 17 =
      (corrC02700MinusMidpointP014Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP014Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP014Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP014Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP014Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP014Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP014Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP014DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP014Factor2570 * embedPair2542
          corrC02700MinusMidpointP014Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP014Factor2570 : ℝ) *
            corrC02700MinusMidpointP014Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP014Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP014Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP014BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP014Factor2570)

def corrC02700MinusMidpointP015Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1826280091905607810113908433 : ℚ) /
        1888946593147858085478400000000))

def corrC02700MinusMidpointP015Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP015Factor2570 : RatPair2542 := (((((((((((149155 * 10^40
        + 5484314678879284030670297492268494311209) * 10^40
        + 1440278290773464289678273814556833672100) * 10^40
        + 9601334987492196255874421251388136349865) * 10^40
        + 1113993789697444134479936944916389548714) * 10^40
        + 9743849209653841511013622476834854406762) * 10^40
        + 7819123737446488223215390614987907881096) * 10^40
        + 1905014676926492177645303804972666769345) * 10^40
        + 3413155508342796315253615951728528892687) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((31606 * 10^40
        + 5951330459265439202827681057857206277909) * 10^40
        + 938593830987372336121114284584848076803) * 10^40
        + 5297106771563968675441174251208375061773) * 10^40
        + 1762916430280697851966249491321585284953)) : ℚ) /
        (((34041203947163191802420424358972339 * 10^40
        + 9294888048692879294643303459611180948987) * 10^40
        + 6875530082684280963378892437135714531189) * 10^40
        + 5664473480416967517785036299530118627328)))

noncomputable def corrC02700MinusMidpointP015Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP015BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP015Center2570‖ ≤
          corrC02700MinusMidpointP015Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP015Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP015Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP015Input2570 17 =
      (corrC02700MinusMidpointP015Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP015Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP015Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP015Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP015Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP015Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP015Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP015DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP015Factor2570 * embedPair2542
          corrC02700MinusMidpointP015Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP015Factor2570 : ℝ) *
            corrC02700MinusMidpointP015Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP015Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP015Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP015BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP015Factor2570)

def corrC02700MinusMidpointP016Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((966884756949258260679651951 : ℚ) /
        944473296573929042739200000000))

def corrC02700MinusMidpointP016Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP016Factor2570 : RatPair2542 := (((((((((((37288 * 10^40
        + 8871078663841972038877365968172235710754) * 10^40
        + 9748101061391324616937592046670444042935) * 10^40
        + 933794326460921465524964752292117640368) * 10^40
        + 791530227116028382696887878445166114167) * 10^40
        + 1457951503377299050040176054661265092574) * 10^40
        + 2054133131098527422599004498703861732859) * 10^40
        + 7670005678784816168140284250095453148248) * 10^40
        + 2014389009873114962551327317456198739343) : ℚ) /
        (((((((28970089154308971741659275481 * 10^40
        + 2126388141186887675387783019575529417109) * 10^40
        + 2815782369582723828570563524552178535468) * 10^40
        + 7576069922986826598542239409767833360653) * 10^40
        + 1032666280957574548405046709230653969167) * 10^40
        + 3752066861155993903206563357147767762550) * 10^40
        + 5983390139212567603069159285436341901852) * 10^40
        + 5771043991187785222523129296030737104896)),
    (((-((((16733 * 10^40
        + 4327240688254210843457562130284880724340) * 10^40
        + 688207340626961383979053128732145585825) * 10^40
        + 2682449637156749903894524814031975238584) * 10^40
        + 9707407153827047727797000096938526012391)) : ℚ) /
        (((17020601973581595901210212179486169 * 10^40
        + 9647444024346439647321651729805590474493) * 10^40
        + 8437765041342140481689446218567857265594) * 10^40
        + 7832236740208483758892518149765059313664)))

noncomputable def corrC02700MinusMidpointP016Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP016BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP016Center2570‖ ≤
          corrC02700MinusMidpointP016Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP016Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP016Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP016Input2570 17 =
      (corrC02700MinusMidpointP016Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP016Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP016Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP016Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP016Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP016Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP016Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP016DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP016Factor2570 * embedPair2542
          corrC02700MinusMidpointP016Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP016Factor2570 : ℝ) *
            corrC02700MinusMidpointP016Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP016Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP016Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP016BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP016Factor2570)

def corrC02700MinusMidpointP017Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2142560996036405154016564653 : ℚ) /
        1888946593147858085478400000000))

def corrC02700MinusMidpointP017Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP017Factor2570 : RatPair2542 := (((((((((((149155 * 10^40
        + 5484314605856935979421101845667608116590) * 10^40
        + 414940699266642346639057264250746385218) * 10^40
        + 2527454544703227961766008000587349991938) * 10^40
        + 3039608368042091052430752881469781520719) * 10^40
        + 6211613605571952532697132662639277640255) * 10^40
        + 7460449203295925910542126040042542480504) * 10^40
        + 4733408533169861652931559508588632791550) * 10^40
        + 341694330782246237097594432043673476167) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((5297 * 10^40
        + 1891762559128275392317591610233893001808) * 10^40
        + 4071563391165315854276793508856308754468) * 10^40
        + 687715490361014171022646599419801578676) * 10^40
        + 1565695392456923070494978688234028731139)) : ℚ) /
        (((4863029135309027400345774908424619 * 10^40
        + 9899269721241839899234757637087311564141) * 10^40
        + 982218583240611566196984633876530647312) * 10^40
        + 7952067640059566788255005185647159803904)))

noncomputable def corrC02700MinusMidpointP017Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP017BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP017Center2570‖ ≤
          corrC02700MinusMidpointP017Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP017Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP017Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP017Input2570 17 =
      (corrC02700MinusMidpointP017Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP017Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP017Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP017Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP017Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP017Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP017Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP017DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP017Factor2570 * embedPair2542
          corrC02700MinusMidpointP017Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP017Factor2570 : ℝ) *
            corrC02700MinusMidpointP017Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP017Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP017Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP017BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP017Factor2570)

def corrC02700MinusMidpointP018Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((555375153147096446436377307 : ℚ) /
        472236648286964521369600000000))

def corrC02700MinusMidpointP018Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP018Factor2570 : RatPair2542 := (((((((((((9322 * 10^40
        + 2217769661613537502452424372010526735210) * 10^40
        + 7609329683139093614902927889229887629217) * 10^40
        + 9262583227696048121424776779642043369297) * 10^40
        + 2371823987046871168420345564741683765157) * 10^40
        + 2687894125386633292367699985459104050406) * 10^40
        + 6010269678049719773587532329113803157114) * 10^40
        + 9644859296249807073044975037179703591507) * 10^40
        + 8383352239495650660884396036792281475287) : ℚ) /
        (((((((7242522288577242935414818870 * 10^40
        + 3031597035296721918846945754893882354277) * 10^40
        + 3203945592395680957142640881138044633867) * 10^40
        + 1894017480746706649635559852441958340163) * 10^40
        + 2758166570239393637101261677307663492291) * 10^40
        + 8438016715288998475801640839286941940637) * 10^40
        + 6495847534803141900767289821359085475463) * 10^40
        + 1442760997796946305630782324007684276224)),
    (((-((((9611 * 10^40
        + 6240275924317958929309251854906530161492) * 10^40
        + 3501900319538834569781941279221680800815) * 10^40
        + 8785439781713329128824098250014465010316) * 10^40
        + 1321585791335460137112157434199606206387)) : ℚ) /
        (((8510300986790797950605106089743084 * 10^40
        + 9823722012173219823660825864902795237246) * 10^40
        + 9218882520671070240844723109283928632797) * 10^40
        + 3916118370104241879446259074882529656832)))

noncomputable def corrC02700MinusMidpointP018Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP018BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP018Center2570‖ ≤
          corrC02700MinusMidpointP018Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP018Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP018Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP018Input2570 17 =
      (corrC02700MinusMidpointP018Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP018Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP018Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP018Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP018Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP018Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP018Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP018DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP018Factor2570 * embedPair2542
          corrC02700MinusMidpointP018Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP018Factor2570 : ℝ) *
            corrC02700MinusMidpointP018Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP018Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP018Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP018BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP018Factor2570)

def corrC02700MinusMidpointP019Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((118208299174604243670929049 : ℚ) /
        94447329657392904273920000000))

def corrC02700MinusMidpointP019Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP019Factor2570 : RatPair2542 := (((((((((((9322 * 10^40
        + 2217769659234944291566494083969898384143) * 10^40
        + 5854428031625628726318566184202459588293) * 10^40
        + 322820456282784118863083249387984123739) * 10^40
        + 7206052223737495128540025050269665125364) * 10^40
        + 2274025122849824072105345736286367279174) * 10^40
        + 991710946911368971370524824832500375762) * 10^40
        + 9377816767292187221407030351905990748392) * 10^40
        + 1691551975483351598625845530675078197031) : ℚ) /
        (((((((7242522288577242935414818870 * 10^40
        + 3031597035296721918846945754893882354277) * 10^40
        + 3203945592395680957142640881138044633867) * 10^40
        + 1894017480746706649635559852441958340163) * 10^40
        + 2758166570239393637101261677307663492291) * 10^40
        + 8438016715288998475801640839286941940637) * 10^40
        + 6495847534803141900767289821359085475463) * 10^40
        + 1442760997796946305630782324007684276224)),
    (((-((((329 * 10^40
        + 9640363028902018082327651546479960786500) * 10^40
        + 5201008080876562545357179107434164537008) * 10^40
        + 2390413001562095855096339475046793921616) * 10^40
        + 6451450299128238063110457947113684227195)) : ℚ) /
        (((274525838283574127438874389991712 * 10^40
        + 4187862000392684510440671802093638556040) * 10^40
        + 2232867178086163556156281390622062213961) * 10^40
        + 2061810270003362641272459970157500956672)))

noncomputable def corrC02700MinusMidpointP019Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP019BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP019Center2570‖ ≤
          corrC02700MinusMidpointP019Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP019Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP019Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP019Input2570 17 =
      (corrC02700MinusMidpointP019Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP019Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP019Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP019Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP019Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP019Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP019Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP019DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP019Factor2570 * embedPair2542
          corrC02700MinusMidpointP019Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP019Factor2570 : ℝ) *
            corrC02700MinusMidpointP019Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP019Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP019Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP019BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP019Factor2570)

def corrC02700MinusMidpointP020Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2519303167856168777929316541 : ℚ) /
        1888946593147858085478400000000))

def corrC02700MinusMidpointP020Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP020Factor2570 : RatPair2542 := (((((((((((149155 * 10^40
        + 5484314503687036996998673180089621509171) * 10^40
        + 4271543227008271849406873769533047988561) * 10^40
        + 6525639679370655618830766102784172643685) * 10^40
        + 4608527231945125516112962659328689406908) * 10^40
        + 5694940419208004729126799922559265506978) * 10^40
        + 9126795006953691370856522603605295117820) * 10^40
        + 4516148031834048311620389980428820482734) * 10^40
        + 6873626556060118476921564069511558055335) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((6228 * 10^40
        + 6326957144775913725461090502256959886912) * 10^40
        + 6756654280959351773984887982953109723255) * 10^40
        + 7359411907697041628173618361838922577758) * 10^40
        + 1666566978245488118999501853723994468083)) : ℚ) /
        (((4863029135309027400345774908424619 * 10^40
        + 9899269721241839899234757637087311564141) * 10^40
        + 982218583240611566196984633876530647312) * 10^40
        + 7952067640059566788255005185647159803904)))

noncomputable def corrC02700MinusMidpointP020Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP020BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP020Center2570‖ ≤
          corrC02700MinusMidpointP020Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP020Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP020Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP020Input2570 17 =
      (corrC02700MinusMidpointP020Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP020Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP020Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP020Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP020Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP020Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP020Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP020DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP020Factor2570 * embedPair2542
          corrC02700MinusMidpointP020Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP020Factor2570 : ℝ) *
            corrC02700MinusMidpointP020Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP020Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP020Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP020BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP020Factor2570)

def corrC02700MinusMidpointP021Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2648771212589104536068841693 : ℚ) /
        1888946593147858085478400000000))

def corrC02700MinusMidpointP021Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP021Factor2570 : RatPair2542 := (((((((((((149155 * 10^40
        + 5484314464763665021029924452924530384853) * 10^40
        + 6665491717635056413830609228910070029143) * 10^40
        + 2851868383082119088620866646254689963004) * 10^40
        + 5649108536476542173280363592236610278105) * 10^40
        + 7000441902409248098327231282740921927914) * 10^40
        + 1152091315168495912420842546622592852648) * 10^40
        + 3616208595777949428870110677274983066920) * 10^40
        + 4996354572741600567831965378947438657127) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((1478 * 10^40
        + 7442957077432317986033490262473247915569) * 10^40
        + 7455584646107210412673600597128623414292) * 10^40
        + 5430715865416056365025227538071751857272) * 10^40
        + 17398639265440371918668066666194624923)) : ℚ) /
        (((1098103353134296509755497559966849 * 10^40
        + 6751448001570738041762687208374554224160) * 10^40
        + 8931468712344654224625125562488248855844) * 10^40
        + 8247241080013450565089839880630003826688)))

noncomputable def corrC02700MinusMidpointP021Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP021BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP021Center2570‖ ≤
          corrC02700MinusMidpointP021Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP021Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP021Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP021Input2570 17 =
      (corrC02700MinusMidpointP021Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP021Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP021Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP021Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP021Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP021Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP021Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP021DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP021Factor2570 * embedPair2542
          corrC02700MinusMidpointP021Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP021Factor2570 : ℝ) *
            corrC02700MinusMidpointP021Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP021Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP021Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP021BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP021Factor2570)

def corrC02700MinusMidpointP022Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((543007546456794340281131487 : ℚ) /
        377789318629571617095680000000))

def corrC02700MinusMidpointP022Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP022Factor2570 : RatPair2542 := (((((((((((149155 * 10^40
        + 5484314444086710418148831806617050124233) * 10^40
        + 4988960703500317597282712924564679369592) * 10^40
        + 9882162654088004407602549074192853498695) * 10^40
        + 4911686560900429701535912887816175788457) * 10^40
        + 8718286974207142509999513702835003985425) * 10^40
        + 1763159114380889256573394759524738868847) * 10^40
        + 1311890189993620979395988089319095014158) * 10^40
        + 5116115517726025103935732918569949747671) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((46987 * 10^40
        + 9175464821973685591200355959108401975897) * 10^40
        + 2773134132162410347355123075610869517891) * 10^40
        + 7064874995182650483380035228712203690901) * 10^40
        + 1247650902159752734639881101253295798835)) : ℚ) /
        (((34041203947163191802420424358972339 * 10^40
        + 9294888048692879294643303459611180948987) * 10^40
        + 6875530082684280963378892437135714531189) * 10^40
        + 5664473480416967517785036299530118627328)))

noncomputable def corrC02700MinusMidpointP022Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP022BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP022Center2570‖ ≤
          corrC02700MinusMidpointP022Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP022Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP022Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP022Input2570 17 =
      (corrC02700MinusMidpointP022Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP022Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP022Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP022Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP022Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP022Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP022Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP022DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP022Factor2570 * embedPair2542
          corrC02700MinusMidpointP022Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP022Factor2570 : ℝ) *
            corrC02700MinusMidpointP022Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP022Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP022Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP022BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP022Factor2570)

def corrC02700MinusMidpointP023Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1453048211174897778209007387 : ℚ) /
        944473296573929042739200000000))

def corrC02700MinusMidpointP023Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP023Factor2570 : RatPair2542 := (((((((((((37288 * 10^40
        + 8871078595402798377030161815267491862519) * 10^40
        + 1503179105617766134587371639844268316794) * 10^40
        + 4774353873439066130129002733436890875363) * 10^40
        + 7301168735484048671219979456329983217744) * 10^40
        + 1404043328112998292689470458944822169137) * 10^40
        + 6452641385978616888056830863780853395284) * 10^40
        + 6672163555473112569846992558632206797499) * 10^40
        + 9977004240026803518724898297266918677335) : ℚ) /
        (((((((28970089154308971741659275481 * 10^40
        + 2126388141186887675387783019575529417109) * 10^40
        + 2815782369582723828570563524552178535468) * 10^40
        + 7576069922986826598542239409767833360653) * 10^40
        + 1032666280957574548405046709230653969167) * 10^40
        + 3752066861155993903206563357147767762550) * 10^40
        + 5983390139212567603069159285436341901852) * 10^40
        + 5771043991187785222523129296030737104896)),
    (((-((((25147 * 10^40
        + 2415008810800779756338670670468107148225) * 10^40
        + 7948563200921199590412731197973089127210) * 10^40
        + 7872528931018474297834336589696705351130) * 10^40
        + 2343504174756501431309580738450644231667)) : ℚ) /
        (((17020601973581595901210212179486169 * 10^40
        + 9647444024346439647321651729805590474493) * 10^40
        + 8437765041342140481689446218567857265594) * 10^40
        + 7832236740208483758892518149765059313664)))

noncomputable def corrC02700MinusMidpointP023Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP023BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP023Center2570‖ ≤
          corrC02700MinusMidpointP023Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP023Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP023Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP023Input2570 17 =
      (corrC02700MinusMidpointP023Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP023Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP023Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP023Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP023Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP023Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP023Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP023DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP023Factor2570 * embedPair2542
          corrC02700MinusMidpointP023Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP023Factor2570 : ℝ) *
            corrC02700MinusMidpointP023Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP023Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP023Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP023BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP023Factor2570)

def corrC02700MinusMidpointP024Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1496949629611413064555803333 : ℚ) /
        944473296573929042739200000000))

def corrC02700MinusMidpointP024Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP024Factor2570 : RatPair2542 := (((((((((((37288 * 10^40
        + 8871078587868906859898750216112093549808) * 10^40
        + 4869593913892634766453328021037023197640) * 10^40
        + 5980783361983481926497961128301340780426) * 10^40
        + 75433072545477558592145676855470018713) * 10^40
        + 9991111607121225809611763769755253002364) * 10^40
        + 7694801285272617926880842184838047020593) * 10^40
        + 7553044929909064172235870006783683369654) * 10^40
        + 9141853204629878675500891483581064638615) : ℚ) /
        (((((((28970089154308971741659275481 * 10^40
        + 2126388141186887675387783019575529417109) * 10^40
        + 2815782369582723828570563524552178535468) * 10^40
        + 7576069922986826598542239409767833360653) * 10^40
        + 1032666280957574548405046709230653969167) * 10^40
        + 3752066861155993903206563357147767762550) * 10^40
        + 5983390139212567603069159285436341901852) * 10^40
        + 5771043991187785222523129296030737104896)),
    (((-((((25907 * 10^40
        + 232914395757604643644102295489655951632) * 10^40
        + 9029312193682980295095410071983218313596) * 10^40
        + 4813008673053868871054369830015667286404) * 10^40
        + 9655147297683468373689767711468690735853)) : ℚ) /
        (((17020601973581595901210212179486169 * 10^40
        + 9647444024346439647321651729805590474493) * 10^40
        + 8437765041342140481689446218567857265594) * 10^40
        + 7832236740208483758892518149765059313664)))

noncomputable def corrC02700MinusMidpointP024Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP024BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP024Center2570‖ ≤
          corrC02700MinusMidpointP024Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP024Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP024Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP024Input2570 17 =
      (corrC02700MinusMidpointP024Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP024Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP024Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP024Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP024Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP024Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP024Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP024DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP024Factor2570 * embedPair2542
          corrC02700MinusMidpointP024Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP024Factor2570 : ℝ) *
            corrC02700MinusMidpointP024Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP024Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP024Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP024BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP024Factor2570)

def corrC02700MinusMidpointP025Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((48499811018293309025440887 : ℚ) /
        29514790517935282585600000000))

def corrC02700MinusMidpointP025Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP025Factor2570 : RatPair2542 := (((((((((((36 * 10^40
        + 4149288162673931599166445567379640741588) * 10^40
        + 9586441857547365885627607936481463874000) * 10^40
        + 6676044773207701801377351169016775254813) * 10^40
        + 2790857137815673955938811600897871509329) * 10^40
        + 4257246964124812596528675414718232079633) * 10^40
        + 2221238077491959752810594623278441669669) * 10^40
        + 8649891251333345786787368531310110378824) * 10^40
        + 8220632587128558082702256644302356456287) : ℚ) /
        (((((((28291102689754855216464136 * 10^40
        + 2121217175919127819995495881855054227946) * 10^40
        + 3957827912470295628738838440941945486851) * 10^40
        + 437086005784166822850138905673601399766) * 10^40
        + 2627961588164997631394926803426983060516) * 10^40
        + 7650148502794097650296100159528464616955) * 10^40
        + 6158186904432824773049872225864683927638) * 10^40
        + 5279073285147644321506370243453155016704)),
    (((-((((17 * 10^40
        + 1298789793970779149015818689253653991100) * 10^40
        + 241975019288383302405478574073727193704) * 10^40
        + 2371510186047925418275492564906669024616) * 10^40
        + 3439568142483656200634668715786656293983)) : ℚ) /
        (((10854975748457650447200390420590 * 10^40
        + 6696203727056343392632220441154212749027) * 10^40
        + 1006656737909019222245975412129188684480) * 10^40
        + 6089178722410847247295212065146533838848)))

noncomputable def corrC02700MinusMidpointP025Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP025BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP025Center2570‖ ≤
          corrC02700MinusMidpointP025Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP025Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP025Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP025Input2570 17 =
      (corrC02700MinusMidpointP025Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP025Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP025Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP025Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP025Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP025Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP025Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP025DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP025Factor2570 * embedPair2542
          corrC02700MinusMidpointP025Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP025Factor2570 : ℝ) *
            corrC02700MinusMidpointP025Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP025Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP025Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP025BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP025Factor2570)

def corrC02700MinusMidpointP026Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((100515438378930241589387643 : ℚ) /
        59029581035870565171200000000))

def corrC02700MinusMidpointP026Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP026Factor2570 : RatPair2542 := (((((((((((145 * 10^40
        + 6597152650655329732080372688188782275925) * 10^40
        + 4766676189987547041725187879859487817782) * 10^40
        + 7738394372406770271247220012660207619240) * 10^40
        + 517198069612470802712843860375701138152) * 10^40
        + 521341649138120340887272706755420937101) * 10^40
        + 5764241178378717694686761648281905578579) * 10^40
        + 4782054653839365911054666824424795678172) * 10^40
        + 8042825580056343731030859522324062163735) : ℚ) /
        (((((((113164410759019420865856544 * 10^40
        + 8484868703676511279981983527420216911785) * 10^40
        + 5831311649881182514955353763767781947404) * 10^40
        + 1748344023136667291400555622694405599065) * 10^40
        + 511846352659990525579707213707932242067) * 10^40
        + 600594011176390601184400638113858467822) * 10^40
        + 4632747617731299092199488903458735710554) * 10^40
        + 1116293140590577286025480973812620066816)),
    (((-((((1739 * 10^40
        + 5747670602525420259768900716632158954946) * 10^40
        + 6023370534495176374583837455474331484273) * 10^40
        + 9108674126351653770239198915859182257278) * 10^40
        + 3005583168960562248656234762501506036563)) : ℚ) /
        (((1063787623348849743825638261217885 * 10^40
        + 6227965251521652477957603233112849404655) * 10^40
        + 8652360315083883780105590388660491079099) * 10^40
        + 6739514796263030234930782384360316207104)))

noncomputable def corrC02700MinusMidpointP026Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP026BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP026Center2570‖ ≤
          corrC02700MinusMidpointP026Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP026Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP026Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP026Input2570 17 =
      (corrC02700MinusMidpointP026Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP026Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP026Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP026Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP026Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP026Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP026Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP026DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP026Factor2570 * embedPair2542
          corrC02700MinusMidpointP026Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP026Factor2570 : ℝ) *
            corrC02700MinusMidpointP026Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP026Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP026Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP026BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP026Factor2570)

def corrC02700MinusMidpointP027Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((211177751933296260595876053 : ℚ) /
        118059162071741130342400000000))

def corrC02700MinusMidpointP027Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP027Factor2570 : RatPair2542 := (((((((((((582 * 10^40
        + 6388610602378004138451091118256579013162) * 10^40
        + 154829694181675135028270897303571238204) * 10^40
        + 4830207545592054165468734987859994954017) * 10^40
        + 9497801516436640323015716558904964691708) * 10^40
        + 624147810769259252684860353305133531333) * 10^40
        + 8664435644174024396993252444407288212572) * 10^40
        + 5485720182249567145926759087810610899180) * 10^40
        + 8735619915852635723852839628207972157687) : ℚ) /
        (((((((452657643036077683463426179 * 10^40
        + 3939474814706045119927934109680867647142) * 10^40
        + 3325246599524730059821415055071127789616) * 10^40
        + 6993376092546669165602222490777622396260) * 10^40
        + 2047385410639962102318828854831728968268) * 10^40
        + 2402376044705562404737602552455433871289) * 10^40
        + 8530990470925196368797955613834942842216) * 10^40
        + 4465172562362309144101923895250480267264)),
    (((-((((3654 * 10^40
        + 7568667290067022466608030249643794453013) * 10^40
        + 3615518646235859005872189444400566979867) * 10^40
        + 6816558937416249754083171701647420514480) * 10^40
        + 7681031926352516562330401269540140245373)) : ℚ) /
        (((2127575246697699487651276522435771 * 10^40
        + 2455930503043304955915206466225698809311) * 10^40
        + 7304720630167767560211180777320982158199) * 10^40
        + 3479029592526060469861564768720632414208)))

noncomputable def corrC02700MinusMidpointP027Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP027BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP027Center2570‖ ≤
          corrC02700MinusMidpointP027Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP027Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP027Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP027Input2570 17 =
      (corrC02700MinusMidpointP027Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP027Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP027Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP027Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP027Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP027Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP027Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP027DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP027Factor2570 * embedPair2542
          corrC02700MinusMidpointP027Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP027Factor2570 : ℝ) *
            corrC02700MinusMidpointP027Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP027Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP027Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP027BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP027Factor2570)

def corrC02700MinusMidpointP028Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((860780157665754287223049953 : ℚ) /
        472236648286964521369600000000))

def corrC02700MinusMidpointP028Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP028Factor2570 : RatPair2542 := (((((((((((9322 * 10^40
        + 2217769636453797628373980281614845808598) * 10^40
        + 3885265053491135945796794503554348088196) * 10^40
        + 6490556847715094944216213683525365717135) * 10^40
        + 7758481127494339019132938862179916471417) * 10^40
        + 6097318184574256896749708970684999018633) * 10^40
        + 5955789412310925816424272973785024317536) * 10^40
        + 7698232907503231546651497734154702285378) * 10^40
        + 4397323095306551726307422550875888684527) : ℚ) /
        (((((((7242522288577242935414818870 * 10^40
        + 3031597035296721918846945754893882354277) * 10^40
        + 3203945592395680957142640881138044633867) * 10^40
        + 1894017480746706649635559852441958340163) * 10^40
        + 2758166570239393637101261677307663492291) * 10^40
        + 8438016715288998475801640839286941940637) * 10^40
        + 6495847534803141900767289821359085475463) * 10^40
        + 1442760997796946305630782324007684276224)),
    (((-((((14897 * 10^40
        + 1289028907113406752954325087855376412451) * 10^40
        + 2744105071689247118487402137594614325828) * 10^40
        + 3283082827570872030846438638156625383765) * 10^40
        + 9377658405563922977327651541683911735273)) : ℚ) /
        (((8510300986790797950605106089743084 * 10^40
        + 9823722012173219823660825864902795237246) * 10^40
        + 9218882520671070240844723109283928632797) * 10^40
        + 3916118370104241879446259074882529656832)))

noncomputable def corrC02700MinusMidpointP028Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP028BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP028Center2570‖ ≤
          corrC02700MinusMidpointP028Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP028Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP028Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP028Input2570 17 =
      (corrC02700MinusMidpointP028Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP028Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP028Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP028Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP028Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP028Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP028Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP028DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP028Factor2570 * embedPair2542
          corrC02700MinusMidpointP028Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP028Factor2570 : ℝ) *
            corrC02700MinusMidpointP028Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP028Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP028Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP028BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP028Factor2570)

def corrC02700MinusMidpointP029Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((885244406725664293840781901 : ℚ) /
        472236648286964521369600000000))

def corrC02700MinusMidpointP029Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02700MinusMidpointP029Factor2570 : RatPair2542 := (((((((((((9322 * 10^40
        + 2217769633968940914346366310158677812193) * 10^40
        + 279577580165557267238270442655335494263) * 10^40
        + 6337030138823518159946648651489327669452) * 10^40
        + 5941046679950527672881970028923341410499) * 10^40
        + 9611175856299633007327032456753085195687) * 10^40
        + 7424826556697583778971647999769762655972) * 10^40
        + 344656107259630741156683152779416576044) * 10^40
        + 2294628423380571109688879797211722912775) : ℚ) /
        (((((((7242522288577242935414818870 * 10^40
        + 3031597035296721918846945754893882354277) * 10^40
        + 3203945592395680957142640881138044633867) * 10^40
        + 1894017480746706649635559852441958340163) * 10^40
        + 2758166570239393637101261677307663492291) * 10^40
        + 8438016715288998475801640839286941940637) * 10^40
        + 6495847534803141900767289821359085475463) * 10^40
        + 1442760997796946305630782324007684276224)),
    (((-((((15320 * 10^40
        + 5204837865840519083688685106481627531880) * 10^40
        + 7466748772482076136494106769764581462) * 10^40
        + 2208655396500243057618484292592132035333) * 10^40
        + 6814452295567614280761319688709064220341)) : ℚ) /
        (((8510300986790797950605106089743084 * 10^40
        + 9823722012173219823660825864902795237246) * 10^40
        + 9218882520671070240844723109283928632797) * 10^40
        + 3916118370104241879446259074882529656832)))

noncomputable def corrC02700MinusMidpointP029Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02700MinusMidpointP029BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP029Center2570‖ ≤
          corrC02700MinusMidpointP029Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hz : ‖embedPair2542 corrC02700MinusMidpointP029Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02700MinusMidpointP029Input2570]
  have hs : compactExp2547 corrC02700MinusMidpointP029Input2570 17 =
      (corrC02700MinusMidpointP029Center2570, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02700MinusMidpointP029Input2570 17).2 : ℝ) =
      corrC02700MinusMidpointP029Error2570 :=
      by
    rw [hs]
    norm_num [corrC02700MinusMidpointP029Error2570]
  have h := compactExp_error2547 corrC02700MinusMidpointP029Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      corrC02700MinusMidpointPosition2570 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          corrC02700MinusMidpointP029Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02700MinusMidpointPosition2570, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02700MinusMidpointP029Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02700MinusMidpointP029DerivativeError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP029Factor2570 * embedPair2542
          corrC02700MinusMidpointP029Center2570‖ ≤
        (pairMagnitude2542 corrC02700MinusMidpointP029Factor2570 : ℝ) *
            corrC02700MinusMidpointP029Error2570 := by
  have hx : |corrC02700MinusMidpointPosition2570| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [corrC02700MinusMidpointPosition2570, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) corrC02700MinusMidpointPosition2570 = embedPair2542
          corrC02700MinusMidpointP029Factor2570 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02700MinusMidpointPosition2570, storedWidth, nodeModulation2541, embedPair2542,
      corrC02700MinusMidpointP029Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02700MinusMidpointP029BaseError2570
    (embedPair_magnitude2542 corrC02700MinusMidpointP029Factor2570)

theorem corrC02700MinusMidpointGrid2570 :
    -stripRadius2303 + ((5401 : ℝ) /
        2) * (2 * stripRadius2303 / 10240) =
      corrC02700MinusMidpointPosition2570 := by
  norm_num [stripRadius2303, corrC02700MinusMidpointPosition2570]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP000DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP001DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP002DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP003DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP004DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP005DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP006DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP007DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP008DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP009DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP010DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP011DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP012DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP013DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP014DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP015DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP016DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP017DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP018DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP019DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP020DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP021DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP022DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP023DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP024DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP025DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP026DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP027DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP028DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointP029DerivativeError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusMidpointGrid2570
