import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchC02700PlusMidpointPosition2558 : ℝ := (((-317128708839) : ℝ) /
        102400000000)

theorem batchC02700PlusMidpointZero2558 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchC02700PlusMidpointP000Center2558 : RatPair2542 := (0, 0)

def batchC02700PlusMidpointP000Factor2558 : RatPair2542 := (0, 0)

noncomputable def batchC02700PlusMidpointP000Error2558 : ℝ := 0

theorem batchC02700PlusMidpointP000Exterior2558 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02700PlusMidpointPosition2558 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |batchC02700PlusMidpointPosition2558| := by
    norm_num [storedWidth, batchC02700PlusMidpointPosition2558]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem batchC02700PlusMidpointP000BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP000Center2558‖ ≤ batchC02700PlusMidpointP000Error2558
          := by
  rw [batchC02700PlusMidpointP000Exterior2558]
  norm_num [batchC02700PlusMidpointP000Center2558, batchC02700PlusMidpointP000Error2558,
      batchC02700PlusMidpointZero2558]

theorem batchC02700PlusMidpointP000DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP000Factor2558 * embedPair2542
          batchC02700PlusMidpointP000Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP000Factor2558 : ℝ) *
            batchC02700PlusMidpointP000Error2558 := by
  rw [batchC02700PlusMidpointP000Exterior2558]
  norm_num [batchC02700PlusMidpointP000Factor2558, batchC02700PlusMidpointP000Center2558,
      batchC02700PlusMidpointP000Error2558,
      batchC02700PlusMidpointZero2558, pairMagnitude2542]

def batchC02700PlusMidpointP001Input2558 : RatPair2542 := ((((-((75 * 10^40
        + 5793610062624408994825365663891066264162) * 10^40
        + 9918580294757314292856548188915782259599)) : ℚ) /
        ((208 * 10^40
        + 8043940912794372598641292711490528776820) * 10^40
        + 5100987153752063079186153183641600000000)),
    ((1751911280236833479653958331 : ℚ) /
        7378697629483820646400000000))

def batchC02700PlusMidpointP001Center2558 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP001Factor2558 : RatPair2542 := ((((((((((1136552540511217150243643336
    * 10^40
        + 2349385147195245711882978590493549728072) * 10^40
        + 8557514563813148439801784313125042118641) * 10^40
        + 5505741301441538609916972302169365965172) * 10^40
        + 7910990787390285490284845098180436171767) * 10^40
        + 712314953091495794964195483812693353485) * 10^40
        + 816852657255150933336347957313361350912) * 10^40
        + 9864868262070096640789739530530616564855) : ℚ) /
        (((((((3114429284045443776614 * 10^40
        + 9680444835455280460140749335584001093358) * 10^40
        + 1911666244245281745966243066311980061204) * 10^40
        + 528329653512445415592798536726260464355) * 10^40
        + 1801406946283238328514682425762387519584) * 10^40
        + 3490628447045898579670805122056367448802) * 10^40
        + 9889831084762471402572093792358697720904) * 10^40
        + 1848635307526357013279069283978496180224)),
    (((-(((266744175016200646835707941843677921 * 10^40
        + 2872645247674460203995397814188126148393) * 10^40
        + 9537678369083383649689015043003715665515) * 10^40
        + 1213973585473276742026270292629354921149)) : ℚ) /
        (((5580707198953770389983466974217 * 10^40
        + 9009587017588522182642900543038828648160) * 10^40
        + 1385716774918519770136509599163173339651) * 10^40
        + 717525258581434384188834601649116807168)))

noncomputable def batchC02700PlusMidpointP001Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP001BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP001Center2558‖ ≤ batchC02700PlusMidpointP001Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP001Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP001Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP001Input2558 9 =
      (batchC02700PlusMidpointP001Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP001Input2558 9).2 : ℝ) =
      batchC02700PlusMidpointP001Error2558 := by
    rw [hs]
    norm_num [batchC02700PlusMidpointP001Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP001Input2558 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          batchC02700PlusMidpointP001Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP001Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP001DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP001Factor2558 * embedPair2542
          batchC02700PlusMidpointP001Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP001Factor2558 : ℝ) *
            batchC02700PlusMidpointP001Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP001Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP001Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP001BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP001Factor2558)

def batchC02700PlusMidpointP002Input2558 : RatPair2542 := ((((-((2007 * 10^40
        + 5023240729250299860289918989155247824672) * 10^40
        + 8628363056985938976693269865273365762959)) : ℚ) /
        ((8147 * 10^40
        + 6895918656149932623563298325318453465194) * 10^40
        + 9452298146475584633489225469132800000000)),
    (((-1751911280236833479653958331) : ℚ) /
        3689348814741910323200000000))

def batchC02700PlusMidpointP002Center2558 : RatPair2542 := ((((-339364505114828529043) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-241773850067246350091) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC02700PlusMidpointP002Factor2558 : RatPair2542 :=
    ((((((((((20182259225994191485145792903696 * 10^40
        + 6000610344002938397078148481087003853535) * 10^40
        + 593568821820900297836712180218053186409) * 10^40
        + 3790509458493478496988278520557893683634) * 10^40
        + 7007142323839653084831508999226660029967) * 10^40
        + 3111456430359603185772932337820880769580) * 10^40
        + 7116082574497240677929234081004668618728) * 10^40
        + 1919393205724976063559176378504528321655) : ℚ) /
        (((((((115525490748260174715076203586 * 10^40
        + 9841353533651885412466610413671356681188) * 10^40
        + 7642562632268933197074993551067893033088) * 10^40
        + 7944740562176547541096260135886068737629) * 10^40
        + 3285334223738111778445965844867044888674) * 10^40
        + 5575446764899759210915261339522269986558) * 10^40
        + 2997495251739314740075027225728645103699) * 10^40
        + 5374814466683858103126194814725667160064)),
    (((((112753384519665666909875577707506423926 * 10^40
        + 632303668784115475483380445781797812122) * 10^40
        + 7067433010009044399670800077144726486934) * 10^40
        + 2368525336814819841931450498594596142269) : ℚ) /
        (((33989040990922379173162885590005531 * 10^40
        + 7367314092441466677914319666200769647378) * 10^40
        + 7700021938458516116839260266589107341797) * 10^40
        + 6043262579466265220719258022173902635008)))

noncomputable def batchC02700PlusMidpointP002Error2558 : ℝ := ((2191587035296828369 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP002BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP002Center2558‖ ≤ batchC02700PlusMidpointP002Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP002Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP002Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP002Input2558 8 =
      (batchC02700PlusMidpointP002Center2558, ((2191587035296828369 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP002Input2558 8).2 : ℝ) =
      batchC02700PlusMidpointP002Error2558 := by
    rw [hs]
    norm_num [batchC02700PlusMidpointP002Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP002Input2558 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02700PlusMidpointP002Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP002Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP002DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP002Factor2558 * embedPair2542
          batchC02700PlusMidpointP002Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP002Factor2558 : ℝ) *
            batchC02700PlusMidpointP002Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP002Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP002Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP002BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP002Factor2558)

def batchC02700PlusMidpointP003Input2558 : RatPair2542 := ((((-((7224110 * 10^40
        + 4406628376595866370136231705353501324162) * 10^40
        + 1511332573809066646429207955160645591911)) : ℚ) /
        ((39860431 * 10^40
        + 3525369205518296877772896888819194996209) * 10^40
        + 8027785848626107559175480881971200000000)),
    (((-1751911280236833479653958331) : ℚ) /
        3689348814741910323200000000))

def batchC02700PlusMidpointP003Center2558 : RatPair2542 := ((((-5949091438372091633409808421) : ℚ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-132447442184126730267608627) : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)))

def batchC02700PlusMidpointP003Factor2558 : RatPair2542 := ((((-((((((((8831291 * 10^40
        + 7203916942294472264605761218543108638074) * 10^40
        + 9827750071684412767791794668118205761479) * 10^40
        + 6828575789033247244120297418673672680130) * 10^40
        + 8297066710558972008900193113415856686713) * 10^40
        + 810420718893404360307956074769123050209) * 10^40
        + 1216818652947017972044693261529949965887) * 10^40
        + 3163594322212871634250780737209351278820) * 10^40
        + 4669786937560542599225785784716002507945)) : ℚ) /
        ((((((((6617 * 10^40
        + 7125422076468304010688842754536356362659) * 10^40
        + 5386377453594199918208717244286697190680) * 10^40
        + 8071597337658982165835423313409578778727) * 10^40
        + 5691218389018228563362915437783942818555) * 10^40
        + 5492133941841779868889048247305091618183) * 10^40
        + 5000432551886719187743182772291576826294) * 10^40
        + 3387671642793116577989155749696368425591) * 10^40
        + 1234362302035428370555877184122948419584)),
    ((((((94735 * 10^40
        + 8580685375879323895193794218810081241424) * 10^40
        + 1441469566300647578157031367112868399043) * 10^40
        + 1854365736212226642430227005362402391732) * 10^40
        + 6241705344818842807482177269986926614029) : ℚ) /
        ((((81 * 10^40
        + 3493241656477858559825274349299360270924) * 10^40
        + 1698071194914685148847557874921996951747) * 10^40
        + 5087744417512963469373459473366349438543) * 10^40
        + 6929975997517327555611596299530118627328)))

noncomputable def batchC02700PlusMidpointP003Error2558 : ℝ := ((17997678379747832815547905 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC02700PlusMidpointP003BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP003Center2558‖ ≤ batchC02700PlusMidpointP003Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP003Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP003Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP003Input2558 8 =
      (batchC02700PlusMidpointP003Center2558, ((17997678379747832815547905 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP003Input2558 8).2 : ℝ) =
      batchC02700PlusMidpointP003Error2558 := by
    rw [hs]
    norm_num [batchC02700PlusMidpointP003Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP003Input2558 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02700PlusMidpointP003Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP003Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP003DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP003Factor2558 * embedPair2542
          batchC02700PlusMidpointP003Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP003Factor2558 : ℝ) *
            batchC02700PlusMidpointP003Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP003Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP003Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP003BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP003Factor2558)

def batchC02700PlusMidpointP004Input2558 : RatPair2542 := ((((-((4673 * 10^40
        + 4597880448384906672533435637131642652828) * 10^40
        + 431693750250106491058255045937428262959)) : ℚ) /
        ((29780 * 10^40
        + 5895054484312759971766663273404887092534) * 10^40
        + 1331668037402944633489225469132800000000)),
    ((1751911280236833479653958331 : ℚ) /
        3689348814741910323200000000))

def batchC02700PlusMidpointP004Center2558 : RatPair2542 := ((((-1498581575969300851911523103931) :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((4270544877866285909173470095625 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC02700PlusMidpointP004Factor2558 : RatPair2542 :=
    ((((-(((((((30658282981642100343220296354972335 *
    10^40
        + 1633339699242660344157099316939199457454) * 10^40
        + 5263570603013814615427188682817450813333) * 10^40
        + 3023692878586139736685803735959360763348) * 10^40
        + 5299039798442294574276544077083741536646) * 10^40
        + 5570717971923401664773915835180100583613) * 10^40
        + 2600412403600139227956351754220081261086) * 10^40
        + 6896439875678820768830453992589221678345)) : ℚ) /
        (((((((20619260398185266867770268076303 * 10^40
        + 810658110180138412392108416437618619019) * 10^40
        + 986181953701573507156749035082291902121) * 10^40
        + 3051596691796931788383473745700259187266) * 10^40
        + 8089028926060019584365844952163407895982) * 10^40
        + 9107592919862370423145459969197768349176) * 10^40
        + 2345231521801162654220189886828470833514) * 10^40
        + 2599327465781412486793394814725667160064)),
    (((-(((273486215942200655346604947700510194075 * 10^40
        + 1328826389439223636300053501579632619728) * 10^40
        + 6162280337348051751061883594203075211465) * 10^40
        + 7049688552543525959864661582578971142269)) : ℚ) /
        (((454084357781516923150618442898949233 * 10^40
        + 7351628418167286031113461605381744134575) * 10^40
        + 430352166525634131497045575473615820870) * 10^40
        + 4011403570180837345698458022173902635008)))

noncomputable def batchC02700PlusMidpointP004Error2558 : ℝ := ((17699073006843670952439380847 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP004BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP004Center2558‖ ≤ batchC02700PlusMidpointP004Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP004Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP004Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP004Input2558 8 =
      (batchC02700PlusMidpointP004Center2558, ((17699073006843670952439380847 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP004Input2558 8).2 : ℝ) =
      batchC02700PlusMidpointP004Error2558 := by
    rw [hs]
    norm_num [batchC02700PlusMidpointP004Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP004Input2558 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02700PlusMidpointP004Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP004Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP004DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP004Factor2558 * embedPair2542
          batchC02700PlusMidpointP004Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP004Factor2558 : ℝ) *
            batchC02700PlusMidpointP004Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP004Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP004Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP004BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP004Factor2558)

def batchC02700PlusMidpointP005Center2558 : RatPair2542 := (0, 0)

def batchC02700PlusMidpointP005Factor2558 : RatPair2542 := (0, 0)

noncomputable def batchC02700PlusMidpointP005Error2558 : ℝ := 0

theorem batchC02700PlusMidpointP005Exterior2558 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02700PlusMidpointPosition2558 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |batchC02700PlusMidpointPosition2558| := by
    norm_num [storedWidth, batchC02700PlusMidpointPosition2558]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem batchC02700PlusMidpointP005BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP005Center2558‖ ≤ batchC02700PlusMidpointP005Error2558
          := by
  rw [batchC02700PlusMidpointP005Exterior2558]
  norm_num [batchC02700PlusMidpointP005Center2558, batchC02700PlusMidpointP005Error2558,
      batchC02700PlusMidpointZero2558]

theorem batchC02700PlusMidpointP005DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP005Factor2558 * embedPair2542
          batchC02700PlusMidpointP005Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP005Factor2558 : ℝ) *
            batchC02700PlusMidpointP005Error2558 := by
  rw [batchC02700PlusMidpointP005Exterior2558]
  norm_num [batchC02700PlusMidpointP005Factor2558, batchC02700PlusMidpointP005Center2558,
      batchC02700PlusMidpointP005Error2558,
      batchC02700PlusMidpointZero2558, pairMagnitude2542]

def batchC02700PlusMidpointP006Input2558 : RatPair2542 :=
    ((((-1052103689295998182959213518129206281) : ℚ) /
        1761648103394083163919587737600000000),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP006Center2558 : RatPair2542 := (((922862892562499 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP006Factor2558 : RatPair2542 := (((((4200428254427313 * 10^40
        + 6028971700741400348125960267863197178853) * 10^40
        + 1524827169300218795578102645424357382081) : ℚ) /
        ((815787311011 * 10^40
        + 6853265494000320941081736296179322639449) * 10^40
        + 1419175634369515182312410581697429528324)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP006Error2558 : ℝ := ((1217513621385 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC02700PlusMidpointP006BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP006Center2558‖ ≤ batchC02700PlusMidpointP006Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP006Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP006Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP006Input2558 7 =
      (batchC02700PlusMidpointP006Center2558, ((1217513621385 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP006Input2558 7).2 : ℝ) =
      batchC02700PlusMidpointP006Error2558 := by
    rw [hs]
    norm_num [batchC02700PlusMidpointP006Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP006Input2558 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          batchC02700PlusMidpointP006Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP006Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP006DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP006Factor2558 * embedPair2542
          batchC02700PlusMidpointP006Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP006Factor2558 : ℝ) *
            batchC02700PlusMidpointP006Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP006Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP006Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP006BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP006Factor2558)

def batchC02700PlusMidpointP007Input2558 : RatPair2542 := ((((-((7224110 * 10^40
        + 4406628376595866370136231705353501324162) * 10^40
        + 1511332573809066646429207955160645591911)) : ℚ) /
        ((9965107 * 10^40
        + 8381342301379574219443224222204798749052) * 10^40
        + 4506946462156526889793870220492800000000)),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP007Center2558 : RatPair2542 := (((10355918689374196829550765419 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP007Factor2558 : RatPair2542 := ((((((((((2756555388410581397 * 10^40
        + 4937131362417805071759646532586440204977) * 10^40
        + 5483867836145460518299375165416019956483) * 10^40
        + 9953675690188260313643804202635602572684) * 10^40
        + 8641583780569418067951857690519586102322) * 10^40
        + 1592502801474842692785423474596764468679) * 10^40
        + 7870993399651418212843379274725014348780) * 10^40
        + 4483887871814986214583906702064787648001) : ℚ) /
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

noncomputable def batchC02700PlusMidpointP007Error2558 : ℝ := ((1504548178364114737319599 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP007BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP007Center2558‖ ≤ batchC02700PlusMidpointP007Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP007Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP007Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP007Input2558 6 =
      (batchC02700PlusMidpointP007Center2558, ((1504548178364114737319599 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP007Input2558 6).2 : ℝ) =
      batchC02700PlusMidpointP007Error2558 := by
    rw [hs]
    norm_num [batchC02700PlusMidpointP007Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP007Input2558 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          batchC02700PlusMidpointP007Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP007Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP007DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP007Factor2558 * embedPair2542
          batchC02700PlusMidpointP007Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP007Factor2558 : ℝ) *
            batchC02700PlusMidpointP007Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP007Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP007Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP007BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP007Factor2558)

def batchC02700PlusMidpointP008Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1261719220645415482412484183 : ℚ) /
        3777893186295716170956800000000))

def batchC02700PlusMidpointP008Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP008Factor2558 : RatPair2542 := (((((((((((596622 * 10^40
        + 2042436352897714195253302031706360975680) * 10^40
        + 5449953047292391281350800554431516516967) * 10^40
        + 1647698848086381507036065327738379005173) * 10^40
        + 6237263796463090721141318061750278259533) * 10^40
        + 4950161197866368927085373922944733541931) * 10^40
        + 1739237892824820277704776255268923830765) * 10^40
        + 5817523368974330951960771415366783048975) * 10^40
        + 3471671717163817238388571285480029785375) : ℚ) /
        (((((((463521426468943547866548407699 * 10^40
        + 4022210258990202806204528313208470673748) * 10^40
        + 5052517913323581257129016392834856567500) * 10^40
        + 1217118767789225576675830556285333770449) * 10^40
        + 6522660495321192774480747347690463506678) * 10^40
        + 33069778495902451305013714364284200809) * 10^40
        + 5734242227401081649106548566981470429641) * 10^40
        + 2336703859004563560370068736491793678336)),
    (((-((((3119 * 10^40
        + 4283244915193059485553320094667148283104) * 10^40
        + 3802027171461609756151018198220210150536) * 10^40
        + 6104120903534010133115179163175183677072) * 10^40
        + 3541122397168306662562421737038698758471)) : ℚ) /
        (((9726058270618054800691549816849239 * 10^40
        + 9798539442483679798469515274174623128282) * 10^40
        + 1964437166481223132393969267753061294625) * 10^40
        + 5904135280119133576510010371294319607808)))

noncomputable def batchC02700PlusMidpointP008Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP008BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP008Center2558‖ ≤ batchC02700PlusMidpointP008Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP008Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP008Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP008Input2558 17 =
      (batchC02700PlusMidpointP008Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP008Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP008Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP008Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP008Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP008Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP008Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP008DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP008Factor2558 * embedPair2542
          batchC02700PlusMidpointP008Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP008Factor2558 : ℝ) *
            batchC02700PlusMidpointP008Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP008Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP008Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP008BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP008Factor2558)

def batchC02700PlusMidpointP009Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1876507056447276098253971529 : ℚ) /
        3777893186295716170956800000000))

def batchC02700PlusMidpointP009Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP009Factor2558 : RatPair2542 := (((((((((((596622 * 10^40
        + 2042436240662631106012434447783960368902) * 10^40
        + 9187458842549664312359560030661571130543) * 10^40
        + 6236871138963173465822967328933656600010) * 10^40
        + 7350503080231832117589232249830728683383) * 10^40
        + 4366798126804619965212645135104760182242) * 10^40
        + 8200538689083471108386881798291072591609) * 10^40
        + 1023943289433810013470427413188041721603) * 10^40
        + 6166064631905431511177316463541014980063) : ℚ) /
        (((((((463521426468943547866548407699 * 10^40
        + 4022210258990202806204528313208470673748) * 10^40
        + 5052517913323581257129016392834856567500) * 10^40
        + 1217118767789225576675830556285333770449) * 10^40
        + 6522660495321192774480747347690463506678) * 10^40
        + 33069778495902451305013714364284200809) * 10^40
        + 5734242227401081649106548566981470429641) * 10^40
        + 2336703859004563560370068736491793678336)),
    (((-((((1047 * 10^40
        + 6080821349832873715075907405389161331356) * 10^40
        + 6820581673166049562637261056100972477884) * 10^40
        + 783099162475089397321722257306948022993) * 10^40
        + 16040826916130414156082045596337519281)) : ℚ) /
        (((2196206706268593019510995119933699 * 10^40
        + 3502896003141476083525374416749108448321) * 10^40
        + 7862937424689308449250251124976497711689) * 10^40
        + 6494482160026901130179679761260007653376)))

noncomputable def batchC02700PlusMidpointP009Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP009BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP009Center2558‖ ≤ batchC02700PlusMidpointP009Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP009Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP009Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP009Input2558 17 =
      (batchC02700PlusMidpointP009Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP009Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP009Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP009Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP009Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP009Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP009Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP009DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP009Factor2558 * embedPair2542
          batchC02700PlusMidpointP009Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP009Factor2558 : ℝ) *
            batchC02700PlusMidpointP009Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP009Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP009Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP009BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP009Factor2558)

def batchC02700PlusMidpointP010Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1116282043593459096767143119 : ℚ) /
        1888946593147858085478400000000))

def batchC02700PlusMidpointP010Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP010Factor2558 : RatPair2542 := (((((((((((149155 * 10^40
        + 5510609038888072143980508939162418153927) * 10^40
        + 1184196890854413305175354715571713866445) * 10^40
        + 5667572887315233274661316311380446777063) * 10^40
        + 6078147919676073839953939555020012457365) * 10^40
        + 6131814302445644474629010727533482041814) * 10^40
        + 396637527518620891867121853493225229239) * 10^40
        + 3043419450817443222256414984891591559774) * 10^40
        + 8149458107354727887839525465247470501455) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((19318 * 10^40
        + 9834754821453229176507594089104050912713) * 10^40
        + 3113736396103164194047080541756212246409) * 10^40
        + 7032688001393239072231813418021893082756) * 10^40
        + 6579072094292122935674906162463607246521)) : ℚ) /
        (((34041203947163191802420424358972339 * 10^40
        + 9294888048692879294643303459611180948987) * 10^40
        + 6875530082684280963378892437135714531189) * 10^40
        + 5664473480416967517785036299530118627328)))

noncomputable def batchC02700PlusMidpointP010Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP010BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP010Center2558‖ ≤ batchC02700PlusMidpointP010Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP010Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP010Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP010Input2558 17 =
      (batchC02700PlusMidpointP010Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP010Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP010Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP010Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP010Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP010Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP010Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP010DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP010Factor2558 * embedPair2542
          batchC02700PlusMidpointP010Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP010Factor2558 : ℝ) *
            batchC02700PlusMidpointP010Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP010Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP010Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP010BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP010Factor2558)

def batchC02700PlusMidpointP011Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1234978985119947335660559039 : ℚ) /
        1888946593147858085478400000000))

def batchC02700PlusMidpointP011Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP011Factor2558 : RatPair2542 := (((((((((((149155 * 10^40
        + 5510609022652803241948855563026445335133) * 10^40
        + 6943352535657300138220410867058245785531) * 10^40
        + 7581258019915776799322053697721061405885) * 10^40
        + 8287403831620311653632790963661844185167) * 10^40
        + 6302351220599797009927140669126309806015) * 10^40
        + 5068855301451916172237331326384461986246) * 10^40
        + 373236563332039538214542923673482759734) * 10^40
        + 7149890469408662219501709978594881493295) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((21373 * 10^40
        + 2172285923286330114715221111815081924933) * 10^40
        + 6021879927599542381161323043771334274640) * 10^40
        + 2124895743371386916846735526282621784283) * 10^40
        + 8097025570749520712443231799641226985801)) : ℚ) /
        (((34041203947163191802420424358972339 * 10^40
        + 9294888048692879294643303459611180948987) * 10^40
        + 6875530082684280963378892437135714531189) * 10^40
        + 5664473480416967517785036299530118627328)))

noncomputable def batchC02700PlusMidpointP011Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP011BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP011Center2558‖ ≤ batchC02700PlusMidpointP011Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP011Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP011Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP011Input2558 17 =
      (batchC02700PlusMidpointP011Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP011Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP011Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP011Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP011Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP011Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP011Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP011DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP011Factor2558 * embedPair2542
          batchC02700PlusMidpointP011Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP011Factor2558 : ℝ) *
            batchC02700PlusMidpointP011Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP011Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP011Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP011BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP011Factor2558)

def batchC02700PlusMidpointP012Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((27158399338384035222570051 : ℚ) /
        37778931862957161709568000000))

def batchC02700PlusMidpointP012Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP012Factor2558 : RatPair2542 := (((((((((((37288 * 10^40
        + 8877652251027222559808318523821238271563) * 10^40
        + 1244106190627668484704214693408669485525) * 10^40
        + 7423984534173789963572642489797820668926) * 10^40
        + 1558938389145013271478055694013367413301) * 10^40
        + 4247931812403158363817469129363325758095) * 10^40
        + 5903208546155126096184698116265286889676) * 10^40
        + 2481416516760813460645459324556594703885) * 10^40
        + 4342916791388534966922152411978591100599) : ℚ) /
        (((((((28970089154308971741659275481 * 10^40
        + 2126388141186887675387783019575529417109) * 10^40
        + 2815782369582723828570563524552178535468) * 10^40
        + 7576069922986826598542239409767833360653) * 10^40
        + 1032666280957574548405046709230653969167) * 10^40
        + 3752066861155993903206563357147767762550) * 10^40
        + 5983390139212567603069159285436341901852) * 10^40
        + 5771043991187785222523129296030737104896)),
    (((-((((11750 * 10^40
        + 4503241357332182944869015648179468358866) * 10^40
        + 8384127266663926682523367327384273841992) * 10^40
        + 1554191412533964889238527359588834899086) * 10^40
        + 3194223135343160720530267839846272637725)) : ℚ) /
        (((17020601973581595901210212179486169 * 10^40
        + 9647444024346439647321651729805590474493) * 10^40
        + 8437765041342140481689446218567857265594) * 10^40
        + 7832236740208483758892518149765059313664)))

noncomputable def batchC02700PlusMidpointP012Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP012BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP012Center2558‖ ≤ batchC02700PlusMidpointP012Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP012Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP012Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP012Input2558 17 =
      (batchC02700PlusMidpointP012Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP012Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP012Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP012Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP012Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP012Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP012Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP012DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP012Factor2558 * embedPair2542
          batchC02700PlusMidpointP012Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP012Factor2558 : ℝ) *
            batchC02700PlusMidpointP012Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP012Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP012Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP012BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP012Factor2558)

def batchC02700PlusMidpointP013Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((293990861666597709724015149 : ℚ) /
        377789318629571617095680000000))

def batchC02700PlusMidpointP013Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP013Factor2558 : RatPair2542 := (((((((((((149155 * 10^40
        + 5510608985678676380661151691630905177728) * 10^40
        + 4870071478583321855566522298155032716602) * 10^40
        + 55667561398012123493022506822057684596) * 10^40
        + 8417469131699096542338547074008254760279) * 10^40
        + 9116053705423108869710012957054258534371) * 10^40
        + 6063160924448431509130075032884885242517) * 10^40
        + 8993510852932481949530210318937590163840) * 10^40
        + 685971364552818778955244213156974437871) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((25439 * 10^40
        + 8278243210035407581125679314651271380970) * 10^40
        + 5574834651322072680514301676137706810379) * 10^40
        + 4832823900036257239335372939649011574405) * 10^40
        + 3002596884218875743441999793752073106455)) : ℚ) /
        (((34041203947163191802420424358972339 * 10^40
        + 9294888048692879294643303459611180948987) * 10^40
        + 6875530082684280963378892437135714531189) * 10^40
        + 5664473480416967517785036299530118627328)))

noncomputable def batchC02700PlusMidpointP013Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP013BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP013Center2558‖ ≤ batchC02700PlusMidpointP013Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP013Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP013Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP013Input2558 17 =
      (batchC02700PlusMidpointP013Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP013Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP013Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP013Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP013Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP013Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP013Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP013DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP013Factor2558 * embedPair2542
          batchC02700PlusMidpointP013Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP013Factor2558 : ℝ) *
            batchC02700PlusMidpointP013Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP013Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP013Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP013BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP013Factor2558)

def batchC02700PlusMidpointP014Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1677542468568059149194008229 : ℚ) /
        1888946593147858085478400000000))

def batchC02700PlusMidpointP014Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP014Factor2558 : RatPair2542 := (((((((((((149155 * 10^40
        + 5510608947669628921467704971158159210850) * 10^40
        + 2936740608108984349122405118886595806789) * 10^40
        + 2251299053362454746632102353634442562547) * 10^40
        + 5890875432085915847028636968541305782040) * 10^40
        + 2570185709537010581459478715467078573949) * 10^40
        + 4277318587435725804379886270553062932162) * 10^40
        + 9777462198794753549233595607503559054344) * 10^40
        + 667124823089477778243338374348670818775) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((29032 * 10^40
        + 4612992599063171811696314193253427992975) * 10^40
        + 6472663831775015408632222826441757953943) * 10^40
        + 7808356809687333342828698042431163579594) * 10^40
        + 4229092883036380542485214294967313513011)) : ℚ) /
        (((34041203947163191802420424358972339 * 10^40
        + 9294888048692879294643303459611180948987) * 10^40
        + 6875530082684280963378892437135714531189) * 10^40
        + 5664473480416967517785036299530118627328)))

noncomputable def batchC02700PlusMidpointP014Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP014BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP014Center2558‖ ≤ batchC02700PlusMidpointP014Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP014Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP014Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP014Input2558 17 =
      (batchC02700PlusMidpointP014Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP014Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP014Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP014Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP014Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP014Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP014Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP014DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP014Factor2558 * embedPair2542
          batchC02700PlusMidpointP014Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP014Factor2558 : ℝ) *
            batchC02700PlusMidpointP014Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP014Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP014Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP014BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP014Factor2558)

def batchC02700PlusMidpointP015Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1826280091905607810113908433 : ℚ) /
        1888946593147858085478400000000))

def batchC02700PlusMidpointP015Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP015Factor2558 : RatPair2542 := (((((((((((149155 * 10^40
        + 5510608917352919983291019900424250290462) * 10^40
        + 3859203131420007887135695137161193596024) * 10^40
        + 6963222280629197096040142056526804866118) * 10^40
        + 8067837522702457110727510865389419633728) * 10^40
        + 9945884098822328685838263449594560547375) * 10^40
        + 6836844461005570049491261523834523236652) * 10^40
        + 263257143337729401179977197319322229402) * 10^40
        + 3294048471896076315253615951728528892687) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((31606 * 10^40
        + 5954116304183737556753925080422876432476) * 10^40
        + 9229220837689589715724025807794861246784) * 10^40
        + 4154846262920318827437420306797818026806) * 10^40
        + 4917775686731782148033750508678414715047)) : ℚ) /
        (((34041203947163191802420424358972339 * 10^40
        + 9294888048692879294643303459611180948987) * 10^40
        + 6875530082684280963378892437135714531189) * 10^40
        + 5664473480416967517785036299530118627328)))

noncomputable def batchC02700PlusMidpointP015Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP015BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP015Center2558‖ ≤ batchC02700PlusMidpointP015Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP015Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP015Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP015Input2558 17 =
      (batchC02700PlusMidpointP015Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP015Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP015Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP015Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP015Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP015Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP015Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP015DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP015Factor2558 * embedPair2542
          batchC02700PlusMidpointP015Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP015Factor2558 : ℝ) *
            batchC02700PlusMidpointP015Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP015Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP015Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP015BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP015Factor2558)

def batchC02700PlusMidpointP016Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((966884756949258260679651951 : ℚ) /
        944473296573929042739200000000))

def batchC02700PlusMidpointP016Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP016Factor2558 : RatPair2542 := (((((((((((37288 * 10^40
        + 8877652223460381027032546570211174705568) * 10^40
        + 2852832271552960516301947377321534023916) * 10^40
        + 274266149745171675566394953576784769431) * 10^40
        + 5029991160367281626758781358563423635420) * 10^40
        + 6508460225669420843746336297851191627727) * 10^40
        + 4308563311988297879167972225915515571748) * 10^40
        + 7259566295387625474023952598182117013262) * 10^40
        + 4484612250761434962551327317456198739343) : ℚ) /
        (((((((28970089154308971741659275481 * 10^40
        + 2126388141186887675387783019575529417109) * 10^40
        + 2815782369582723828570563524552178535468) * 10^40
        + 7576069922986826598542239409767833360653) * 10^40
        + 1032666280957574548405046709230653969167) * 10^40
        + 3752066861155993903206563357147767762550) * 10^40
        + 5983390139212567603069159285436341901852) * 10^40
        + 5771043991187785222523129296030737104896)),
    (((-((((16733 * 10^40
        + 4328715593992200156082303598206149006219) * 10^40
        + 2640403137565854177517180595682247754151) * 10^40
        + 8781062014957200226788497378834953990511) * 10^40
        + 6606901508895512272202999903061473987609)) : ℚ) /
        (((17020601973581595901210212179486169 * 10^40
        + 9647444024346439647321651729805590474493) * 10^40
        + 8437765041342140481689446218567857265594) * 10^40
        + 7832236740208483758892518149765059313664)))

noncomputable def batchC02700PlusMidpointP016Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP016BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP016Center2558‖ ≤ batchC02700PlusMidpointP016Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP016Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP016Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP016Input2558 17 =
      (batchC02700PlusMidpointP016Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP016Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP016Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP016Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP016Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP016Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP016Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP016DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP016Factor2558 * embedPair2542
          batchC02700PlusMidpointP016Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP016Factor2558 : ℝ) *
            batchC02700PlusMidpointP016Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP016Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP016Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP016BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP016Factor2558)

def batchC02700PlusMidpointP017Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2142560996036405154016564653 : ℚ) /
        1888946593147858085478400000000))

def batchC02700PlusMidpointP017Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP017Factor2558 : RatPair2542 := (((((((((((149155 * 10^40
        + 5510608844330571932041824253823364095843) * 10^40
        + 2833865539913185944096478586855106309141) * 10^40
        + 9889341837840228801931728805726018508191) * 10^40
        + 9993452101047104028678326801942811605733) * 10^40
        + 6413648494740439707521773635398983780868) * 10^40
        + 6478169926855007736817996948889157836060) * 10^40
        + 3091650999581098876466232900935288251607) * 10^40
        + 222587294335526237097594432043673476167) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((5297 * 10^40
        + 1892229460023035435785080249009233461101) * 10^40
        + 7338426533247098752369636088139350874496) * 10^40
        + 968129118565230756411049340075538097646) * 10^40
        + 727898577985316929505021311765971268861)) : ℚ) /
        (((4863029135309027400345774908424619 * 10^40
        + 9899269721241839899234757637087311564141) * 10^40
        + 982218583240611566196984633876530647312) * 10^40
        + 7952067640059566788255005185647159803904)))

noncomputable def batchC02700PlusMidpointP017Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP017BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP017Center2558‖ ≤ batchC02700PlusMidpointP017Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP017Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP017Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP017Input2558 17 =
      (batchC02700PlusMidpointP017Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP017Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP017Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP017Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP017Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP017Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP017Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP017DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP017Factor2558 * embedPair2542
          batchC02700PlusMidpointP017Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP017Factor2558 : ℝ) *
            batchC02700PlusMidpointP017Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP017Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP017Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP017BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP017Factor2558)

def batchC02700PlusMidpointP018Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((555375153147096446436377307 : ℚ) /
        472236648286964521369600000000))

def batchC02700PlusMidpointP018Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP018Factor2558 : RatPair2542 := (((((((((((9322 * 10^40
        + 2219413051518139749491219522520261483914) * 10^40
        + 885512485679502589744016721892660124463) * 10^40
        + 1597701183517110673935134329963210151563) * 10^40
        + 931439220359684479435818934771248145470) * 10^40
        + 6450521305959663740794240046256585684194) * 10^40
        + 9073877223272162387729774260916716616837) * 10^40
        + 2042249450400509399515892124201369557761) * 10^40
        + 4000908049717730660884396036792281475287) : ℚ) /
        (((((((7242522288577242935414818870 * 10^40
        + 3031597035296721918846945754893882354277) * 10^40
        + 3203945592395680957142640881138044633867) * 10^40
        + 1894017480746706649635559852441958340163) * 10^40
        + 2758166570239393637101261677307663492291) * 10^40
        + 8438016715288998475801640839286941940637) * 10^40
        + 6495847534803141900767289821359085475463) * 10^40
        + 1442760997796946305630782324007684276224)),
    (((-((((9611 * 10^40
        + 6241123104909261118201799044775831866261) * 10^40
        + 4957461670592935845638743175033734555356) * 10^40
        + 9463324469698380796764158532082862416097) * 10^40
        + 7445540357866459862887842565800393793613)) : ℚ) /
        (((8510300986790797950605106089743084 * 10^40
        + 9823722012173219823660825864902795237246) * 10^40
        + 9218882520671070240844723109283928632797) * 10^40
        + 3916118370104241879446259074882529656832)))

noncomputable def batchC02700PlusMidpointP018Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP018BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP018Center2558‖ ≤ batchC02700PlusMidpointP018Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP018Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP018Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP018Input2558 17 =
      (batchC02700PlusMidpointP018Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP018Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP018Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP018Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP018Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP018Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP018Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP018DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP018Factor2558 * embedPair2542
          batchC02700PlusMidpointP018Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP018Factor2558 : ℝ) *
            batchC02700PlusMidpointP018Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP018Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP018Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP018BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP018Factor2558)

def batchC02700PlusMidpointP019Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((118208299174604243670929049 : ℚ) /
        94447329657392904273920000000))

def batchC02700PlusMidpointP019Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP019Factor2558 : RatPair2542 := (((((((((((9322 * 10^40
        + 2219413049139546538605289234479633132846) * 10^40
        + 9130610834166037701159655016865232083538) * 10^40
        + 2657938412103846671373440799709150906005) * 10^40
        + 5765667457050308439555498420299229505677) * 10^40
        + 6036652303422854520531885797083848912962) * 10^40
        + 4055318492133811585512766756635413835485) * 10^40
        + 1775206921442889547877947438927656714645) * 10^40
        + 7309107785705431598625845530675078197031) : ℚ) /
        (((((((7242522288577242935414818870 * 10^40
        + 3031597035296721918846945754893882354277) * 10^40
        + 3203945592395680957142640881138044633867) * 10^40
        + 1894017480746706649635559852441958340163) * 10^40
        + 2758166570239393637101261677307663492291) * 10^40
        + 8438016715288998475801640839286941940637) * 10^40
        + 6495847534803141900767289821359085475463) * 10^40
        + 1442760997796946305630782324007684276224)),
    (((-((((329 * 10^40
        + 9640392112345833722276011370970727440253) * 10^40
        + 6790126383291514435537772024419095485603) * 10^40
        + 3848317176039066079373343382064837241403) * 10^40
        + 489925054522961936889542052886315772805)) : ℚ) /
        (((274525838283574127438874389991712 * 10^40
        + 4187862000392684510440671802093638556040) * 10^40
        + 2232867178086163556156281390622062213961) * 10^40
        + 2061810270003362641272459970157500956672)))

noncomputable def batchC02700PlusMidpointP019Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP019BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP019Center2558‖ ≤ batchC02700PlusMidpointP019Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP019Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP019Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP019Input2558 17 =
      (batchC02700PlusMidpointP019Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP019Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP019Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP019Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP019Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP019Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP019Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP019DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP019Factor2558 * embedPair2542
          batchC02700PlusMidpointP019Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP019Factor2558 : ℝ) *
            batchC02700PlusMidpointP019Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP019Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP019Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP019BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP019Factor2558)

def batchC02700PlusMidpointP020Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2519303167856168777929316541 : ℚ) /
        1888946593147858085478400000000))

def batchC02700PlusMidpointP020Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP020Factor2558 : RatPair2542 := (((((((((((149155 * 10^40
        + 5510608742160672949619395588245377488424) * 10^40
        + 6690468067654815446864295092137407912485) * 10^40
        + 3887526972507656458996486907922841159939) * 10^40
        + 1562370964950138492360536579801719491922) * 10^40
        + 5896975308376491903951440895318971647591) * 10^40
        + 8144515730512773197132393512451910473376) * 10^40
        + 2874390498245285535155063372775475942791) * 10^40
        + 6754519519613398476921564069511558055335) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((6228 * 10^40
        + 6327506144270173104189199800512433352607) * 10^40
        + 3519978068638596465122436729651949576023) * 10^40
        + 7011608982758252253933933255240136894271) * 10^40
        + 7115215626267791881000498146276005531917)) : ℚ) /
        (((4863029135309027400345774908424619 * 10^40
        + 9899269721241839899234757637087311564141) * 10^40
        + 982218583240611566196984633876530647312) * 10^40
        + 7952067640059566788255005185647159803904)))

noncomputable def batchC02700PlusMidpointP020Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP020BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP020Center2558‖ ≤ batchC02700PlusMidpointP020Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP020Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP020Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP020Input2558 17 =
      (batchC02700PlusMidpointP020Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP020Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP020Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP020Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP020Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP020Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP020Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP020DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP020Factor2558 * embedPair2542
          batchC02700PlusMidpointP020Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP020Factor2558 : ℝ) *
            batchC02700PlusMidpointP020Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP020Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP020Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP020BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP020Factor2558)

def batchC02700PlusMidpointP021Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2648771212589104536068841693 : ℚ) /
        1888946593147858085478400000000))

def batchC02700PlusMidpointP021Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP021Factor2558 : RatPair2542 := (((((((((((149155 * 10^40
        + 5510608703237300973650646861080286364106) * 10^40
        + 9084416558281600011288030551514429953067) * 10^40
        + 213755676219119928786587451393358479258) * 10^40
        + 2602952269481555149527937512709640363119) * 10^40
        + 7202476791577735273151872255500628068527) * 10^40
        + 169812038727577738696713455469208208204) * 10^40
        + 1974451062189186652404784069621638526977) * 10^40
        + 4877247536294880567831965378947438657127) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((1478 * 10^40
        + 7443087415808353718603170307321099000108) * 10^40
        + 6456417293158960864997831924415830933521) * 10^40
        + 1684449298724273916429601792752282968717) * 10^40
        + 6758379787942239628081331933333805375077)) : ℚ) /
        (((1098103353134296509755497559966849 * 10^40
        + 6751448001570738041762687208374554224160) * 10^40
        + 8931468712344654224625125562488248855844) * 10^40
        + 8247241080013450565089839880630003826688)))

noncomputable def batchC02700PlusMidpointP021Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP021BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP021Center2558‖ ≤ batchC02700PlusMidpointP021Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP021Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP021Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP021Input2558 17 =
      (batchC02700PlusMidpointP021Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP021Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP021Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP021Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP021Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP021Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP021Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP021DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP021Factor2558 * embedPair2542
          batchC02700PlusMidpointP021Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP021Factor2558 : ℝ) *
            batchC02700PlusMidpointP021Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP021Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP021Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP021BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP021Factor2558)

def batchC02700PlusMidpointP022Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((543007546456794340281131487 : ℚ) /
        377789318629571617095680000000))

def batchC02700PlusMidpointP022Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP022Factor2558 : RatPair2542 := (((((((((((149155 * 10^40
        + 5510608682560346370769554214772806103486) * 10^40
        + 7407885544146861194740134247169039293516) * 10^40
        + 7244049947225005247768269879331522014949) * 10^40
        + 1865530293905442677783486808289205873471) * 10^40
        + 8920321863375629684824154675594710126038) * 10^40
        + 780879837939971082849265668371354224402) * 10^40
        + 9670132656404858202930661481665750474215) * 10^40
        + 4997008481279305103935732918569949747671) : ℚ) /
        (((((((115880356617235886966637101924 * 10^40
        + 8505552564747550701551132078302117668437) * 10^40
        + 1263129478330895314282254098208714141875) * 10^40
        + 304279691947306394168957639071333442612) * 10^40
        + 4130665123830298193620186836922615876669) * 10^40
        + 5008267444623975612826253428591071050202) * 10^40
        + 3933560556850270412276637141745367607410) * 10^40
        + 3084175964751140890092517184122948419584)),
    (((-((((46987 * 10^40
        + 9179606395932135400278194628820644890498) * 10^40
        + 9251895384798656006209263723747143283875) * 10^40
        + 5148378689581663880633116370268373697566) * 10^40
        + 4671368972553847265360118898746704201165)) : ℚ) /
        (((34041203947163191802420424358972339 * 10^40
        + 9294888048692879294643303459611180948987) * 10^40
        + 6875530082684280963378892437135714531189) * 10^40
        + 5664473480416967517785036299530118627328)))

noncomputable def batchC02700PlusMidpointP022Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP022BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP022Center2558‖ ≤ batchC02700PlusMidpointP022Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP022Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP022Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP022Input2558 17 =
      (batchC02700PlusMidpointP022Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP022Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP022Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP022Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP022Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP022Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP022Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP022DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP022Factor2558 * embedPair2542
          batchC02700PlusMidpointP022Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP022Factor2558 : ℝ) *
            batchC02700PlusMidpointP022Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP022Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP022Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP022BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP022Factor2558)

def batchC02700PlusMidpointP023Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1453048211174897778209007387 : ℚ) /
        944473296573929042739200000000))

def batchC02700PlusMidpointP023Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP023Factor2558 : RatPair2542 := (((((((((((37288 * 10^40
        + 8877652155021207365185342417306430857332) * 10^40
        + 4607910315779402033951726970495358297775) * 10^40
        + 4114825696723316340170432934721558004427) * 10^40
        + 1539629668735301915281872936448240738997) * 10^40
        + 6454552050405120086395630702134748704290) * 10^40
        + 8707071566868387344625798590992507234173) * 10^40
        + 6261724172075921875730660906718870662514) * 10^40
        + 2447227480915123518724898297266918677335) : ℚ) /
        (((((((28970089154308971741659275481 * 10^40
        + 2126388141186887675387783019575529417109) * 10^40
        + 2815782369582723828570563524552178535468) * 10^40
        + 7576069922986826598542239409767833360653) * 10^40
        + 1032666280957574548405046709230653969167) * 10^40
        + 3752066861155993903206563357147767762550) * 10^40
        + 5983390139212567603069159285436341901852) * 10^40
        + 5771043991187785222523129296030737104896)),
    (((-((((25147 * 10^40
        + 2417225320192239148975351659379497165645) * 10^40
        + 157140521474363549095701547936907158358) * 10^40
        + 9254280983598626055788497362118330501653) * 10^40
        + 9996616877690218568690419261549355768333)) : ℚ) /
        (((17020601973581595901210212179486169 * 10^40
        + 9647444024346439647321651729805590474493) * 10^40
        + 8437765041342140481689446218567857265594) * 10^40
        + 7832236740208483758892518149765059313664)))

noncomputable def batchC02700PlusMidpointP023Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP023BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP023Center2558‖ ≤ batchC02700PlusMidpointP023Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP023Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP023Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP023Input2558 17 =
      (batchC02700PlusMidpointP023Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP023Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP023Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP023Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP023Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP023Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP023Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP023DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP023Factor2558 * embedPair2542
          batchC02700PlusMidpointP023Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP023Factor2558 : ℝ) *
            batchC02700PlusMidpointP023Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP023Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP023Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP023BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP023Factor2558)

def batchC02700PlusMidpointP024Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1496949629611413064555803333 : ℚ) /
        944473296573929042739200000000))

def batchC02700PlusMidpointP024Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP024Factor2558 : RatPair2542 := (((((((((((37288 * 10^40
        + 8877652147487315848053930818151032544621) * 10^40
        + 7974325124054270665817683351688113178621) * 10^40
        + 5321255185267732136539391329586007909489) * 10^40
        + 4313894005796730802654039156973727539967) * 10^40
        + 5041620329413347603317924012945179537517) * 10^40
        + 9949231466162388383449809912049700859482) * 10^40
        + 7142605546511873478119538354870347234669) * 10^40
        + 1612076445518198675500891483581064638615) : ℚ) /
        (((((((28970089154308971741659275481 * 10^40
        + 2126388141186887675387783019575529417109) * 10^40
        + 2815782369582723828570563524552178535468) * 10^40
        + 7576069922986826598542239409767833360653) * 10^40
        + 1032666280957574548405046709230653969167) * 10^40
        + 3752066861155993903206563357147767762550) * 10^40
        + 5983390139212567603069159285436341901852) * 10^40
        + 5771043991187785222523129296030737104896)),
    (((-((((25907 * 10^40
        + 235197873268576219543475314448232935362) * 10^40
        + 993942457664951042731112757626760755639) * 10^40
        + 5503373631490209172134756787838590366491) * 10^40
        + 4321508217473011626310232288531309264147)) : ℚ) /
        (((17020601973581595901210212179486169 * 10^40
        + 9647444024346439647321651729805590474493) * 10^40
        + 8437765041342140481689446218567857265594) * 10^40
        + 7832236740208483758892518149765059313664)))

noncomputable def batchC02700PlusMidpointP024Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP024BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP024Center2558‖ ≤ batchC02700PlusMidpointP024Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP024Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP024Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP024Input2558 17 =
      (batchC02700PlusMidpointP024Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP024Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP024Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP024Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP024Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP024Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP024Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP024DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP024Factor2558 * embedPair2542
          batchC02700PlusMidpointP024Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP024Factor2558 : ℝ) *
            batchC02700PlusMidpointP024Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP024Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP024Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP024BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP024Factor2558)

def batchC02700PlusMidpointP025Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((48499811018293309025440887 : ℚ) /
        29514790517935282585600000000))

def batchC02700PlusMidpointP025Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP025Factor2558 : RatPair2542 := (((((((((((36 * 10^40
        + 4149294582165746451693940860936319392951) * 10^40
        + 810176946619789358185580939734052829060) * 10^40
        + 2192978827722627826973094753197717312556) * 10^40
        + 5050855634820802132934965793749549495190) * 10^40
        + 248507226548925996717841586830722242265) * 10^40
        + 2076955294465484919272087755824546800371) * 10^40
        + 9049881056622996967750145551181288761505) * 10^40
        + 5000388664512238082702256644302356456287) : ℚ) /
        (((((((28291102689754855216464136 * 10^40
        + 2121217175919127819995495881855054227946) * 10^40
        + 3957827912470295628738838440941945486851) * 10^40
        + 437086005784166822850138905673601399766) * 10^40
        + 2627961588164997631394926803426983060516) * 10^40
        + 7650148502794097650296100159528464616955) * 10^40
        + 6158186904432824773049872225864683927638) * 10^40
        + 5279073285147644321506370243453155016704)),
    (((-((((17 * 10^40
        + 1298791303819787083590316853081987590704) * 10^40
        + 1075901646182174323152801831991196017404) * 10^40
        + 8314580860211279177503337520132085040298) * 10^40
        + 63309380173623799365331284213343706017)) : ℚ) /
        (((10854975748457650447200390420590 * 10^40
        + 6696203727056343392632220441154212749027) * 10^40
        + 1006656737909019222245975412129188684480) * 10^40
        + 6089178722410847247295212065146533838848)))

noncomputable def batchC02700PlusMidpointP025Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP025BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP025Center2558‖ ≤ batchC02700PlusMidpointP025Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP025Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP025Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP025Input2558 17 =
      (batchC02700PlusMidpointP025Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP025Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP025Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP025Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP025Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP025Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP025Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP025DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP025Factor2558 * embedPair2542
          batchC02700PlusMidpointP025Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP025Factor2558 : ℝ) *
            batchC02700PlusMidpointP025Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP025Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP025Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP025BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP025Factor2558)

def batchC02700PlusMidpointP026Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((100515438378930241589387643 : ℚ) /
        59029581035870565171200000000))

def batchC02700PlusMidpointP026Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP026Factor2558 : RatPair2542 := (((((((((((145 * 10^40
        + 6597178328622589142190353862415496881373) * 10^40
        + 9661616546277240931957079892869843638020) * 10^40
        + 9806130590466474373630194349383975850212) * 10^40
        + 9557192057632983510697460631782413081594) * 10^40
        + 4486382698834573941643937395205381587629) * 10^40
        + 5187110046272818360532734178466326101387) * 10^40
        + 6382013874997970634905774903909509208895) * 10^40
        + 5161849889591063731030859522324062163735) : ℚ) /
        (((((((113164410759019420865856544 * 10^40
        + 8484868703676511279981983527420216911785) * 10^40
        + 5831311649881182514955353763767781947404) * 10^40
        + 1748344023136667291400555622694405599065) * 10^40
        + 511846352659990525579707213707932242067) * 10^40
        + 600594011176390601184400638113858467822) * 10^40
        + 4632747617731299092199488903458735710554) * 10^40
        + 1116293140590577286025480973812620066816)),
    (((-((((1739 * 10^40
        + 5747823930826188347614638353826859903148) * 10^40
        + 2649263645647731480993766691160935231132) * 10^40
        + 2664007340835999894495018490253339101507) * 10^40
        + 9956969353709517751343765237498493963437)) : ℚ) /
        (((1063787623348849743825638261217885 * 10^40
        + 6227965251521652477957603233112849404655) * 10^40
        + 8652360315083883780105590388660491079099) * 10^40
        + 6739514796263030234930782384360316207104)))

noncomputable def batchC02700PlusMidpointP026Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP026BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP026Center2558‖ ≤ batchC02700PlusMidpointP026Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP026Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP026Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP026Input2558 17 =
      (batchC02700PlusMidpointP026Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP026Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP026Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP026Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP026Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP026Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP026Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP026DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP026Factor2558 * embedPair2542
          batchC02700PlusMidpointP026Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP026Factor2558 : ℝ) *
            batchC02700PlusMidpointP026Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP026Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP026Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP026BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP026Factor2558)

def batchC02700PlusMidpointP027Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((211177751933296260595876053 : ℚ) /
        118059162071741130342400000000))

def batchC02700PlusMidpointP027Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP027Factor2558 : RatPair2542 := (((((((((((582 * 10^40
        + 6388713314247041778891015815163437434955) * 10^40
        + 9734591119340450695955838949344994519157) * 10^40
        + 3101152417830870575000632334755067877909) * 10^40
        + 5657777468518691154954183644531812465477) * 10^40
        + 6484312009555073655711519107104976133445) * 10^40
        + 6355911115750427060377142565144970303805) * 10^40
        + 1885557066883986041331191405749465022071) * 10^40
        + 7211717153991515723852839628207972157687) : ℚ) /
        (((((((452657643036077683463426179 * 10^40
        + 3939474814706045119927934109680867647142) * 10^40
        + 3325246599524730059821415055071127789616) * 10^40
        + 6993376092546669165602222490777622396260) * 10^40
        + 2047385410639962102318828854831728968268) * 10^40
        + 2402376044705562404737602552455433871289) * 10^40
        + 8530990470925196368797955613834942842216) * 10^40
        + 4465172562362309144101923895250480267264)),
    (((-((((3654 * 10^40
        + 7568989424919003019648035236175165185557) * 10^40
        + 9704059622523991846997448996472746210059) * 10^40
        + 7359237111102643135813587912797412144420) * 10^40
        + 968066363127163437669598730459859754627)) : ℚ) /
        (((2127575246697699487651276522435771 * 10^40
        + 2455930503043304955915206466225698809311) * 10^40
        + 7304720630167767560211180777320982158199) * 10^40
        + 3479029592526060469861564768720632414208)))

noncomputable def batchC02700PlusMidpointP027Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP027BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP027Center2558‖ ≤ batchC02700PlusMidpointP027Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP027Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP027Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP027Input2558 17 =
      (batchC02700PlusMidpointP027Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP027Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP027Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP027Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP027Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP027Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP027Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP027DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP027Factor2558 * embedPair2542
          batchC02700PlusMidpointP027Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP027Factor2558 : ℝ) *
            batchC02700PlusMidpointP027Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP027Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP027Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP027BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP027Factor2558)

def batchC02700PlusMidpointP028Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((860780157665754287223049953 : ℚ) /
        472236648286964521369600000000))

def batchC02700PlusMidpointP028Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP028Factor2558 : RatPair2542 := (((((((((((9322 * 10^40
        + 2219413026358399875412775432124580557301) * 10^40
        + 7161447856031544920637883336217120583441) * 10^40
        + 8825674803536157496726571233846532499401) * 10^40
        + 6318096360807152330148412232209480851730) * 10^40
        + 9859945365147287345176249031482480652421) * 10^40
        + 9019396957533368430566514905587937777259) * 10^40
        + 95623061653933873122414821176368251632) * 10^40
        + 14878905528631726307422550875888684527) : ℚ) /
        (((((((7242522288577242935414818870 * 10^40
        + 3031597035296721918846945754893882354277) * 10^40
        + 3203945592395680957142640881138044633867) * 10^40
        + 1894017480746706649635559852441958340163) * 10^40
        + 2758166570239393637101261677307663492291) * 10^40
        + 8438016715288998475801640839286941940637) * 10^40
        + 6495847534803141900767289821359085475463) * 10^40
        + 1442760997796946305630782324007684276224)),
    (((-((((14897 * 10^40
        + 1290341958730534679945353007082461297356) * 10^40
        + 4629631159026868301840307331813668403654) * 10^40
        + 696864671165534581082726833296662442223) * 10^40
        + 3194529308299757022672348458316088264727)) : ℚ) /
        (((8510300986790797950605106089743084 * 10^40
        + 9823722012173219823660825864902795237246) * 10^40
        + 9218882520671070240844723109283928632797) * 10^40
        + 3916118370104241879446259074882529656832)))

noncomputable def batchC02700PlusMidpointP028Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP028BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP028Center2558‖ ≤ batchC02700PlusMidpointP028Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP028Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP028Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP028Input2558 17 =
      (batchC02700PlusMidpointP028Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP028Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP028Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP028Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP028Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP028Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP028Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP028DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP028Factor2558 * embedPair2542
          batchC02700PlusMidpointP028Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP028Factor2558 : ℝ) *
            batchC02700PlusMidpointP028Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP028Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP028Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP028BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP028Factor2558)

def batchC02700PlusMidpointP029Input2558 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((885244406725664293840781901 : ℚ) /
        472236648286964521369600000000))

def batchC02700PlusMidpointP029Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02700PlusMidpointP029Factor2558 : RatPair2542 := (((((((((((9322 * 10^40
        + 2219413023873543161385161460668412560896) * 10^40
        + 3555760382705966242079359275318107989508) * 10^40
        + 8672148094644580712457006201810494451718) * 10^40
        + 4500661913263340983897443398952905790813) * 10^40
        + 3373803036872663455753572517550566829476) * 10^40
        + 488434101920026393113889931572676115694) * 10^40
        + 2742046261410333067627600239801082542297) * 10^40
        + 7912184233602651109688879797211722912775) : ℚ) /
        (((((((7242522288577242935414818870 * 10^40
        + 3031597035296721918846945754893882354277) * 10^40
        + 3203945592395680957142640881138044633867) * 10^40
        + 1894017480746706649635559852441958340163) * 10^40
        + 2758166570239393637101261677307663492291) * 10^40
        + 8438016715288998475801640839286941940637) * 10^40
        + 6495847534803141900767289821359085475463) * 10^40
        + 1442760997796946305630782324007684276224)),
    (((-((((15320 * 10^40
        + 5206188235722367523291511626403758276411) * 10^40
        + 5316781174544293047842236891625606998519) * 10^40
        + 8237875807106343726194119215632099035576) * 10^40
        + 6604368293426945719238680311290935779659)) : ℚ) /
        (((8510300986790797950605106089743084 * 10^40
        + 9823722012173219823660825864902795237246) * 10^40
        + 9218882520671070240844723109283928632797) * 10^40
        + 3916118370104241879446259074882529656832)))

noncomputable def batchC02700PlusMidpointP029Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02700PlusMidpointP029BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP029Center2558‖ ≤ batchC02700PlusMidpointP029Error2558
          := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02700PlusMidpointP029Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02700PlusMidpointP029Input2558]
  have hs : compactExp2547 batchC02700PlusMidpointP029Input2558 17 =
      (batchC02700PlusMidpointP029Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02700PlusMidpointP029Input2558 17).2 : ℝ) =
      batchC02700PlusMidpointP029Error2558 :=
      by
    rw [hs]
    norm_num [batchC02700PlusMidpointP029Error2558]
  have h := compactExp_error2547 batchC02700PlusMidpointP029Input2558 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      batchC02700PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^17 * embedPair2542
          batchC02700PlusMidpointP029Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02700PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02700PlusMidpointP029Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02700PlusMidpointP029DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP029Factor2558 * embedPair2542
          batchC02700PlusMidpointP029Center2558‖ ≤
        (pairMagnitude2542 batchC02700PlusMidpointP029Factor2558 : ℝ) *
            batchC02700PlusMidpointP029Error2558 := by
  have hx : |batchC02700PlusMidpointPosition2558| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC02700PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchC02700PlusMidpointPosition2558 = embedPair2542
          batchC02700PlusMidpointP029Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02700PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02700PlusMidpointP029Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02700PlusMidpointP029BaseError2558
    (embedPair_magnitude2542 batchC02700PlusMidpointP029Factor2558)

theorem batchC02700PlusMidpointGrid2558 :
    -stripRadius2303 + ((5401 : ℝ) /
        2) * (2 * stripRadius2303 / 10240) =
      batchC02700PlusMidpointPosition2558 := by
  norm_num [stripRadius2303, batchC02700PlusMidpointPosition2558]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP000DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP001DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP002DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP003DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP004DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP005DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP006DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP007DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP008DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP009DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP010DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP011DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP012DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP013DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP014DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP015DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP016DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP017DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP018DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP019DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP020DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP021DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP022DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP023DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP024DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP025DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP026DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP027DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP028DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointP029DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusMidpointGrid2558
