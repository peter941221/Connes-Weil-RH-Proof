import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def pairedN02700PlusPosition2553 : ℝ := (((-7929856121) : ℝ) /
        2560000000)

theorem pairedN02700PlusZero2553 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def pairedN02700PlusP000Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP000Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP000Error2553 : ℝ := 0

theorem pairedN02700PlusP000Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN02700PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem pairedN02700PlusP000BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP000Center2553‖ ≤ pairedN02700PlusP000Error2553 := by
  rw [pairedN02700PlusP000Exterior2553]
  norm_num [pairedN02700PlusP000Center2553, pairedN02700PlusP000Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP000DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP000Factor2553 * embedPair2542 pairedN02700PlusP000Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP000Factor2553 : ℝ) * pairedN02700PlusP000Error2553 :=
            by
  rw [pairedN02700PlusP000Exterior2553]
  norm_num [pairedN02700PlusP000Factor2553, pairedN02700PlusP000Center2553,
      pairedN02700PlusP000Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP001Input2553 : RatPair2542 := ((((-(6802033789088462436296480399940728088864
    *
    10^40
        + 8972281175305676998687477935786509916481)) : ℚ) /
        ((1 * 10^40
        + 8752578370474248106975932892819564741070) * 10^40
        + 9992275832742435204355224137891840000000)),
    ((43806833004475480685705509 : ℚ) /
        184467440737095516160000000))

def pairedN02700PlusP001Center2553 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def pairedN02700PlusP001Factor2553 : RatPair2542 := ((((((((((((((11580 * 10^40
        + 2551684365954693445363484655155344174177) * 10^40
        + 6284432213830271158663760632252958362905) * 10^40
        + 953166390166095064925913222145161221680) * 10^40
        + 7867250343568748642790201549214000010849) * 10^40
        + 2967527517612109802149107814802925421138) * 10^40
        + 9566780931603092560238782089001432193363) * 10^40
        + 3165650429471361270946902741025477845267) * 10^40
        + 9611026038231368549620053022529685208098) * 10^40
        + 7973743787036004211582554309239996630995) * 10^40
        + 4889067068353834528410477296016534984081) * 10^40
        + 1473614792971824372877484051667675350453) : ℚ) /
        ((((((((((530855096499264200375034182669100673 * 10^40
        + 715392029682525059248925153059675044429) * 10^40
        + 5489363255140266824871665260987928636415) * 10^40
        + 458272112093495727347951208345346508074) * 10^40
        + 9148582145375010260865381697339130077386) * 10^40
        + 7591781714327890688097094366362750108129) * 10^40
        + 6933614735151579388525686059108082363210) * 10^40
        + 6030781413670877109197816563879673208538) * 10^40
        + 6492950348723417282277947976729800937427) * 10^40
        + 2748721362364127200489517533382453361543) * 10^40
        + 8879986962378556953061808521299726696448)),
    (((-((((((((31 * 10^40
        + 7402902405693293869843981751664535323634) * 10^40
        + 4366627428419548604845220464458927903337) * 10^40
        + 2778255452338398484875278163782916207418) * 10^40
        + 3816799354044767403759543732921875894131) * 10^40
        + 9490302488583233529748515626958926689302) * 10^40
        + 6464417887325835175074215828666455790643) * 10^40
        + 7137062879519429370664561656864439893842) * 10^40
        + 1732608586697768441969398698818949316683)) : ℚ) /
        (((((((7299845313529492577405338625902062 * 10^40
        + 5040060464039829882467981137888151089350) * 10^40
        + 7680046837126516249820690069166339688010) * 10^40
        + 4945758958980690475063849034962907971196) * 10^40
        + 5509877864502588213528625647279806208619) * 10^40
        + 8720169451280884093960950506406750384451) * 10^40
        + 8546691820820725614871493256901978037975) * 10^40
        + 4996929156900611117775561124908506284032)))

noncomputable def pairedN02700PlusP001Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02700PlusP001BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP001Center2553‖ ≤ pairedN02700PlusP001Error2553 := by
  have hx : |pairedN02700PlusPosition2553| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [pairedN02700PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02700PlusP001Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02700PlusP001Input2553]
  have hs : compactExp2547 pairedN02700PlusP001Input2553 9 =
      (pairedN02700PlusP001Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02700PlusP001Input2553 9).2 : ℝ) =
      pairedN02700PlusP001Error2553
      := by
    rw [hs]
    norm_num [pairedN02700PlusP001Error2553]
  have h := compactExp_error2547 pairedN02700PlusP001Input2553 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      pairedN02700PlusPosition2553 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          pairedN02700PlusP001Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02700PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02700PlusP001Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02700PlusP001DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP001Factor2553 * embedPair2542 pairedN02700PlusP001Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP001Factor2553 : ℝ) * pairedN02700PlusP001Error2553 :=
            by
  have hx : |pairedN02700PlusPosition2553| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [pairedN02700PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) pairedN02700PlusPosition2553 = embedPair2542
          pairedN02700PlusP001Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02700PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02700PlusP001Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02700PlusP001BaseError2553
    (embedPair_magnitude2542 pairedN02700PlusP001Factor2553)

def pairedN02700PlusP002Input2553 : RatPair2542 := ((((-((18 * 10^40
        + 674198634096258458583628358041758074204) * 10^40
        + 9347881399256746042719324903889090304321)) : ℚ) /
        ((73 * 10^40
        + 2973526485978139422317359752257065937823) * 10^40
        + 6716006270187613354841793103134720000000)),
    (((-43806833004475480685705509) : ℚ) /
        92233720368547758080000000))

def pairedN02700PlusP002Center2553 : RatPair2542 := ((((-342022637592315929245) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-462193622279321905361) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN02700PlusP002Factor2553 : RatPair2542 := ((((-(((((((((((1557740985546 * 10^40
        + 9814527370367420397827746208496820226428) * 10^40
        + 4103128637725152101093372746783229775747) * 10^40
        + 7409048140346066145262244052570825689344) * 10^40
        + 4791139166630464565904495264847150723918) * 10^40
        + 9978948179935057354575084257153082623135) * 10^40
        + 5318701095755658063409036532503692059853) * 10^40
        + 3614710749496850579833782928788810218659) * 10^40
        + 2574019124876712290699164134376898150727) * 10^40
        + 1807181629084067321722454709795118210475) * 10^40
        + 1136913525141294249646945064481018207049) * 10^40
        + 3313045918472131336465957509918541118027)) : ℚ) /
        (((((((((((12114898 * 10^40
        + 808526435114873017777700953161428250352) * 10^40
        + 654977035246259760268619518356430313504) * 10^40
        + 66997916955805644216311755183676721994) * 10^40
        + 6630844278013223882961518184401750937135) * 10^40
        + 6174312101300894008825153507630529833013) * 10^40
        + 2241880182730136398551076257160017283966) * 10^40
        + 1784056612655200506715307522328759125821) * 10^40
        + 6511239150957279482391535525021371145080) * 10^40
        + 8926853851767160798356756790048568749286) * 10^40
        + 6309802908408506998128790377591588177656) * 10^40
        + 5298436988590367697105894115527274528768)),
    ((((((((((3870078 * 10^40
        + 2126662519068673942251461457929006770648) * 10^40
        + 3363989550984380572130688807562964312151) * 10^40
        + 7817122809367025494945812961005724082488) * 10^40
        + 4660724636956513820942575990796091849410) * 10^40
        + 3799412692071562425781331591480641917323) * 10^40
        + 7016555236734243419888221787565790751981) * 10^40
        + 2587731211847183457512255512755787957444) * 10^40
        + 3652279829419198636709022292528384933963) : ℚ) /
        ((((((((27 * 10^40
        + 2610663525562379419552896007600270606803) * 10^40
        + 6063064689458095386466352056150455113401) * 10^40
        + 119106213456037419595487161540470251152) * 10^40
        + 5026560681324236180341400296724160954667) * 10^40
        + 4615026096081574931661867517444799672804) * 10^40
        + 8762536589996236920173911548894242629877) * 10^40
        + 8765772211137353631322503631410017498) * 10^40
        + 3069405594712846138679290003867830321152)))

noncomputable def pairedN02700PlusP002Error2553 : ℝ := ((2124679950171895707 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02700PlusP002BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP002Center2553‖ ≤ pairedN02700PlusP002Error2553 := by
  have hx : |pairedN02700PlusPosition2553| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [pairedN02700PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02700PlusP002Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02700PlusP002Input2553]
  have hs : compactExp2547 pairedN02700PlusP002Input2553 8 =
      (pairedN02700PlusP002Center2553, ((2124679950171895707 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02700PlusP002Input2553 8).2 : ℝ) =
      pairedN02700PlusP002Error2553
      := by
    rw [hs]
    norm_num [pairedN02700PlusP002Error2553]
  have h := compactExp_error2547 pairedN02700PlusP002Input2553 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      pairedN02700PlusPosition2553 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          pairedN02700PlusP002Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02700PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02700PlusP002Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02700PlusP002DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP002Factor2553 * embedPair2542 pairedN02700PlusP002Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP002Factor2553 : ℝ) * pairedN02700PlusP002Error2553 :=
            by
  have hx : |pairedN02700PlusPosition2553| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [pairedN02700PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) pairedN02700PlusPosition2553 = embedPair2542
          pairedN02700PlusP002Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02700PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02700PlusP002Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02700PlusP002BaseError2553
    (embedPair_magnitude2542 pairedN02700PlusP002Factor2553)

def pairedN02700PlusP003Input2553 : RatPair2542 := ((((-((2408 * 10^40
        + 369770750836432817481799749086268690782) * 10^40
        + 3306951315371206135663408401255839432267)) : ℚ) /
        ((13284 * 10^40
        + 922703065279921881810676711054660831348) * 10^40
        + 9952512674799299317166344800829440000000)),
    (((-43806833004475480685705509) : ℚ) /
        92233720368547758080000000))

def pairedN02700PlusP003Center2553 : RatPair2542 := ((((-3050957105819623379802289723) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-4122922757640557388486708103) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def pairedN02700PlusP003Factor2553 : RatPair2542 := ((((-(((((((((((764296751897339906297680010 *
    10^40
        + 9174751986968691763753713220021270288175) * 10^40
        + 9018163147868791210428675066113811424115) * 10^40
        + 1233985970324443068907186870718968473067) * 10^40
        + 4696715751461092567516778541845489639387) * 10^40
        + 3717172209535408903275802230110935461347) * 10^40
        + 8824705509810924047100020562756907486755) * 10^40
        + 7392508635687186933984090896978589547017) * 10^40
        + 8505842652868837956118181512358673973967) * 10^40
        + 4594540685978952747961006376510391982049) * 10^40
        + 3614713815560511383415023935940657103735) * 10^40
        + 6579013505015077378482069458849748755281)) : ℚ) /
        (((((((((((11591645624957923641255 * 10^40
        + 7169307872138455404407220793325865774016) * 10^40
        + 1306576402704904108300689441178374989106) * 10^40
        + 3337009721098198857409058631031722259601) * 10^40
        + 9840504720346373095684392942248556673910) * 10^40
        + 188874464745142484446815513898313297959) * 10^40
        + 3895234986689035515941419368241724842493) * 10^40
        + 7572594310394036144173205388518287780874) * 10^40
        + 4382400772073097468240060841430635623810) * 10^40
        + 8394407883881474032463357826835105430657) * 10^40
        + 471503876859420940021589950296099627515) * 10^40
        + 2477037911601278867886710049441373487104)),
    (((-((((((((1063521344408139 * 10^40
        + 6795964174461492254658750580314264142914) * 10^40
        + 8479568028108947534271350980983924286424) * 10^40
        + 8336938210967472857016464741845132920561) * 10^40
        + 4279009416141103706269672180247483797643) * 10^40
        + 4620594684857297996927317102467740199406) * 10^40
        + 3621671208745918672115708469434287637248) * 10^40
        + 2480454631024898637837187536196236198425) * 10^40
        + 5678979696903057104148574790217223191717)) : ℚ) /
        ((((((((29411502928 * 10^40
        + 107965064720505489447392351946316508944) * 10^40
        + 570954626614098327124123755152464922891) * 10^40
        + 2877605674389988743713106167413174053831) * 10^40
        + 7239508824147568550728793920929118234919) * 10^40
        + 8857157502476592489823314064997997943306) * 10^40
        + 1804629076702604115588829234849554350924) * 10^40
        + 4283956541675445184864963615547766928589) * 10^40
        + 9582731533623441209194749549825000210432)))

noncomputable def pairedN02700PlusP003Error2553 : ℝ := ((35512274632534440194531833 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02700PlusP003BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP003Center2553‖ ≤ pairedN02700PlusP003Error2553 := by
  have hx : |pairedN02700PlusPosition2553| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [pairedN02700PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02700PlusP003Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02700PlusP003Input2553]
  have hs : compactExp2547 pairedN02700PlusP003Input2553 8 =
      (pairedN02700PlusP003Center2553, ((35512274632534440194531833 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02700PlusP003Input2553 8).2 : ℝ) =
      pairedN02700PlusP003Error2553
      := by
    rw [hs]
    norm_num [pairedN02700PlusP003Error2553]
  have h := compactExp_error2547 pairedN02700PlusP003Input2553 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      pairedN02700PlusPosition2553 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          pairedN02700PlusP003Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02700PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02700PlusP003Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02700PlusP003DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP003Factor2553 * embedPair2542 pairedN02700PlusP003Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP003Factor2553 : ℝ) * pairedN02700PlusP003Error2553 :=
            by
  have hx : |pairedN02700PlusPosition2553| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [pairedN02700PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) pairedN02700PlusPosition2553 = embedPair2542
          pairedN02700PlusP003Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02700PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02700PlusP003Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02700PlusP003BaseError2553
    (embedPair_magnitude2542 pairedN02700PlusP003Factor2553)

def pairedN02700PlusP004Input2553 : RatPair2542 := ((((-((42 * 10^40
        + 612804092845883320592175325793232154346) * 10^40
        + 2807937213934500805991847895100027804321)) : ℚ) /
        ((267 * 10^40
        + 9934518708431604868451190036789843840469) * 10^40
        + 7242920599205959594841793103134720000000)),
    ((43806833004475480685705509 : ℚ) /
        92233720368547758080000000))

def pairedN02700PlusP004Center2553 : RatPair2542 := ((((-3088285000154142764160101575539) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((4173365952909685099392742956493 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN02700PlusP004Factor2553 : RatPair2542 := ((((-(((((((((((1016885133931067 * 10^40
        + 2558388139263035300095821892434586930737) * 10^40
        + 1104373342449062171710006010147085614544) * 10^40
        + 6865429994131974615432278217429131289715) * 10^40
        + 6439125430232722989859627131299316077057) * 10^40
        + 7403131658348747080513625897309750605662) * 10^40
        + 5690669888675789629340894331181107564475) * 10^40
        + 1207253441496213086071265231220979752095) * 10^40
        + 9147383308052493214522657160274252103951) * 10^40
        + 5775122843910360609309253458174409699622) * 10^40
        + 8697485519133442292592360624553530109351) * 10^40
        + 8372747373367643620524917711090416118027)) : ℚ) /
        (((((((((((28942438972 * 10^40
        + 3657646772279795725887540344474329274315) * 10^40
        + 3959325550306428794551586301701551816782) * 10^40
        + 6192740838979085908754914458596252577942) * 10^40
        + 1132446609039100958234748718225104215413) * 10^40
        + 9051242576597935768780229020676597808408) * 10^40
        + 6802209594057265208799415035889783174068) * 10^40
        + 5260834448098122429992084481393987137970) * 10^40
        + 1532484656859527888074553476657700266655) * 10^40
        + 6150862715353027237022237965886408319713) * 10^40
        + 9169981849055012881150024208049122294911) * 10^40
        + 8611116161343013813318630115527274528768)),
    ((((((((((263700523 * 10^40
        + 7452449380902000968621914489593907782500) * 10^40
        + 7366493756515192977133186437209370550321) * 10^40
        + 9877506753606898969818480106602520140451) * 10^40
        + 6439554206392789228938726914880782357903) * 10^40
        + 9403184112359627380104359126545223859734) * 10^40
        + 2769613989002427928887544788416852187904) * 10^40
        + 6263087518095786669849806481484746235831) * 10^40
        + 5839148737399505211911744781690365066037) : ℚ) /
        ((((((((4871 * 10^40
        + 7659315104606025147200408996023734269028) * 10^40
        + 8224330893135061231407877888946841612744) * 10^40
        + 4156179482148062401670989876663191453274) * 10^40
        + 9361997009934290183253537725993980116759) * 10^40
        + 1697904539460718883964967176616423492020) * 10^40
        + 6924729299185745215261580734292228090225) * 10^40
        + 423453899942074101460331283842958437764) * 10^40
        + 275001873072231092396026003867830321152)))

noncomputable def pairedN02700PlusP004Error2553 : ℝ := ((4385370515285168518352942979 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem pairedN02700PlusP004BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP004Center2553‖ ≤ pairedN02700PlusP004Error2553 := by
  have hx : |pairedN02700PlusPosition2553| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [pairedN02700PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02700PlusP004Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02700PlusP004Input2553]
  have hs : compactExp2547 pairedN02700PlusP004Input2553 8 =
      (pairedN02700PlusP004Center2553, ((4385370515285168518352942979 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02700PlusP004Input2553 8).2 : ℝ) =
      pairedN02700PlusP004Error2553
      := by
    rw [hs]
    norm_num [pairedN02700PlusP004Error2553]
  have h := compactExp_error2547 pairedN02700PlusP004Input2553 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      pairedN02700PlusPosition2553 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          pairedN02700PlusP004Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02700PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02700PlusP004Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02700PlusP004DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP004Factor2553 * embedPair2542 pairedN02700PlusP004Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP004Factor2553 : ℝ) * pairedN02700PlusP004Error2553 :=
            by
  have hx : |pairedN02700PlusPosition2553| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [pairedN02700PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) pairedN02700PlusPosition2553 = embedPair2542
          pairedN02700PlusP004Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02700PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02700PlusP004Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02700PlusP004BaseError2553
    (embedPair_magnitude2542 pairedN02700PlusP004Factor2553)

def pairedN02700PlusP005Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP005Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP005Error2553 : ℝ := 0

theorem pairedN02700PlusP005Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN02700PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem pairedN02700PlusP005BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP005Center2553‖ ≤ pairedN02700PlusP005Error2553 := by
  rw [pairedN02700PlusP005Exterior2553]
  norm_num [pairedN02700PlusP005Center2553, pairedN02700PlusP005Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP005DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP005Factor2553 * embedPair2542 pairedN02700PlusP005Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP005Factor2553 : ℝ) * pairedN02700PlusP005Error2553 :=
            by
  rw [pairedN02700PlusP005Exterior2553]
  norm_num [pairedN02700PlusP005Factor2553, pairedN02700PlusP005Center2553,
      pairedN02700PlusP005Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP006Input2553 : RatPair2542 := ((((-5479660975716824374691255046813) : ℚ) /
        9169574712713507276718080000000),
    ((0 : ℚ) /
        1))

def pairedN02700PlusP006Center2553 : RatPair2542 := (((440386906605911 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def pairedN02700PlusP006Factor2553 : RatPair2542 := ((((((572 * 10^40
        + 9736685104584173440087473394174857890754) * 10^40
        + 1790110940073970681389820663818342913116) * 10^40
        + 3915242146342375258795871208443756000883) : ℚ) /
        ((16205757207505281662197928304602393680 * 10^40
        + 5293276773758322903228484500985510207016) * 10^40
        + 9958614357229206230366969667550048007064)),
    ((0 : ℚ) /
        1))

noncomputable def pairedN02700PlusP006Error2553 : ℝ := ((2424345947741 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02700PlusP006BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP006Center2553‖ ≤ pairedN02700PlusP006Error2553 := by
  have hx : |pairedN02700PlusPosition2553| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [pairedN02700PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02700PlusP006Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02700PlusP006Input2553]
  have hs : compactExp2547 pairedN02700PlusP006Input2553 7 =
      (pairedN02700PlusP006Center2553, ((2424345947741 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02700PlusP006Input2553 7).2 : ℝ) =
      pairedN02700PlusP006Error2553
      := by
    rw [hs]
    norm_num [pairedN02700PlusP006Error2553]
  have h := compactExp_error2547 pairedN02700PlusP006Input2553 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      pairedN02700PlusPosition2553 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          pairedN02700PlusP006Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02700PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02700PlusP006Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02700PlusP006DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP006Factor2553 * embedPair2542 pairedN02700PlusP006Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP006Factor2553 : ℝ) * pairedN02700PlusP006Error2553 :=
            by
  have hx : |pairedN02700PlusPosition2553| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [pairedN02700PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) pairedN02700PlusPosition2553 = embedPair2542
          pairedN02700PlusP006Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02700PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02700PlusP006Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02700PlusP006BaseError2553
    (embedPair_magnitude2542 pairedN02700PlusP006Factor2553)

def pairedN02700PlusP007Input2553 : RatPair2542 := ((((-((2408 * 10^40
        + 369770750836432817481799749086268690782) * 10^40
        + 3306951315371206135663408401255839432267)) : ℚ) /
        ((3321 * 10^40
        + 230675766319980470452669177763665207837) * 10^40
        + 2488128168699824829291586200207360000000)),
    ((0 : ℚ) /
        1))

def pairedN02700PlusP007Center2553 : RatPair2542 := (((1282254638493795595923663161 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1))

def pairedN02700PlusP007Factor2553 : RatPair2542 :=
    (((((((((((((62577310175290924809139367860157750406 *
    10^40
        + 8075599408082455131088269167505482922831) * 10^40
        + 6630232061778822034017737112764219766971) * 10^40
        + 8628825923288488927057829293073874200920) * 10^40
        + 5229800633659361908235217053950415105574) * 10^40
        + 6720625777506157690040011927500464650372) * 10^40
        + 2727489859553899145547657380594261322778) * 10^40
        + 8368307663370614881372442876896050916508) * 10^40
        + 4641297618567392942532649152282042983023) * 10^40
        + 1135781052197643158183984867518581272720) * 10^40
        + 6049535293821782679449477488547419271203) : ℚ) /
        ((((((((((23409141915406051220036596658895703 * 10^40
        + 5270335118167222874082409338211804987319) * 10^40
        + 5727870704272825401770771079948171924854) * 10^40
        + 4571321504451550502214877018424552369447) * 10^40
        + 6206290265870300972842205837835135493640) * 10^40
        + 2551309011635991958953513571342238531357) * 10^40
        + 1512628219746634169991264988968568996042) * 10^40
        + 2805410045528479718635674533668031308830) * 10^40
        + 8069202893520658185802766719817315057560) * 10^40
        + 4425240148047063462268328888531805988781) * 10^40
        + 6331405806574261435595819908379354169624)),
    ((0 : ℚ) /
        1))

noncomputable def pairedN02700PlusP007Error2553 : ℝ := ((372637180338657148206451 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem pairedN02700PlusP007BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP007Center2553‖ ≤ pairedN02700PlusP007Error2553 := by
  have hx : |pairedN02700PlusPosition2553| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [pairedN02700PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02700PlusP007Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02700PlusP007Input2553]
  have hs : compactExp2547 pairedN02700PlusP007Input2553 6 =
      (pairedN02700PlusP007Center2553, ((372637180338657148206451 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02700PlusP007Input2553 6).2 : ℝ) =
      pairedN02700PlusP007Error2553
      := by
    rw [hs]
    norm_num [pairedN02700PlusP007Error2553]
  have h := compactExp_error2547 pairedN02700PlusP007Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      pairedN02700PlusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN02700PlusP007Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02700PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02700PlusP007Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02700PlusP007DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP007Factor2553 * embedPair2542 pairedN02700PlusP007Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP007Factor2553 : ℝ) * pairedN02700PlusP007Error2553 :=
            by
  have hx : |pairedN02700PlusPosition2553| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [pairedN02700PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) pairedN02700PlusPosition2553 = embedPair2542
          pairedN02700PlusP007Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02700PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02700PlusP007Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02700PlusP007BaseError2553
    (embedPair_magnitude2542 pairedN02700PlusP007Factor2553)

def pairedN02700PlusP008Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP008Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP008Error2553 : ℝ := 0

theorem pairedN02700PlusP008Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN02700PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨8, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨8, by omega⟩)
    (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx

theorem pairedN02700PlusP008BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP008Center2553‖ ≤ pairedN02700PlusP008Error2553 := by
  rw [pairedN02700PlusP008Exterior2553]
  norm_num [pairedN02700PlusP008Center2553, pairedN02700PlusP008Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP008DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP008Factor2553 * embedPair2542 pairedN02700PlusP008Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP008Factor2553 : ℝ) * pairedN02700PlusP008Error2553 :=
            by
  rw [pairedN02700PlusP008Exterior2553]
  norm_num [pairedN02700PlusP008Factor2553, pairedN02700PlusP008Center2553,
      pairedN02700PlusP008Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP009Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP009Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP009Error2553 : ℝ := 0

theorem pairedN02700PlusP009Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN02700PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨9, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨9, by omega⟩)
    (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx

theorem pairedN02700PlusP009BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP009Center2553‖ ≤ pairedN02700PlusP009Error2553 := by
  rw [pairedN02700PlusP009Exterior2553]
  norm_num [pairedN02700PlusP009Center2553, pairedN02700PlusP009Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP009DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP009Factor2553 * embedPair2542 pairedN02700PlusP009Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP009Factor2553 : ℝ) * pairedN02700PlusP009Error2553 :=
            by
  rw [pairedN02700PlusP009Exterior2553]
  norm_num [pairedN02700PlusP009Factor2553, pairedN02700PlusP009Center2553,
      pairedN02700PlusP009Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP010Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP010Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP010Error2553 : ℝ := 0

theorem pairedN02700PlusP010Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨10, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨10, by omega⟩)
    (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx

theorem pairedN02700PlusP010BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP010Center2553‖ ≤ pairedN02700PlusP010Error2553 := by
  rw [pairedN02700PlusP010Exterior2553]
  norm_num [pairedN02700PlusP010Center2553, pairedN02700PlusP010Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP010DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP010Factor2553 * embedPair2542 pairedN02700PlusP010Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP010Factor2553 : ℝ) * pairedN02700PlusP010Error2553 :=
            by
  rw [pairedN02700PlusP010Exterior2553]
  norm_num [pairedN02700PlusP010Factor2553, pairedN02700PlusP010Center2553,
      pairedN02700PlusP010Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP011Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP011Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP011Error2553 : ℝ := 0

theorem pairedN02700PlusP011Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨11, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨11, by omega⟩)
    (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx

theorem pairedN02700PlusP011BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP011Center2553‖ ≤ pairedN02700PlusP011Error2553 := by
  rw [pairedN02700PlusP011Exterior2553]
  norm_num [pairedN02700PlusP011Center2553, pairedN02700PlusP011Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP011DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP011Factor2553 * embedPair2542 pairedN02700PlusP011Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP011Factor2553 : ℝ) * pairedN02700PlusP011Error2553 :=
            by
  rw [pairedN02700PlusP011Exterior2553]
  norm_num [pairedN02700PlusP011Factor2553, pairedN02700PlusP011Center2553,
      pairedN02700PlusP011Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP012Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP012Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP012Error2553 : ℝ := 0

theorem pairedN02700PlusP012Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨12, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨12, by omega⟩)
    (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx

theorem pairedN02700PlusP012BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP012Center2553‖ ≤ pairedN02700PlusP012Error2553 := by
  rw [pairedN02700PlusP012Exterior2553]
  norm_num [pairedN02700PlusP012Center2553, pairedN02700PlusP012Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP012DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP012Factor2553 * embedPair2542 pairedN02700PlusP012Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP012Factor2553 : ℝ) * pairedN02700PlusP012Error2553 :=
            by
  rw [pairedN02700PlusP012Exterior2553]
  norm_num [pairedN02700PlusP012Factor2553, pairedN02700PlusP012Center2553,
      pairedN02700PlusP012Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP013Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP013Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP013Error2553 : ℝ := 0

theorem pairedN02700PlusP013Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨13, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨13, by omega⟩)
    (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx

theorem pairedN02700PlusP013BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP013Center2553‖ ≤ pairedN02700PlusP013Error2553 := by
  rw [pairedN02700PlusP013Exterior2553]
  norm_num [pairedN02700PlusP013Center2553, pairedN02700PlusP013Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP013DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP013Factor2553 * embedPair2542 pairedN02700PlusP013Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP013Factor2553 : ℝ) * pairedN02700PlusP013Error2553 :=
            by
  rw [pairedN02700PlusP013Exterior2553]
  norm_num [pairedN02700PlusP013Factor2553, pairedN02700PlusP013Center2553,
      pairedN02700PlusP013Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP014Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP014Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP014Error2553 : ℝ := 0

theorem pairedN02700PlusP014Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨14, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨14, by omega⟩)
    (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx

theorem pairedN02700PlusP014BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP014Center2553‖ ≤ pairedN02700PlusP014Error2553 := by
  rw [pairedN02700PlusP014Exterior2553]
  norm_num [pairedN02700PlusP014Center2553, pairedN02700PlusP014Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP014DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP014Factor2553 * embedPair2542 pairedN02700PlusP014Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP014Factor2553 : ℝ) * pairedN02700PlusP014Error2553 :=
            by
  rw [pairedN02700PlusP014Exterior2553]
  norm_num [pairedN02700PlusP014Factor2553, pairedN02700PlusP014Center2553,
      pairedN02700PlusP014Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP015Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP015Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP015Error2553 : ℝ := 0

theorem pairedN02700PlusP015Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨15, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨15, by omega⟩)
    (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx

theorem pairedN02700PlusP015BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP015Center2553‖ ≤ pairedN02700PlusP015Error2553 := by
  rw [pairedN02700PlusP015Exterior2553]
  norm_num [pairedN02700PlusP015Center2553, pairedN02700PlusP015Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP015DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP015Factor2553 * embedPair2542 pairedN02700PlusP015Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP015Factor2553 : ℝ) * pairedN02700PlusP015Error2553 :=
            by
  rw [pairedN02700PlusP015Exterior2553]
  norm_num [pairedN02700PlusP015Factor2553, pairedN02700PlusP015Center2553,
      pairedN02700PlusP015Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP016Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP016Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP016Error2553 : ℝ := 0

theorem pairedN02700PlusP016Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨16, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨16, by omega⟩)
    (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx

theorem pairedN02700PlusP016BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP016Center2553‖ ≤ pairedN02700PlusP016Error2553 := by
  rw [pairedN02700PlusP016Exterior2553]
  norm_num [pairedN02700PlusP016Center2553, pairedN02700PlusP016Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP016DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP016Factor2553 * embedPair2542 pairedN02700PlusP016Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP016Factor2553 : ℝ) * pairedN02700PlusP016Error2553 :=
            by
  rw [pairedN02700PlusP016Exterior2553]
  norm_num [pairedN02700PlusP016Factor2553, pairedN02700PlusP016Center2553,
      pairedN02700PlusP016Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP017Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP017Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP017Error2553 : ℝ := 0

theorem pairedN02700PlusP017Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨17, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨17, by omega⟩)
    (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx

theorem pairedN02700PlusP017BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP017Center2553‖ ≤ pairedN02700PlusP017Error2553 := by
  rw [pairedN02700PlusP017Exterior2553]
  norm_num [pairedN02700PlusP017Center2553, pairedN02700PlusP017Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP017DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP017Factor2553 * embedPair2542 pairedN02700PlusP017Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP017Factor2553 : ℝ) * pairedN02700PlusP017Error2553 :=
            by
  rw [pairedN02700PlusP017Exterior2553]
  norm_num [pairedN02700PlusP017Factor2553, pairedN02700PlusP017Center2553,
      pairedN02700PlusP017Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP018Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP018Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP018Error2553 : ℝ := 0

theorem pairedN02700PlusP018Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨18, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨18, by omega⟩)
    (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx

theorem pairedN02700PlusP018BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP018Center2553‖ ≤ pairedN02700PlusP018Error2553 := by
  rw [pairedN02700PlusP018Exterior2553]
  norm_num [pairedN02700PlusP018Center2553, pairedN02700PlusP018Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP018DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP018Factor2553 * embedPair2542 pairedN02700PlusP018Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP018Factor2553 : ℝ) * pairedN02700PlusP018Error2553 :=
            by
  rw [pairedN02700PlusP018Exterior2553]
  norm_num [pairedN02700PlusP018Factor2553, pairedN02700PlusP018Center2553,
      pairedN02700PlusP018Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP019Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP019Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP019Error2553 : ℝ := 0

theorem pairedN02700PlusP019Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨19, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨19, by omega⟩)
    (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx

theorem pairedN02700PlusP019BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP019Center2553‖ ≤ pairedN02700PlusP019Error2553 := by
  rw [pairedN02700PlusP019Exterior2553]
  norm_num [pairedN02700PlusP019Center2553, pairedN02700PlusP019Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP019DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP019Factor2553 * embedPair2542 pairedN02700PlusP019Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP019Factor2553 : ℝ) * pairedN02700PlusP019Error2553 :=
            by
  rw [pairedN02700PlusP019Exterior2553]
  norm_num [pairedN02700PlusP019Factor2553, pairedN02700PlusP019Center2553,
      pairedN02700PlusP019Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP020Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP020Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP020Error2553 : ℝ := 0

theorem pairedN02700PlusP020Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨20, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨20, by omega⟩)
    (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx

theorem pairedN02700PlusP020BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP020Center2553‖ ≤ pairedN02700PlusP020Error2553 := by
  rw [pairedN02700PlusP020Exterior2553]
  norm_num [pairedN02700PlusP020Center2553, pairedN02700PlusP020Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP020DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP020Factor2553 * embedPair2542 pairedN02700PlusP020Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP020Factor2553 : ℝ) * pairedN02700PlusP020Error2553 :=
            by
  rw [pairedN02700PlusP020Exterior2553]
  norm_num [pairedN02700PlusP020Factor2553, pairedN02700PlusP020Center2553,
      pairedN02700PlusP020Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP021Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP021Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP021Error2553 : ℝ := 0

theorem pairedN02700PlusP021Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨21, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨21, by omega⟩)
    (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx

theorem pairedN02700PlusP021BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP021Center2553‖ ≤ pairedN02700PlusP021Error2553 := by
  rw [pairedN02700PlusP021Exterior2553]
  norm_num [pairedN02700PlusP021Center2553, pairedN02700PlusP021Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP021DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP021Factor2553 * embedPair2542 pairedN02700PlusP021Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP021Factor2553 : ℝ) * pairedN02700PlusP021Error2553 :=
            by
  rw [pairedN02700PlusP021Exterior2553]
  norm_num [pairedN02700PlusP021Factor2553, pairedN02700PlusP021Center2553,
      pairedN02700PlusP021Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP022Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP022Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP022Error2553 : ℝ := 0

theorem pairedN02700PlusP022Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨22, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨22, by omega⟩)
    (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx

theorem pairedN02700PlusP022BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP022Center2553‖ ≤ pairedN02700PlusP022Error2553 := by
  rw [pairedN02700PlusP022Exterior2553]
  norm_num [pairedN02700PlusP022Center2553, pairedN02700PlusP022Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP022DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP022Factor2553 * embedPair2542 pairedN02700PlusP022Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP022Factor2553 : ℝ) * pairedN02700PlusP022Error2553 :=
            by
  rw [pairedN02700PlusP022Exterior2553]
  norm_num [pairedN02700PlusP022Factor2553, pairedN02700PlusP022Center2553,
      pairedN02700PlusP022Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP023Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP023Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP023Error2553 : ℝ := 0

theorem pairedN02700PlusP023Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨23, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨23, by omega⟩)
    (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx

theorem pairedN02700PlusP023BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP023Center2553‖ ≤ pairedN02700PlusP023Error2553 := by
  rw [pairedN02700PlusP023Exterior2553]
  norm_num [pairedN02700PlusP023Center2553, pairedN02700PlusP023Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP023DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP023Factor2553 * embedPair2542 pairedN02700PlusP023Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP023Factor2553 : ℝ) * pairedN02700PlusP023Error2553 :=
            by
  rw [pairedN02700PlusP023Exterior2553]
  norm_num [pairedN02700PlusP023Factor2553, pairedN02700PlusP023Center2553,
      pairedN02700PlusP023Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP024Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP024Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP024Error2553 : ℝ := 0

theorem pairedN02700PlusP024Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨24, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨24, by omega⟩)
    (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx

theorem pairedN02700PlusP024BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP024Center2553‖ ≤ pairedN02700PlusP024Error2553 := by
  rw [pairedN02700PlusP024Exterior2553]
  norm_num [pairedN02700PlusP024Center2553, pairedN02700PlusP024Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP024DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP024Factor2553 * embedPair2542 pairedN02700PlusP024Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP024Factor2553 : ℝ) * pairedN02700PlusP024Error2553 :=
            by
  rw [pairedN02700PlusP024Exterior2553]
  norm_num [pairedN02700PlusP024Factor2553, pairedN02700PlusP024Center2553,
      pairedN02700PlusP024Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP025Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP025Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP025Error2553 : ℝ := 0

theorem pairedN02700PlusP025Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨25, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨25, by omega⟩)
    (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx

theorem pairedN02700PlusP025BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP025Center2553‖ ≤ pairedN02700PlusP025Error2553 := by
  rw [pairedN02700PlusP025Exterior2553]
  norm_num [pairedN02700PlusP025Center2553, pairedN02700PlusP025Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP025DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP025Factor2553 * embedPair2542 pairedN02700PlusP025Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP025Factor2553 : ℝ) * pairedN02700PlusP025Error2553 :=
            by
  rw [pairedN02700PlusP025Exterior2553]
  norm_num [pairedN02700PlusP025Factor2553, pairedN02700PlusP025Center2553,
      pairedN02700PlusP025Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP026Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP026Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP026Error2553 : ℝ := 0

theorem pairedN02700PlusP026Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨26, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨26, by omega⟩)
    (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx

theorem pairedN02700PlusP026BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP026Center2553‖ ≤ pairedN02700PlusP026Error2553 := by
  rw [pairedN02700PlusP026Exterior2553]
  norm_num [pairedN02700PlusP026Center2553, pairedN02700PlusP026Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP026DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP026Factor2553 * embedPair2542 pairedN02700PlusP026Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP026Factor2553 : ℝ) * pairedN02700PlusP026Error2553 :=
            by
  rw [pairedN02700PlusP026Exterior2553]
  norm_num [pairedN02700PlusP026Factor2553, pairedN02700PlusP026Center2553,
      pairedN02700PlusP026Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP027Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP027Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP027Error2553 : ℝ := 0

theorem pairedN02700PlusP027Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨27, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨27, by omega⟩)
    (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx

theorem pairedN02700PlusP027BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP027Center2553‖ ≤ pairedN02700PlusP027Error2553 := by
  rw [pairedN02700PlusP027Exterior2553]
  norm_num [pairedN02700PlusP027Center2553, pairedN02700PlusP027Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP027DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP027Factor2553 * embedPair2542 pairedN02700PlusP027Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP027Factor2553 : ℝ) * pairedN02700PlusP027Error2553 :=
            by
  rw [pairedN02700PlusP027Exterior2553]
  norm_num [pairedN02700PlusP027Factor2553, pairedN02700PlusP027Center2553,
      pairedN02700PlusP027Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP028Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP028Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP028Error2553 : ℝ := 0

theorem pairedN02700PlusP028Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨28, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨28, by omega⟩)
    (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx

theorem pairedN02700PlusP028BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP028Center2553‖ ≤ pairedN02700PlusP028Error2553 := by
  rw [pairedN02700PlusP028Exterior2553]
  norm_num [pairedN02700PlusP028Center2553, pairedN02700PlusP028Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP028DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP028Factor2553 * embedPair2542 pairedN02700PlusP028Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP028Factor2553 : ℝ) * pairedN02700PlusP028Error2553 :=
            by
  rw [pairedN02700PlusP028Exterior2553]
  norm_num [pairedN02700PlusP028Factor2553, pairedN02700PlusP028Center2553,
      pairedN02700PlusP028Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

def pairedN02700PlusP029Center2553 : RatPair2542 := (0, 0)

def pairedN02700PlusP029Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02700PlusP029Error2553 : ℝ := 0

theorem pairedN02700PlusP029Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN02700PlusPosition2553 = 0
        := by
  have hx : storedWidth ⟨29, by omega⟩ ^ 2 ≤ |pairedN02700PlusPosition2553| := by
    norm_num [storedWidth, pairedN02700PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨29, by omega⟩)
    (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx

theorem pairedN02700PlusP029BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP029Center2553‖ ≤ pairedN02700PlusP029Error2553 := by
  rw [pairedN02700PlusP029Exterior2553]
  norm_num [pairedN02700PlusP029Center2553, pairedN02700PlusP029Error2553,
      pairedN02700PlusZero2553]

theorem pairedN02700PlusP029DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN02700PlusPosition2553 -
      embedPair2542 pairedN02700PlusP029Factor2553 * embedPair2542 pairedN02700PlusP029Center2553‖
          ≤
        (pairMagnitude2542 pairedN02700PlusP029Factor2553 : ℝ) * pairedN02700PlusP029Error2553 :=
            by
  rw [pairedN02700PlusP029Exterior2553]
  norm_num [pairedN02700PlusP029Factor2553, pairedN02700PlusP029Center2553,
      pairedN02700PlusP029Error2553, pairedN02700PlusZero2553, pairMagnitude2542]

theorem pairedN02700PlusGrid2553 :
    -stripRadius2303 + (2700 : ℝ) * (2 * stripRadius2303 / 10240) =
      pairedN02700PlusPosition2553 := by
  norm_num [stripRadius2303, pairedN02700PlusPosition2553]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.pairedN02700PlusP000DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP001DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP002DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP003DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP004DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP005DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP006DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP007DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP008DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP009DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP010DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP011DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP012DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP013DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP014DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP015DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP016DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP017DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP018DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP019DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP020DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP021DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP022DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP023DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP024DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP025DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP026DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP027DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP028DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusP029DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02700PlusGrid2553
