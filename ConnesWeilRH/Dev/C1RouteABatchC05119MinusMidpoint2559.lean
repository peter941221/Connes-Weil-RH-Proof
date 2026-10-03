import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchC05119MinusMidpointPosition2559 : ℝ := (((-65536001) : ℝ) /
        102400000000)

theorem batchC05119MinusMidpointZero2559 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchC05119MinusMidpointP000Input2559 : RatPair2542 := ((((-((526555 * 10^40
        + 8416874957316511208463416532305144862326) * 10^40
        + 9455414103737957782005021812057173103077)) : ℚ) /
        ((561665 * 10^40
        + 5204615401596259359546075575030701463919) * 10^40
        + 9047602218941736342579897453772800000000)),
    ((362039942185747774262029 : ℚ) /
        461168601842738790400000000))

def batchC05119MinusMidpointP000Center2559 : RatPair2542 :=
    (((136762160995969260667145464348122061 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((3436402783073724993200643250380411 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP000Factor2559 : RatPair2542 := ((((-((((((((4967 * 10^40
        + 8701552045464125501256675936857180805471) * 10^40
        + 794090741940764926480790939455001063385) * 10^40
        + 8378316761231779643946575449443940700399) * 10^40
        + 6614189416201180579459996996623783948611) * 10^40
        + 1533548710886824418590896224314831273298) * 10^40
        + 8110358765447035805870671431064281473042) * 10^40
        + 41969348104482952498698775502116765332) * 10^40
        + 7799817572352237309762363647105735772235)) : ℚ) /
        ((((((((3 * 10^40
        + 2057686793453645853832099023368682584443) * 10^40
        + 5440858390501675271628047073308679587005) * 10^40
        + 1513069510408717658199897381730895785210) * 10^40
        + 1765320025484634949277469779219555022669) * 10^40
        + 7821280952039764869081162360272287237951) * 10^40
        + 7707246990041006361829070588070261039907) * 10^40
        + 859565785342992470324763599478722112557) * 10^40
        + 7586065775090471380160226829877569912832)),
    ((((((120 * 10^40
        + 3023266422026620467918210965838259452498) * 10^40
        + 5010918217295971853559262771415429853062) * 10^40
        + 488619268414315870333009483614168253372) * 10^40
        + 5998904261857437483615477016614963319823) : ℚ) /
        ((((3 * 10^40
        + 1011781693472714364753146591009322093985) * 10^40
        + 5597280945859674264716413246412442858283) * 10^40
        + 7411798469021794771778051689090114685404) * 10^40
        + 545894146172216270068548039023196635136)))

noncomputable def batchC05119MinusMidpointP000Error2559 : ℝ := ((12591520189929968232570901257005
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP000BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP000Center2559‖ ≤
          batchC05119MinusMidpointP000Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP000Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP000Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP000Input2559 5 =
      (batchC05119MinusMidpointP000Center2559, ((12591520189929968232570901257005 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP000Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP000Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP000Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP000Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP000Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP000Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP000DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP000Factor2559 * embedPair2542
          batchC05119MinusMidpointP000Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP000Factor2559 : ℝ) *
            batchC05119MinusMidpointP000Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
      (storedWidth ⟨0, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP000Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP000Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨0, by omega⟩) (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP000BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP000Factor2559)

def batchC05119MinusMidpointP001Input2559 : RatPair2542 := ((((-((674 * 10^40
        + 5235288709793656808750221777917767410387) * 10^40
        + 7466988077655638785145811064393352481311)) : ℚ) /
        ((719 * 10^40
        + 4994130785584412590035563316819680975485) * 10^40
        + 8958819876028164556647397385830400000000)),
    ((362039942185747774262029 : ℚ) /
        461168601842738790400000000))

def batchC05119MinusMidpointP001Center2559 : RatPair2542 :=
    (((136762270810936686122004299685086797 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((3436405542378323105726561142399955 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP001Factor2559 : RatPair2542 :=
    ((((-(((((((44479390434130002682098013956692 *
    10^40
        + 7300889170653433522132441796354613122967) * 10^40
        + 5167521522911640392903579575181397825698) * 10^40
        + 3223035844694970143458218879889311815279) * 10^40
        + 9848243315611694110951258899540606269152) * 10^40
        + 8021597936685636194420733795130176814145) * 10^40
        + 9988379406132437511901472642668441077303) * 10^40
        + 2438849449188470955438027963582705416745)) : ℚ) /
        (((((((28775418324532319786967952471 * 10^40
        + 7247443626522465508482203787428130133755) * 10^40
        + 3587965448109955141623234642302009442615) * 10^40
        + 3131429987758643614585588767372245872650) * 10^40
        + 6185919165191365775118962992303050726788) * 10^40
        + 6521124831663484534272997719416531149618) * 10^40
        + 7603540845108823723409040976099340983178) * 10^40
        + 4078516865497767906843283707414282502144)),
    (((((661390434537622336538761862026277410 * 10^40
        + 8744902776221558108393051652465949676604) * 10^40
        + 2010032436917326593383320443565101670850) * 10^40
        + 2616871839208675334156074828254998312909) : ℚ) /
        (((16963318756815341936648765708178539 * 10^40
        + 5105814919489435369552687615131382672370) * 10^40
        + 2794683902922656136241201367600925059266) * 10^40
        + 9128461603094105914686949958279378239488)))

noncomputable def batchC05119MinusMidpointP001Error2559 : ℝ := ((12591529984501871920947439696323
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP001BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP001Center2559‖ ≤
          batchC05119MinusMidpointP001Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP001Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP001Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP001Input2559 5 =
      (batchC05119MinusMidpointP001Center2559, ((12591529984501871920947439696323 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP001Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP001Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP001Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP001Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP001Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP001Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP001DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP001Factor2559 * embedPair2542
          batchC05119MinusMidpointP001Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP001Factor2559 : ℝ) *
            batchC05119MinusMidpointP001Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP001Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP001Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP001BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP001Factor2559)

def batchC05119MinusMidpointP002Input2559 : RatPair2542 := ((((-((17623 * 10^40
        + 7828840977132447850696713707942284416859) * 10^40
        + 4867311535974285399051535308949645560351)) : ℚ) /
        ((18798 * 10^40
        + 9018532842369922254306089281683396764734) * 10^40
        + 566069047467097906358358173286400000000)),
    (((-362039942185747774262029) : ℚ) /
        461168601842738790400000000))

def batchC05119MinusMidpointP002Center2559 : RatPair2542 :=
    (((136762327642202879604871336048569083 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-3436406970369222713141244702147797) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP002Factor2559 : RatPair2542 :=
    ((((-(((((((20701230055098321838716840187542659375
    * 10^40
        + 2563974774998552407965704189825862197632) * 10^40
        + 9285691771290220894051053364429028340038) * 10^40
        + 4030556911806955901055166217073590153772) * 10^40
        + 8594044369703594147611928464571674364954) * 10^40
        + 7647861690933420617225798908685189397027) * 10^40
        + 9623125889286417689592560077370103276493) * 10^40
        + 6381161545076396020300200278453920315945)) : ℚ) /
        (((((((13410031310565378882449342305679330 * 10^40
        + 401664902234481302814542192008003684139) * 10^40
        + 852905566929832024718753418406856746614) * 10^40
        + 7877434763023558242133004913500222975218) * 10^40
        + 278028831589967000503241012990574579820) * 10^40
        + 9446022210166289686110292446630587367471) * 10^40
        + 6913050450403786944441411779349472056112) * 10^40
        + 9930369338561747280442649102418060509184)),
    (((-(((452684940620325918136345931075944159269 * 10^40
        + 7323501218500537817902063997673466175468) * 10^40
        + 4155066632724912790863486611917400883025) * 10^40
        + 3926172089089342848845858457138210682829)) : ℚ) /
        (((11580168958424302231511249020634879878 * 10^40
        + 4210121338939055992415895206895249975204) * 10^40
        + 5290647308855873800588227128193473645967) * 10^40
        + 3600485467521501550732789319520829308928)))

noncomputable def batchC05119MinusMidpointP002Error2559 : ℝ := ((1573941881671618964777200380875 :
    ℝ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))

theorem batchC05119MinusMidpointP002BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP002Center2559‖ ≤
          batchC05119MinusMidpointP002Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP002Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP002Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP002Input2559 5 =
      (batchC05119MinusMidpointP002Center2559, ((1573941881671618964777200380875 : ℚ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP002Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP002Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP002Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP002Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP002Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP002Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP002DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP002Factor2559 * embedPair2542
          batchC05119MinusMidpointP002Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP002Factor2559 : ℝ) *
            batchC05119MinusMidpointP002Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP002Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP002Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP002BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP002Factor2559)

def batchC05119MinusMidpointP003Input2559 : RatPair2542 := ((((-((2327643 * 10^40
        + 3891523835322816685751821624774770640403) * 10^40
        + 8606999235573092198926223098678266853077)) : ℚ) /
        ((2482846 * 10^40
        + 636835275403096208616850176779124390100) * 10^40
        + 1635094399228984342579897453772800000000)),
    (((-362039942185747774262029) : ℚ) /
        461168601842738790400000000))

def batchC05119MinusMidpointP003Center2559 : RatPair2542 := (((68381179708103930777440198533101651
    : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-3436407768749990859891123297327487) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP003Factor2559 : RatPair2542 := ((((-((((((((5664850 * 10^40
        + 4068008015450758158328689417923025219068) * 10^40
        + 2868977485724734256454818488694619938216) * 10^40
        + 4066141312114324704879451002815600840109) * 10^40
        + 4245626320942975046461117336678339236687) * 10^40
        + 3422355770655447444982160811738410263715) * 10^40
        + 54170410099874703891082212046640922138) * 10^40
        + 5328098508372337444968986845838358370918) * 10^40
        + 621942269898493262476951829989082316705)) : ℚ) /
        ((((((((3672 * 10^40
        + 3287779048855716809537066613285847618482) * 10^40
        + 218250735350543419281472381851475990008) * 10^40
        + 5041395110736834555187824676417997903913) * 10^40
        + 7750167000640157995043893681458478203901) * 10^40
        + 4024468343049927224229673213608375348585) * 10^40
        + 758291010479280115838670104786290808681) * 10^40
        + 7786739498744472271716234221462351189179) * 10^40
        + 8167986996661568665726120489632709738496)),
    (((-((((2372 * 10^40
        + 3823761217010507969235046939936817216680) * 10^40
        + 2022460893865431161727252621090718626258) * 10^40
        + 1214570264054426764789898898127631187960) * 10^40
        + 619916699580326705950158916029025819823)) : ℚ) /
        ((((60 * 10^40
        + 5997423914069586177573697612318088952245) * 10^40
        + 2919711175873929275085381732187877864721) * 10^40
        + 3867841134428167041263241288726534050566) * 10^40
        + 6977279854411393674976068039023196635136)))

noncomputable def batchC05119MinusMidpointP003Error2559 : ℝ := ((12591537887346996280364717211719
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP003BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP003Center2559‖ ≤
          batchC05119MinusMidpointP003Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP003Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP003Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP003Input2559 5 =
      (batchC05119MinusMidpointP003Center2559, ((12591537887346996280364717211719 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP003Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP003Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP003Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP003Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP003Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP003Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP003DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP003Factor2559 * embedPair2542
          batchC05119MinusMidpointP003Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP003Factor2559 : ℝ) *
            batchC05119MinusMidpointP003Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP003Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP003Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP003BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP003Factor2559)

def batchC05119MinusMidpointP004Input2559 : RatPair2542 := ((((-((40439 * 10^40
        + 4886415768484529121149632256940668195244) * 10^40
        + 4039246029434479755813410723988708060351)) : ℚ) /
        ((43135 * 10^40
        + 9142560649053103021034874848280634595490) * 10^40
        + 6430360174760377906358358173286400000000)),
    ((362039942185747774262029 : ℚ) /
        461168601842738790400000000))

def batchC05119MinusMidpointP004Center2559 : RatPair2542 :=
    (((136762378297247928578380848286965651 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((3436408243171118466659019143140877 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP004Factor2559 : RatPair2542 :=
    ((((-(((((((573208786437650868782912357847935776736 *
    10^40
        + 4609498322892644772121257005269966189261) * 10^40
        + 8638407941377319305103322190840924945463) * 10^40
        + 5051547206530310857286911410298162422973) * 10^40
        + 2873087050741234520658328293252084851072) * 10^40
        + 4326440367822848146261532257141471700057) * 10^40
        + 6637358094013910535016460550602444205710) * 10^40
        + 4079038227190504026905065024547670315945)) : ℚ) /
        (((((((371754212938148354659147433803003664 * 10^40
        + 2275200296478229247172803947590264788504) * 10^40
        + 3744214461033644318096342279782433854401) * 10^40
        + 5958583646481080335765081213521094654813) * 10^40
        + 1710020537322352317460317036562216341031) * 10^40
        + 2349498502665640230877415161379248058499) * 10^40
        + 9282055604377216470126070923508582259216) * 10^40
        + 1932963425659604440429849102418060509184)),
    (((((2389007035043074871872167417891547643758 * 10^40
        + 7236104492767797321027563593852975195223) * 10^40
        + 3278685265703972074070710316226930157741) * 10^40
        + 4883898924073176759963956259872585682829) : ℚ) /
        (((60971650210417329220350949185436832144 * 10^40
        + 8736556519624530247202451315220016226237) * 10^40
        + 5263714786560620305229997810007518251734) * 10^40
        + 2222531371331146615743989319520829308928)))

noncomputable def batchC05119MinusMidpointP004Error2559 : ℝ := ((6295769785688491292762884595393 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05119MinusMidpointP004BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP004Center2559‖ ≤
          batchC05119MinusMidpointP004Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP004Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP004Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP004Input2559 5 =
      (batchC05119MinusMidpointP004Center2559, ((6295769785688491292762884595393 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP004Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP004Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP004Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP004Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP004Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP004Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP004DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP004Factor2559 * embedPair2542
          batchC05119MinusMidpointP004Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP004Factor2559 : ℝ) *
            batchC05119MinusMidpointP004Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP004Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP004Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP004BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP004Factor2559)

def batchC05119MinusMidpointP005Input2559 : RatPair2542 := ((((-((1920095 * 10^40
        + 7496352581759633290314478790859160102927) * 10^40
        + 2539341092657322179483309296034800559231)) : ℚ) /
        ((2048123 * 10^40
        + 8742869729198005596656856045052835367848) * 10^40
        + 8500538745902249027739692361318400000000)),
    ((0 : ℚ) /
        1))

def batchC05119MinusMidpointP005Center2559 : RatPair2542 := (((68402686328474302188562068800721635
    : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def batchC05119MinusMidpointP005Factor2559 : RatPair2542 := ((((-(((((((2780391266707600 * 10^40
        + 7361023748951381967796892253510356165871) * 10^40
        + 9804482579623666779801813722714425489995) * 10^40
        + 4841683661420979119658087685677036018232) * 10^40
        + 2011617332352060189272251750817722729233) * 10^40
        + 634785354036060430229403073949813099460) * 10^40
        + 5549720655142473474778117506038489061878) * 10^40
        + 2252022694925598510773953466277052551679)) : ℚ) /
        (((((((381562028472365 * 10^40
        + 3288857745265286343765659074927076935186) * 10^40
        + 4929907230223500698538879774404655532531) * 10^40
        + 5944632634235498873987618511562310899940) * 10^40
        + 8785582921849823998981820391103656243189) * 10^40
        + 5097150702519412338737296097699843035509) * 10^40
        + 9657396612605376501390068452082043853615) * 10^40
        + 6748809278368645956904186134891789793284)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusMidpointP005Error2559 : ℝ := ((6145676805409930006813700378995 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05119MinusMidpointP005BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP005Center2559‖ ≤
          batchC05119MinusMidpointP005Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP005Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP005Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP005Input2559 5 =
      (batchC05119MinusMidpointP005Center2559, ((6145676805409930006813700378995 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP005Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP005Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP005Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP005Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP005Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP005Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP005DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP005Factor2559 * embedPair2542
          batchC05119MinusMidpointP005Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP005Factor2559 : ℝ) *
            batchC05119MinusMidpointP005Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
      (storedWidth ⟨5, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP005Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP005Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨5, by omega⟩) (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP005BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP005Factor2559)

def batchC05119MinusMidpointP006Input2559 : RatPair2542 :=
    ((((-343593718641278647609865186028202667) : ℚ) /
        366503866542833823313644748800000000),
    ((0 : ℚ) /
        1))

def batchC05119MinusMidpointP006Center2559 : RatPair2542 :=
    (((136805478621947305623669532046630203 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC05119MinusMidpointP006Factor2559 : RatPair2542 := ((((-((12332812323064 * 10^40
        + 1466331700724791927336159468215672043178) * 10^40
        + 1667622585271636761567483869353243079111)) : ℚ) /
        ((3521251306724 * 10^40
        + 4693370084997631605252093003549209262592) * 10^40
        + 5503507844426412953730064522587027683556)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusMidpointP006Error2559 : ℝ := ((3072840708446992824887246168809 :
    ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchC05119MinusMidpointP006BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP006Center2559‖ ≤
          batchC05119MinusMidpointP006Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP006Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP006Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP006Input2559 5 =
      (batchC05119MinusMidpointP006Center2559, ((3072840708446992824887246168809 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP006Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP006Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP006Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP006Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP006Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP006Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP006DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP006Factor2559 * embedPair2542
          batchC05119MinusMidpointP006Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP006Factor2559 : ℝ) *
            batchC05119MinusMidpointP006Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP006Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP006Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP006BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP006Factor2559)

def batchC05119MinusMidpointP007Input2559 : RatPair2542 := ((((-((2327643 * 10^40
        + 3891523835322816685751821624774770640403) * 10^40
        + 8606999235573092198926223098678266853077)) : ℚ) /
        ((2482846 * 10^40
        + 636835275403096208616850176779124390100) * 10^40
        + 1635094399228984342579897453772800000000)),
    ((0 : ℚ) /
        1))

def batchC05119MinusMidpointP007Center2559 : RatPair2542 := (((4275172676912944600992035130672335
    : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    ((0 : ℚ) /
        1))

def batchC05119MinusMidpointP007Factor2559 : RatPair2542 := ((((-(((((((13515414317805544 * 10^40
        + 8125867969858230622948509026877690739929) * 10^40
        + 1438519655999143668881007200787887965971) * 10^40
        + 6140059859221526622467466071128277671980) * 10^40
        + 6294888260057971305016493211673050537795) * 10^40
        + 151225518506165326631505152879174549098) * 10^40
        + 4310530133447334304771309425691045551381) * 10^40
        + 1444969421423194466385657051808561394631)) : ℚ) /
        (((((((7416208906258483 * 10^40
        + 3261257857274600727317754924046118815847) * 10^40
        + 6658504879816333974591682343066044804670) * 10^40
        + 4438717811510267545593991221277134463629) * 10^40
        + 5379244147034486919892582866405560038351) * 10^40
        + 2508347560547665335700144395464900988818) * 10^40
        + 7245239649129439042870440457341473608717) * 10^40
        + 4376538314307222134457371792765754421476)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusMidpointP007Error2559 : ℝ := ((12291366927985645363408331551915
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP007BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP007Center2559‖ ≤
          batchC05119MinusMidpointP007Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP007Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP007Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP007Input2559 5 =
      (batchC05119MinusMidpointP007Center2559, ((12291366927985645363408331551915 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP007Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP007Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP007Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP007Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP007Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP007Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP007DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP007Factor2559 * embedPair2542
          batchC05119MinusMidpointP007Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP007Factor2559 : ℝ) *
            batchC05119MinusMidpointP007Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP007Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP007Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP007BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP007Factor2559)

def batchC05119MinusMidpointP008Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((260739661220379310273297 : ℚ) /
        922337203685477580800000000))

def batchC05119MinusMidpointP008Center2559 : RatPair2542 := (((17099976356006611273366776209573903
    : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((618777760838156604824734862446049 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC05119MinusMidpointP008Factor2559 : RatPair2542 := ((((-((((((((36377 * 10^40
        + 8281442221292574812651279412615925281189) * 10^40
        + 3007919330536949845247232759884401084796) * 10^40
        + 9077649812867061149626040967028195475681) * 10^40
        + 6506533717426897204996659481807190655242) * 10^40
        + 5641069705052739324928227539139871850373) * 10^40
        + 9148013218697425871880324148953567927252) * 10^40
        + 933951076009174738337565057826565765967) * 10^40
        + 9188011490003491890650820720190319321625)) : ℚ) /
        ((((((((176 * 10^40
        + 7650597932611857216123108522235001330676) * 10^40
        + 2995603703798729220364340520705620713238) * 10^40
        + 1683222371992684660937273555963223418543) * 10^40
        + 6796868141686061893975517692089446915147) * 10^40
        + 4074636760409811892766789992102483862821) * 10^40
        + 3984182999672869581816949171858772760434) * 10^40
        + 244185463758786313222522440801334292731) * 10^40
        + 3558326196962898406453921958530838953984)),
    ((((((186 * 10^40
        + 4212744481125462244765865511303973556301) * 10^40
        + 2394276145393130463743195439220711799673) * 10^40
        + 2300443423386677431234209717414586240382) * 10^40
        + 5059251460595904230249011668354228863739) : ℚ) /
        ((((13 * 10^40
        + 2953021700622203542444360811297452827283) * 10^40
        + 6351847415713310855718142994552323757401) * 10^40
        + 7072708926405941203928393311156439663553) * 10^40
        + 43993547069664560821896078046393270272)))

noncomputable def batchC05119MinusMidpointP008Error2559 : ℝ := ((12399208735942409701623662985241
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP008BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP008Center2559‖ ≤
          batchC05119MinusMidpointP008Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP008Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP008Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP008Input2559 5 =
      (batchC05119MinusMidpointP008Center2559, ((12399208735942409701623662985241 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP008Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP008Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP008Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP008Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP008Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP008Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP008DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP008Factor2559 * embedPair2542
          batchC05119MinusMidpointP008Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP008Factor2559 : ℝ) *
            batchC05119MinusMidpointP008Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP008Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP008Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP008BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP008Factor2559)

def batchC05119MinusMidpointP009Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((387788191040974601829711 : ℚ) /
        922337203685477580800000000))

def batchC05119MinusMidpointP009Center2559 : RatPair2542 := (((34198256724905201189125478272223919
    : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((230067360105540145878898492778927 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)))

def batchC05119MinusMidpointP009Factor2559 : RatPair2542 := ((((-((((((((79178 * 10^40
        + 9588800858587038137212878843852490507569) * 10^40
        + 5527780010142563719538286178150415023062) * 10^40
        + 4577997557392727418070739743625134352418) * 10^40
        + 6837669186948807157726008752641198939555) * 10^40
        + 3170917527012231456465522327443640006427) * 10^40
        + 5552648497075824246868271760387375616598) * 10^40
        + 8183354647839809449696244717719060345760) * 10^40
        + 1914457757413916708114411380805385297753)) : ℚ) /
        ((((((((176 * 10^40
        + 7650597932611857216123108522235001330676) * 10^40
        + 2995603703798729220364340520705620713238) * 10^40
        + 1683222371992684660937273555963223418543) * 10^40
        + 6796868141686061893975517692089446915147) * 10^40
        + 4074636760409811892766789992102483862821) * 10^40
        + 3984182999672869581816949171858772760434) * 10^40
        + 244185463758786313222522440801334292731) * 10^40
        + 3558326196962898406453921958530838953984)),
    ((((((92 * 10^40
        + 4190927346554275825477291341544906764861) * 10^40
        + 5759792317248563024966121891107404400591) * 10^40
        + 7735718248952038404615509519529772987884) * 10^40
        + 3307492681525414851554104001594960686519) : ℚ) /
        ((((4 * 10^40
        + 4317673900207401180814786937099150942427) * 10^40
        + 8783949138571103618572714331517441252467) * 10^40
        + 2357569642135313734642797770385479887851) * 10^40
        + 14664515689888186940632026015464423424)))

noncomputable def batchC05119MinusMidpointP009Error2559 : ℝ := ((12451858974451582232284083015425
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP009BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP009Center2559‖ ≤
          batchC05119MinusMidpointP009Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP009Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP009Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP009Input2559 5 =
      (batchC05119MinusMidpointP009Center2559, ((12451858974451582232284083015425 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP009Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP009Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP009Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP009Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP009Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP009Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP009DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP009Factor2559 * embedPair2542
          batchC05119MinusMidpointP009Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP009Factor2559 : ℝ) *
            batchC05119MinusMidpointP009Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP009Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP009Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP009BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP009Factor2559)

def batchC05119MinusMidpointP010Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((230684447942438333698521 : ℚ) /
        461168601842738790400000000))

def batchC05119MinusMidpointP010Center2559 : RatPair2542 :=
    (((136787882556443258287540068700487327 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((1094871848319122654056951391460757 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC05119MinusMidpointP010Factor2559 : RatPair2542 := ((((-((((((((27909 * 10^40
        + 4247336612054815642236248961963385155) * 10^40
        + 450154874394012809680472585584958170392) * 10^40
        + 9049719303107493636381599405365911577251) * 10^40
        + 4469612386898542031627505759531881855865) * 10^40
        + 8003474758144675905148458887835309177944) * 10^40
        + 660854224673818286037414380700434054098) * 10^40
        + 5122225784330056422722075884547975753491) * 10^40
        + 2748735633174869858890846884953107648105)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((6 * 10^40
        + 1086174472962103564386916029387005463381) * 10^40
        + 5884947217341154566355952926308226042002) * 10^40
        + 1906306160397410866128073410114229367343) * 10^40
        + 2918473338174746205380979628651576129001) : ℚ) /
        (((2462092994455966732267488163172175052357 * 10^40
        + 1043552729920616867698484129528746736248) * 10^40
        + 1797642757896406318591266542799193327102) * 10^40
        + 8334148028649438232607812890334192467968)))

noncomputable def batchC05119MinusMidpointP010Error2559 : ℝ := ((12482380700600170239926781193601
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP010BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP010Center2559‖ ≤
          batchC05119MinusMidpointP010Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP010Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP010Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP010Input2559 5 =
      (batchC05119MinusMidpointP010Center2559, ((12482380700600170239926781193601 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP010Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP010Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP010Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP010Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP010Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP010Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP010DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP010Factor2559 * embedPair2542
          batchC05119MinusMidpointP010Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP010Factor2559 : ℝ) *
            batchC05119MinusMidpointP010Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP010Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP010Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP010BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP010Factor2559)

def batchC05119MinusMidpointP011Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((255213677437476200797801 : ℚ) /
        461168601842738790400000000))

def batchC05119MinusMidpointP011Center2559 : RatPair2542 :=
    (((136783957352081345859799192558013457 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((2422561214143468626052226662456333 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP011Factor2559 : RatPair2542 := ((((-((((((((34100 * 10^40
        + 3609840272039851824128360550275208906509) * 10^40
        + 8619130060055138289669846102070092337568) * 10^40
        + 7851665354470007287294399892255819477176) * 10^40
        + 1928797053240597954908393327229940425096) * 10^40
        + 8565836387790540289542425113273226490380) * 10^40
        + 375181518762875808796923957877450461410) * 10^40
        + 1679768015006332666087756671189776604454) * 10^40
        + 4256890215689807448625293094928594539145)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((182 * 10^40
        + 4703567604589627698917946150207779834139) * 10^40
        + 521926813475162471931687355311942980831) * 10^40
        + 7510778909761055495105445920058597351573) * 10^40
        + 469784071790973715438177459009825576387) : ℚ) /
        ((((6 * 10^40
        + 6476510850311101771222180405648726413641) * 10^40
        + 8175923707856655427859071497276161878700) * 10^40
        + 8536354463202970601964196655578219831776) * 10^40
        + 5021996773534832280410948039023196635136)))

noncomputable def batchC05119MinusMidpointP011Error2559 : ℝ := ((6251371127616640133925710093375 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05119MinusMidpointP011BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP011Center2559‖ ≤
          batchC05119MinusMidpointP011Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP011Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP011Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP011Input2559 5 =
      (batchC05119MinusMidpointP011Center2559, ((6251371127616640133925710093375 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP011Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP011Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP011Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP011Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP011Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP011Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP011DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP011Factor2559 * embedPair2542
          batchC05119MinusMidpointP011Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP011Factor2559 : ℝ) *
            batchC05119MinusMidpointP011Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP011Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP011Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP011BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP011Factor2559)

def batchC05119MinusMidpointP012Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((5612399119318874813509 : ℚ) /
        9223372036854775808000000))

def batchC05119MinusMidpointP012Center2559 : RatPair2542 := (((68389737016141055831234464805734135
    : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((665923943880992283032758196912547 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchC05119MinusMidpointP012Factor2559 : RatPair2542 := ((((-((((((((10293 * 10^40
        + 321919147089624921014593025574340193418) * 10^40
        + 3962961134599473273567715620464490646513) * 10^40
        + 1515312773370613733806008207460153740067) * 10^40
        + 5707140635383996099205337159210723224570) * 10^40
        + 7579475590647808155003843814061365673240) * 10^40
        + 3386121449028136308703632059517234300491) * 10^40
        + 1308380377072700859560988009131937876159) * 10^40
        + 3391509256158670874172204209126420571969)) : ℚ) /
        ((((((((11 * 10^40
        + 478162370788241076007694282639687583167) * 10^40
        + 2687225231487420576272771282544101294577) * 10^40
        + 3855201398249542791308579597247701463658) * 10^40
        + 9799804258855378868373469855755590432196) * 10^40
        + 7129664797525613243297924374506405241426) * 10^40
        + 3374011437479554348863559323241173297527) * 10^40
        + 1265261591484924144576407652550083393295) * 10^40
        + 7097395387310181150403370122408177434624)),
    ((((((100 * 10^40
        + 3175534974110234081621537372676526986000) * 10^40
        + 6947478604479926581657890339901527113357) * 10^40
        + 6573369554920689080168212715559238601926) * 10^40
        + 5533163992957810739745727508708017364575) : ℚ) /
        ((((3 * 10^40
        + 3238255425155550885611090202824363206820) * 10^40
        + 9087961853928327713929535748638080939350) * 10^40
        + 4268177231601485300982098327789109915888) * 10^40
        + 2510998386767416140205474019511598317568)))

noncomputable def batchC05119MinusMidpointP012Error2559 : ℝ := ((391370055180045369260788741299 :
    ℝ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))

theorem batchC05119MinusMidpointP012BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP012Center2559‖ ≤
          batchC05119MinusMidpointP012Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP012Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP012Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP012Input2559 5 =
      (batchC05119MinusMidpointP012Center2559, ((391370055180045369260788741299 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP012Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP012Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP012Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP012Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP012Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP012Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP012DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP012Factor2559 * embedPair2542
          batchC05119MinusMidpointP012Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP012Factor2559 : ℝ) *
            batchC05119MinusMidpointP012Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP012Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP012Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP012BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP012Factor2559)

def batchC05119MinusMidpointP013Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((60754466143128272313291 : ℚ) /
        92233720368547758080000000))

def batchC05119MinusMidpointP013Center2559 : RatPair2542 :=
    (((136775018249796462607585370098805365 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((720857757298785014044251596810365 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchC05119MinusMidpointP013Factor2559 : RatPair2542 := ((((-((((((((48200 * 10^40
        + 5370971956142276806914953774530561879005) * 10^40
        + 8372972793598474377994545450579417902645) * 10^40
        + 5987972930922509266055470829625013782516) * 10^40
        + 975936691810120595712786260378122524417) * 10^40
        + 2684339783413041046946358333681565010441) * 10^40
        + 1755611297204661612856451059321219152915) * 10^40
        + 3875153962367775678314673488828074701502) * 10^40
        + 3006932331384071219254695945407390022601)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((72 * 10^40
        + 3961271932204708562328254692294399644498) * 10^40
        + 5497776944153921739311224568747560780157) * 10^40
        + 2118376846181408645059188470560994613645) * 10^40
        + 680691221971649018337718681805726161695) : ℚ) /
        ((((2 * 10^40
        + 2158836950103700590407393468549575471213) * 10^40
        + 9391974569285551809286357165758720626233) * 10^40
        + 6178784821067656867321398885192739943925) * 10^40
        + 5007332257844944093470316013007732211712)))

noncomputable def batchC05119MinusMidpointP013Error2559 : ℝ := ((3135769553132970998090987923461 :
    ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchC05119MinusMidpointP013BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP013Center2559‖ ≤
          batchC05119MinusMidpointP013Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP013Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP013Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP013Input2559 5 =
      (batchC05119MinusMidpointP013Center2559, ((3135769553132970998090987923461 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP013Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP013Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP013Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP013Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP013Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP013Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP013DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP013Factor2559 * embedPair2542
          batchC05119MinusMidpointP013Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP013Factor2559 : ℝ) *
            batchC05119MinusMidpointP013Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP013Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP013Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP013BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP013Factor2559)

def batchC05119MinusMidpointP014Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((346671309892138695845011 : ℚ) /
        461168601842738790400000000))

def batchC05119MinusMidpointP014Center2559 : RatPair2542 :=
    (((136765829141429829991955949031381651 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((3290557853845429299803069536889011 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP014Factor2559 : RatPair2542 := ((((-((((((((62695 * 10^40
        + 3827788534183220524191385119048079001072) * 10^40
        + 8825932395174143799297951393709742744091) * 10^40
        + 1753648640724942185196793965875920433343) * 10^40
        + 3575634152689594629276444410304531768089) * 10^40
        + 9404732458627828892508656658584807394594) * 10^40
        + 5777320489973661255251911212155403972090) * 10^40
        + 5449685544118141835542882748824348217533) * 10^40
        + 9808693468898288065329483075343511797025)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((247 * 10^40
        + 8599040215284584196658552945522366900099) * 10^40
        + 4061188717642043754566777755970981328010) * 10^40
        + 5993905151833285784520111028821741976702) * 10^40
        + 5474735315524568369596729384591409200657) : ℚ) /
        ((((6 * 10^40
        + 6476510850311101771222180405648726413641) * 10^40
        + 8175923707856655427859071497276161878700) * 10^40
        + 8536354463202970601964196655578219831776) * 10^40
        + 5021996773534832280410948039023196635136)))

noncomputable def batchC05119MinusMidpointP014Error2559 : ℝ := ((3144685848393798375435877127523 :
    ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchC05119MinusMidpointP014BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP014Center2559‖ ≤
          batchC05119MinusMidpointP014Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP014Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP014Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP014Input2559 5 =
      (batchC05119MinusMidpointP014Center2559, ((3144685848393798375435877127523 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP014Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP014Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP014Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP014Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP014Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP014Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP014DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP014Factor2559 * embedPair2542
          batchC05119MinusMidpointP014Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP014Factor2559 : ℝ) *
            batchC05119MinusMidpointP014Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP014Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP014Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP014BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP014Factor2559)

def batchC05119MinusMidpointP015Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((377408574479356852679047 : ℚ) /
        461168601842738790400000000))

def batchC05119MinusMidpointP015Center2559 : RatPair2542 := (((17094812486080834740673027395790147
    : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((1791123944574141378292463227302713 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC05119MinusMidpointP015Factor2559 : RatPair2542 := ((((-((((((((74256 * 10^40
        + 7358516023696086214753089854988510449174) * 10^40
        + 979921351892406853408771884609657171246) * 10^40
        + 2044445820676122241761667311806953159870) * 10^40
        + 7298776470380404541649748131309802416038) * 10^40
        + 9057974205536611808119151437515375193616) * 10^40
        + 1897108280260510833365514380981997771646) * 10^40
        + 9912884190202419656276907684044828422217) * 10^40
        + 1828038397871527074537495069350659907497)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((269 * 10^40
        + 8361542420690763085969480552713788277577) * 10^40
        + 1689332266585053744941356685516332958680) * 10^40
        + 4072076726209022112120321676249115435153) * 10^40
        + 4338304831306729715462858535357267438989) : ℚ) /
        ((((6 * 10^40
        + 6476510850311101771222180405648726413641) * 10^40
        + 8175923707856655427859071497276161878700) * 10^40
        + 8536354463202970601964196655578219831776) * 10^40
        + 5021996773534832280410948039023196635136)))

noncomputable def batchC05119MinusMidpointP015Error2559 : ℝ := ((12604315133089072186671904218425
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP015BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP015Center2559‖ ≤
          batchC05119MinusMidpointP015Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP015Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP015Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP015Input2559 5 =
      (batchC05119MinusMidpointP015Center2559, ((12604315133089072186671904218425 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP015Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP015Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP015Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP015Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP015Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP015Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP015DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP015Factor2559 * embedPair2542
          batchC05119MinusMidpointP015Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP015Factor2559 : ℝ) *
            batchC05119MinusMidpointP015Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP015Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP015Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP015BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP015Factor2559)

def batchC05119MinusMidpointP016Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((199810861117846303095609 : ℚ) /
        230584300921369395200000000))

def batchC05119MinusMidpointP016Center2559 : RatPair2542 :=
    (((136752815952712873586289149122719031 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((3793035820516349808332200313791099 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP016Factor2559 : RatPair2542 := ((((-((((((((20805 * 10^40
        + 7164252485305624878648711139141041748751) * 10^40
        + 2531761825800349785266535747789100209541) * 10^40
        + 1977401996184104120844633460273039643157) * 10^40
        + 897557476689625926519744376006571295216) * 10^40
        + 9317596051464658219215454128875985071140) * 10^40
        + 1112880487653117255406085766764320886784) * 10^40
        + 2760958016132972201693049559582429853866) * 10^40
        + 4038489595660650561137818655788293083433)) : ℚ) /
        ((((((((11 * 10^40
        + 478162370788241076007694282639687583167) * 10^40
        + 2687225231487420576272771282544101294577) * 10^40
        + 3855201398249542791308579597247701463658) * 10^40
        + 9799804258855378868373469855755590432196) * 10^40
        + 7129664797525613243297924374506405241426) * 10^40
        + 3374011437479554348863559323241173297527) * 10^40
        + 1265261591484924144576407652550083393295) * 10^40
        + 7097395387310181150403370122408177434624)),
    ((((((47 * 10^40
        + 6196514738387112964233036970174594093730) * 10^40
        + 15150062345114862660640431757174385480) * 10^40
        + 5850359681863681509891460050043851002406) * 10^40
        + 9942687223000722946181349068756621135761) : ℚ) /
        ((((1 * 10^40
        + 1079418475051850295203696734274787735606) * 10^40
        + 9695987284642775904643178582879360313116) * 10^40
        + 8089392410533828433660699442596369971962) * 10^40
        + 7503666128922472046735158006503866105856)))

noncomputable def batchC05119MinusMidpointP016Error2559 : ℝ := ((3155701083892402428876114409053 :
    ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchC05119MinusMidpointP016BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP016Center2559‖ ≤
          batchC05119MinusMidpointP016Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP016Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP016Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP016Input2559 5 =
      (batchC05119MinusMidpointP016Center2559, ((3155701083892402428876114409053 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP016Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP016Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP016Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP016Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP016Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP016Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP016DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP016Factor2559 * embedPair2542
          batchC05119MinusMidpointP016Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP016Factor2559 : ℝ) *
            batchC05119MinusMidpointP016Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP016Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP016Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP016BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP016Factor2559)

def batchC05119MinusMidpointP017Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((442769373018475956606027 : ℚ) /
        461168601842738790400000000))

def batchC05119MinusMidpointP017Center2559 : RatPair2542 :=
    (((136740846819600884579669206042705675 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((525306499679106905092657724724765 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)))

def batchC05119MinusMidpointP017Factor2559 : RatPair2542 := ((((-((((((((102103 * 10^40
        + 9916254155149163099931689371486177596376) * 10^40
        + 6676578027432451180988235895644004165548) * 10^40
        + 3694901366032541511737258578324422495516) * 10^40
        + 2636034423070937341119046187020627305970) * 10^40
        + 4093987088925771517788323496524392099744) * 10^40
        + 5472114283296336810077787656488051266520) * 10^40
        + 406173961014535425661180351414418451254) * 10^40
        + 9784231253423769993727862948827292963377)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((105 * 10^40
        + 5224080836851257633169321235869676918496) * 10^40
        + 3962600435323977917127228393204741257178) * 10^40
        + 6034040452137721096001337571488333328257) * 10^40
        + 461366287408354701686402842754194944083) : ℚ) /
        ((((2 * 10^40
        + 2158836950103700590407393468549575471213) * 10^40
        + 9391974569285551809286357165758720626233) * 10^40
        + 6178784821067656867321398885192739943925) * 10^40
        + 5007332257844944093470316013007732211712)))

noncomputable def batchC05119MinusMidpointP017Error2559 : ℝ := ((6329370053973302602755311676433 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05119MinusMidpointP017BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP017Center2559‖ ≤
          batchC05119MinusMidpointP017Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP017Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP017Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP017Input2559 5 =
      (batchC05119MinusMidpointP017Center2559, ((6329370053973302602755311676433 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP017Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP017Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP017Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP017Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP017Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP017Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP017DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP017Factor2559 * embedPair2542
          batchC05119MinusMidpointP017Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP017Factor2559 : ℝ) *
            batchC05119MinusMidpointP017Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP017Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP017Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP017BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP017Factor2559)

def batchC05119MinusMidpointP018Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((114770645411675231749613 : ℚ) /
        115292150460684697600000000))

def batchC05119MinusMidpointP018Center2559 : RatPair2542 := (((4273000069504393176468086738008447
    : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    ((4357233926713443633251025145290995 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP018Factor2559 : RatPair2542 := ((((-((((((((6859 * 10^40
        + 1515033417456605029551334736578733380642) * 10^40
        + 8867175540483591588735066812674026029463) * 10^40
        + 2529071483640981113637981700328448559898) * 10^40
        + 150304123239695200571083211479449030298) * 10^40
        + 2253281750381809707308541302727905832271) * 10^40
        + 7359724094659048723850532006085972408512) * 10^40
        + 1034072809803179355751191533498028385522) * 10^40
        + 2901714539996118035545819974579535128097)) : ℚ) /
        ((((((((2 * 10^40
        + 7619540592697060269001923570659921895791) * 10^40
        + 8171806307871855144068192820636025323644) * 10^40
        + 3463800349562385697827144899311925365914) * 10^40
        + 7449951064713844717093367463938897608049) * 10^40
        + 1782416199381403310824481093626601310356) * 10^40
        + 5843502859369888587215889830810293324381) * 10^40
        + 7816315397871231036144101913137520848323) * 10^40
        + 9274348846827545287600842530602044358656)),
    ((((((82 * 10^40
        + 576734921547046017980870348705271787797) * 10^40
        + 360569456265983293929217861086520882981) * 10^40
        + 3258752554284788475492304949114017656154) * 10^40
        + 4913025539568331133725808067892824536431) : ℚ) /
        ((((1 * 10^40
        + 6619127712577775442805545101412181603410) * 10^40
        + 4543980926964163856964767874319040469675) * 10^40
        + 2134088615800742650491049163894554957944) * 10^40
        + 1255499193383708070102737009755799158784)))

noncomputable def batchC05119MinusMidpointP018Error2559 : ℝ := ((6336167040453098875138075965889 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05119MinusMidpointP018BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP018Center2559‖ ≤
          batchC05119MinusMidpointP018Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP018Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP018Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP018Input2559 5 =
      (batchC05119MinusMidpointP018Center2559, ((6336167040453098875138075965889 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP018Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP018Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP018Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP018Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP018Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP018Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP018DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP018Factor2559 * embedPair2542
          batchC05119MinusMidpointP018Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP018Factor2559 : ℝ) *
            batchC05119MinusMidpointP018Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP018Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP018Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP018BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP018Factor2559)

def batchC05119MinusMidpointP019Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((24428249467783476683391 : ℚ) /
        23058430092136939520000000))

def batchC05119MinusMidpointP019Center2559 : RatPair2542 := (((4272712571213591104948287367195111
    : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    ((4636952699420616532621441121532253 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP019Factor2559 : RatPair2542 := ((((-((((((((7766 * 10^40
        + 2339964835537328456244170185502335061169) * 10^40
        + 249470786863699165632301182759804098473) * 10^40
        + 159717528519164682481499359965295682472) * 10^40
        + 6066726269970841653785347201022704212046) * 10^40
        + 907309063469557643584989318055099749027) * 10^40
        + 3774793659241007400647496156675229323674) * 10^40
        + 9607966135444869709734855771097532008501) * 10^40
        + 3469461198249566741747027211952717012561)) : ℚ) /
        ((((((((2 * 10^40
        + 7619540592697060269001923570659921895791) * 10^40
        + 8171806307871855144068192820636025323644) * 10^40
        + 3463800349562385697827144899311925365914) * 10^40
        + 7449951064713844717093367463938897608049) * 10^40
        + 1782416199381403310824481093626601310356) * 10^40
        + 5843502859369888587215889830810293324381) * 10^40
        + 7816315397871231036144101913137520848323) * 10^40
        + 9274348846827545287600842530602044358656)),
    ((((((9 * 10^40
        + 7030488338148452799322899573453681918748) * 10^40
        + 5780966393167004644630219078318742172628) * 10^40
        + 4618840404842006252064120181246246619362) * 10^40
        + 3968122979005580040150456686950097592065) : ℚ) /
        (((1846569745841975049200616122379131289267 * 10^40
        + 8282664547440462650773863097146560052186) * 10^40
        + 1348232068422304738943449907099394995327) * 10^40
        + 1250611021487078674455859667750644350976)))

noncomputable def batchC05119MinusMidpointP019Error2559 : ℝ := ((6348456191165250210607674126873 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05119MinusMidpointP019BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP019Center2559‖ ≤
          batchC05119MinusMidpointP019Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP019Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP019Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP019Input2559 5 =
      (batchC05119MinusMidpointP019Center2559, ((6348456191165250210607674126873 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP019Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP019Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP019Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP019Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP019Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP019Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP019DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP019Factor2559 * embedPair2542
          batchC05119MinusMidpointP019Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP019Factor2559 : ℝ) *
            batchC05119MinusMidpointP019Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP019Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP019Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP019BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP019Factor2559)

def batchC05119MinusMidpointP020Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((520624750538575899551419 : ℚ) /
        461168601842738790400000000))

def batchC05119MinusMidpointP020Center2559 : RatPair2542 :=
    (((136716148638125792672224384538601989 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((1235275609180389338053887241018919 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchC05119MinusMidpointP020Factor2559 : RatPair2542 := ((((-((((((((141066 * 10^40
        + 7391304855971096450630183373507279793299) * 10^40
        + 4872772237865823655826191327007533818808) * 10^40
        + 4882446215472306665908148743167660565585) * 10^40
        + 3859504570405929453322874999156972745023) * 10^40
        + 3705783006248474798722111265633452579335) * 10^40
        + 2965606554033331716629549592585254943372) * 10^40
        + 2901037795727175124385805199125109774620) * 10^40
        + 9404640448962096030032355137012577426385)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((372 * 10^40
        + 2315548404423775549133832057342895532342) * 10^40
        + 4619541539550852735877734440706201236341) * 10^40
        + 5765341851702427972067219286418346424389) * 10^40
        + 1653072243263586762726874265194775799753) : ℚ) /
        ((((6 * 10^40
        + 6476510850311101771222180405648726413641) * 10^40
        + 8175923707856655427859071497276161878700) * 10^40
        + 8536354463202970601964196655578219831776) * 10^40
        + 5021996773534832280410948039023196635136)))

noncomputable def batchC05119MinusMidpointP020Error2559 : ℝ := ((12723654311678953738038054392967
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP020BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP020Center2559‖ ≤
          batchC05119MinusMidpointP020Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP020Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP020Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP020Input2559 5 =
      (batchC05119MinusMidpointP020Center2559, ((12723654311678953738038054392967 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP020Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP020Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP020Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP020Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP020Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP020Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP020DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP020Factor2559 * embedPair2542
          batchC05119MinusMidpointP020Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP020Factor2559 : ℝ) *
            batchC05119MinusMidpointP020Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP020Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP020Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP020BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP020Factor2559)

def batchC05119MinusMidpointP021Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((547379874475946380671387 : ℚ) /
        461168601842738790400000000))

def batchC05119MinusMidpointP021Center2559 : RatPair2542 :=
    (((136706739834176938123286846861060005 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((5194908627005977527711348973433625 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP021Factor2559 : RatPair2542 := ((((-((((((((155910 * 10^40
        + 2647623011306686530384416662498946006974) * 10^40
        + 1473611521312142599526899394777390947355) * 10^40
        + 6354781074083811620039349897961859076340) * 10^40
        + 38028068297456441652249907466629335733) * 10^40
        + 5361100495999838487647495295775999382813) * 10^40
        + 2703302677420623695833700597849469585693) * 10^40
        + 2941005750006034207277207941478033322759) * 10^40
        + 5073033222524919072275003180545007909137)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((130 * 10^40
        + 4535634374984184508733185846333263360531) * 10^40
        + 6984242043435723954897026668764401439539) * 10^40
        + 1326668546506270979911569498419503849453) * 10^40
        + 5765704895443290890522196126579399263523) : ℚ) /
        ((((2 * 10^40
        + 2158836950103700590407393468549575471213) * 10^40
        + 9391974569285551809286357165758720626233) * 10^40
        + 6178784821067656867321398885192739943925) * 10^40
        + 5007332257844944093470316013007732211712)))

noncomputable def batchC05119MinusMidpointP021Error2559 : ℝ := ((12745983409194538609818397400611
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP021BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP021Center2559‖ ≤
          batchC05119MinusMidpointP021Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP021Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP021Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP021Input2559 5 =
      (batchC05119MinusMidpointP021Center2559, ((12745983409194538609818397400611 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP021Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP021Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP021Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP021Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP021Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP021Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP021DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP021Factor2559 * embedPair2542
          batchC05119MinusMidpointP021Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP021Factor2559 : ℝ) *
            batchC05119MinusMidpointP021Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP021Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP021Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP021BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP021Factor2559)

def batchC05119MinusMidpointP022Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((112214826711468142236233 : ℚ) /
        92233720368547758080000000))

def batchC05119MinusMidpointP022Center2559 : RatPair2542 :=
    (((136701741757531233807626351245261917 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((5324809122355666700845106602326383 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP022Factor2559 : RatPair2542 := ((((-((((((((163795 * 10^40
        + 4733157954965628827276990554321230954059) * 10^40
        + 4499903737752806782517388009081000166919) * 10^40
        + 7958850834254238488585332951743010127539) * 10^40
        + 3058234513205305685154842019981330004411) * 10^40
        + 4878148972960304722026164313812822946880) * 10^40
        + 2226719225305323191209625820281804485085) * 10^40
        + 5885635086968217648155789787920547833998) * 10^40
        + 5353981391392821693888842035938169306401)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((401 * 10^40
        + 1516872733236923371868773100779905783002) * 10^40
        + 9609595017131297407753053990687342882250) * 10^40
        + 2096676605170371828461921622368818246710) * 10^40
        + 7133210764467163532689929035669529231855) : ℚ) /
        ((((6 * 10^40
        + 6476510850311101771222180405648726413641) * 10^40
        + 8175923707856655427859071497276161878700) * 10^40
        + 8536354463202970601964196655578219831776) * 10^40
        + 5021996773534832280410948039023196635136)))

noncomputable def batchC05119MinusMidpointP022Error2559 : ℝ := ((12757416445031838204868222474267
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP022BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP022Center2559‖ ≤
          batchC05119MinusMidpointP022Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP022Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP022Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP022Input2559 5 =
      (batchC05119MinusMidpointP022Center2559, ((12757416445031838204868222474267 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP022Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP022Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP022Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP022Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP022Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP022Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP022DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP022Factor2559 * embedPair2542
          batchC05119MinusMidpointP022Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP022Factor2559 : ℝ) *
            batchC05119MinusMidpointP022Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP022Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP022Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP022BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP022Factor2559)

def batchC05119MinusMidpointP023Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((300278613592663314364333 : ℚ) /
        230584300921369395200000000))

def batchC05119MinusMidpointP023Center2559 : RatPair2542 :=
    (((136686640415039211203476799403185929 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((5699309061811798124687511188241495 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP023Factor2559 : RatPair2542 := ((((-((((((((46905 * 10^40
        + 1671382316195581691532267241421699001631) * 10^40
        + 3770919478339308495212694481710085821526) * 10^40
        + 4052955811019295937722073969264327805804) * 10^40
        + 2915522917234694698422763485449706221230) * 10^40
        + 9014982679889330617441880285325524790531) * 10^40
        + 9937840078353495271480801286145161326870) * 10^40
        + 9739005390245110387310912167620561115467) * 10^40
        + 9979607191346498768224276739993861908385)) : ℚ) /
        ((((((((11 * 10^40
        + 478162370788241076007694282639687583167) * 10^40
        + 2687225231487420576272771282544101294577) * 10^40
        + 3855201398249542791308579597247701463658) * 10^40
        + 9799804258855378868373469855755590432196) * 10^40
        + 7129664797525613243297924374506405241426) * 10^40
        + 3374011437479554348863559323241173297527) * 10^40
        + 1265261591484924144576407652550083393295) * 10^40
        + 7097395387310181150403370122408177434624)),
    ((((((214 * 10^40
        + 6904754476277674121511170749274102851199) * 10^40
        + 7830456639703771167445944698425769187438) * 10^40
        + 9994682978105431665136993348438327089365) * 10^40
        + 8023822810458015464488512210079377361071) : ℚ) /
        ((((3 * 10^40
        + 3238255425155550885611090202824363206820) * 10^40
        + 9087961853928327713929535748638080939350) * 10^40
        + 4268177231601485300982098327789109915888) * 10^40
        + 2510998386767416140205474019511598317568)))

noncomputable def batchC05119MinusMidpointP023Error2559 : ℝ := ((12790395802961362069933608160469
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP023BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP023Center2559‖ ≤
          batchC05119MinusMidpointP023Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP023Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP023Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP023Input2559 5 =
      (batchC05119MinusMidpointP023Center2559, ((12790395802961362069933608160469 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP023Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP023Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP023Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP023Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP023Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP023Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP023DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP023Factor2559 * embedPair2542
          batchC05119MinusMidpointP023Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP023Factor2559 : ℝ) *
            batchC05119MinusMidpointP023Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP023Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP023Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP023BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP023Factor2559)

def batchC05119MinusMidpointP024Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((309351029057948556428147 : ℚ) /
        230584300921369395200000000))

def batchC05119MinusMidpointP024Center2559 : RatPair2542 := (((68339678180120605506158153258161733
    : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((5871399891207476313442034600357291 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP024Factor2559 : RatPair2542 := ((((-((((((((49778 * 10^40
        + 2355843801483850875578184947281914492582) * 10^40
        + 405381663160420399616041321994772300911) * 10^40
        + 3611049735347981217472458416280808582407) * 10^40
        + 4753737519205880739475821436002493825468) * 10^40
        + 3349166851258769203574291206014409972658) * 10^40
        + 1548107230686626333256107612001427174505) * 10^40
        + 6218777144916642061740189899617494879830) * 10^40
        + 9352254574118913765616305944330131156065)) : ℚ) /
        ((((((((11 * 10^40
        + 478162370788241076007694282639687583167) * 10^40
        + 2687225231487420576272771282544101294577) * 10^40
        + 3855201398249542791308579597247701463658) * 10^40
        + 9799804258855378868373469855755590432196) * 10^40
        + 7129664797525613243297924374506405241426) * 10^40
        + 3374011437479554348863559323241173297527) * 10^40
        + 1265261591484924144576407652550083393295) * 10^40
        + 7097395387310181150403370122408177434624)),
    ((((((221 * 10^40
        + 1769886441443015391281851333838671017316) * 10^40
        + 565800107209998211052893520610020981305) * 10^40
        + 9841568267612017512682196834137053926723) * 10^40
        + 9874850059390131340951304328749571680689) : ℚ) /
        ((((3 * 10^40
        + 3238255425155550885611090202824363206820) * 10^40
        + 9087961853928327713929535748638080939350) * 10^40
        + 4268177231601485300982098327789109915888) * 10^40
        + 2510998386767416140205474019511598317568)))

noncomputable def batchC05119MinusMidpointP024Error2559 : ℝ := ((12805559620621050123162630583929
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP024BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP024Center2559‖ ≤
          batchC05119MinusMidpointP024Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP024Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP024Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP024Input2559 5 =
      (batchC05119MinusMidpointP024Center2559, ((12805559620621050123162630583929 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP024Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP024Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP024Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP024Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP024Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP024Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP024DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP024Factor2559 * embedPair2542
          batchC05119MinusMidpointP024Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP024Factor2559 : ℝ) *
            batchC05119MinusMidpointP024Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP024Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP024Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP024BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP024Factor2559)

def batchC05119MinusMidpointP025Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((10022692915539018190833 : ℚ) /
        7205759403792793600000000))

def batchC05119MinusMidpointP025Center2559 : RatPair2542 := (((34167479339850471652350888600578377
    : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((1521789257472507094779280262146343 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchC05119MinusMidpointP025Factor2559 : RatPair2542 := ((((-((((((((52 * 10^40
        + 2474226737060882895906929140831193863219) * 10^40
        + 3169076225037516718482448788013880541082) * 10^40
        + 5787905304286059139066492560472599395625) * 10^40
        + 5351625237068837052074856126442678234204) * 10^40
        + 4874267199160699069720155127847491560644) * 10^40
        + 6961681347244422476476723106638974765305) * 10^40
        + 2364435999200465175793041550292158869577) * 10^40
        + 9293243135699283278000592364704234139097)) : ℚ) /
        (((((((107888830440222891675788763947890319905 * 10^40
        + 4367858618390124434156516378205609473920) * 10^40
        + 4857280470115478069132137284762937208460) * 10^40
        + 6044726371346538455926145966656011318781) * 10^40
        + 4421025063278833606682908129271978911368) * 10^40
        + 5804076183044413627293812069651602708298) * 10^40
        + 3663344982022934496234937898098193440813) * 10^40
        + 7653415425182920098779690791135164235776)),
    ((((((2 * 10^40
        + 3886446452267050543355055238328360690882) * 10^40
        + 9974054489031924001223289867672892316642) * 10^40
        + 2446318108390023125346817812271380315454) * 10^40
        + 9124059698268544243718885251780741438857) : ℚ) /
        (((346231827345370321725115522946087116737 * 10^40
        + 7177999602645086747020099330714980009784) * 10^40
        + 9002793512829182138551896857581136561623) * 10^40
        + 8359489566528827251460473687703245815808)))

noncomputable def batchC05119MinusMidpointP025Error2559 : ℝ := ((12824579217304171718057015272063
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP025BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP025Center2559‖ ≤
          batchC05119MinusMidpointP025Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP025Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP025Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP025Input2559 5 =
      (batchC05119MinusMidpointP025Center2559, ((12824579217304171718057015272063 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP025Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP025Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP025Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP025Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP025Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP025Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP025DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP025Factor2559 * embedPair2542
          batchC05119MinusMidpointP025Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP025Factor2559 : ℝ) *
            batchC05119MinusMidpointP025Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP025Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP025Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP025BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP025Factor2559)

def batchC05119MinusMidpointP026Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((20771944281655350607437 : ℚ) /
        14411518807585587200000000))

def batchC05119MinusMidpointP026Center2559 : RatPair2542 :=
    (((136659919197270569396874800820455727 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((6307636382018199176097057140661301 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP026Factor2559 : RatPair2542 := ((((-((((((((224 * 10^40
        + 3950601623923801363171854879436821906593) * 10^40
        + 674871754450806208604001365313852576396) * 10^40
        + 4188471315682238371147451968140264740837) * 10^40
        + 2225856756517142165468098276751011906523) * 10^40
        + 8067824535330056381263626491101784213646) * 10^40
        + 1688994420442576706046631376924908396751) * 10^40
        + 821290763701304038564394264728162392523) * 10^40
        + 2929564317460314186527357481484320226785)) : ℚ) /
        (((((((431555321760891566703155055791561279621 * 10^40
        + 7471434473560497736626065512822437895681) * 10^40
        + 9429121880461912276528549139051748833842) * 10^40
        + 4178905485386153823704583866624045275125) * 10^40
        + 7684100253115334426731632517087915645474) * 10^40
        + 3216304732177654509175248278606410833193) * 10^40
        + 4653379928091737984939751592392773763255) * 10^40
        + 613661700731680395118763164540656943104)),
    ((((((4 * 10^40
        + 9504453441248778026509871376363589328326) * 10^40
        + 9801967506248532348511210920378048450857) * 10^40
        + 5231892842895301491559623060730020357648) * 10^40
        + 6152898892543276204703181217906781603973) : ℚ) /
        (((692463654690740643450231045892174233475 * 10^40
        + 4355999205290173494040198661429960019569) * 10^40
        + 8005587025658364277103793715162273123247) * 10^40
        + 6718979133057654502920947375406491631616)))

noncomputable def batchC05119MinusMidpointP026Error2559 : ℝ := ((802751527594199502709434288411 :
    ℝ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))

theorem batchC05119MinusMidpointP026BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP026Center2559‖ ≤
          batchC05119MinusMidpointP026Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP026Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP026Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP026Input2559 5 =
      (batchC05119MinusMidpointP026Center2559, ((802751527594199502709434288411 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP026Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP026Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP026Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP026Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP026Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP026Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP026DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP026Factor2559 * embedPair2542
          batchC05119MinusMidpointP026Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP026Factor2559 : ℝ) *
            batchC05119MinusMidpointP026Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP026Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP026Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP026BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP026Factor2559)

def batchC05119MinusMidpointP027Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((43640783619197408678627 : ℚ) /
        28823037615171174400000000))

def batchC05119MinusMidpointP027Center2559 : RatPair2542 := (((68322432286486280850215626926325827
    : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((1656441546777852633686996522286253 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchC05119MinusMidpointP027Factor2559 : RatPair2542 := ((((-((((((((990 * 10^40
        + 3689466812801397938732772365241217531206) * 10^40
        + 6693110855506507586661145107199313886697) * 10^40
        + 591953887362332104094046405159012900624) * 10^40
        + 9753606791737829724080881920831480633958) * 10^40
        + 3243225810425235168233589882183871639415) * 10^40
        + 7171189580572667916557376139514518144782) * 10^40
        + 224610175347053066367586150258764821114) * 10^40
        + 7566312102526236281923992848926450122497)) : ℚ) /
        (((((((1726221287043566266812620223166245118486 * 10^40
        + 9885737894241990946504262051289751582727) * 10^40
        + 7716487521847649106114196556206995335369) * 10^40
        + 6715621941544615294818335466496181100503) * 10^40
        + 736401012461337706926530068351662581897) * 10^40
        + 2865218928710618036700993114425643332773) * 10^40
        + 8613519712366951939759006369571095053020) * 10^40
        + 2454646802926721580475052658162627772416)),
    ((((((31 * 10^40
        + 2018910438364159058067081894069549686351) * 10^40
        + 4027530363216368796658822916762953338148) * 10^40
        + 8336903718539082854310882039758786393378) * 10^40
        + 7427789230020384206032950850012934168449) : ℚ) /
        (((4154781928144443860701386275353045400852 * 10^40
        + 6135995231741040964241191968579760117418) * 10^40
        + 8033522153950185662622762290973638739486) * 10^40
        + 313874798345927017525684252438949789696)))

noncomputable def batchC05119MinusMidpointP027Error2559 : ℝ := ((12872098684645859738690869196497
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP027BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP027Center2559‖ ≤
          batchC05119MinusMidpointP027Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP027Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP027Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP027Input2559 5 =
      (batchC05119MinusMidpointP027Center2559, ((12872098684645859738690869196497 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP027Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP027Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP027Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP027Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP027Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP027Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP027DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP027Factor2559 * embedPair2542
          batchC05119MinusMidpointP027Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP027Factor2559 : ℝ) *
            batchC05119MinusMidpointP027Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP027Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP027Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP027BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP027Factor2559)

def batchC05119MinusMidpointP028Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((177883892884016178388727 : ℚ) /
        115292150460684697600000000))

def batchC05119MinusMidpointP028Center2559 : RatPair2542 :=
    (((136638699592765050568138124368279213 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((6751708326815425324794131668084415 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05119MinusMidpointP028Factor2559 : RatPair2542 := ((((-((((((((16453 * 10^40
        + 8814753818884419841630453265893849080079) * 10^40
        + 2674245431947495932425376831852955150691) * 10^40
        + 6394239079021389299631061241685329611827) * 10^40
        + 6452120193072274364842126802401443106442) * 10^40
        + 4267187315646745062777153788801902592721) * 10^40
        + 5566621548660763125047211647532479463707) * 10^40
        + 5753600590540497951189285955332317172506) * 10^40
        + 7908685878222388262238814842786639598537)) : ℚ) /
        ((((((((2 * 10^40
        + 7619540592697060269001923570659921895791) * 10^40
        + 8171806307871855144068192820636025323644) * 10^40
        + 3463800349562385697827144899311925365914) * 10^40
        + 7449951064713844717093367463938897608049) * 10^40
        + 1782416199381403310824481093626601310356) * 10^40
        + 5843502859369888587215889830810293324381) * 10^40
        + 7816315397871231036144101913137520848323) * 10^40
        + 9274348846827545287600842530602044358656)),
    ((((((127 * 10^40
        + 1818098559297998360781801955416018102241) * 10^40
        + 78785304606329585301628713073831752297) * 10^40
        + 3473627520309157143595501718452431083624) * 10^40
        + 217018395429299338515547923876976717149) : ℚ) /
        ((((1 * 10^40
        + 6619127712577775442805545101412181603410) * 10^40
        + 4543980926964163856964767874319040469675) * 10^40
        + 2134088615800742650491049163894554957944) * 10^40
        + 1255499193383708070102737009755799158784)))

noncomputable def batchC05119MinusMidpointP028Error2559 : ℝ := ((12883218269031134100672937127365
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05119MinusMidpointP028BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP028Center2559‖ ≤
          batchC05119MinusMidpointP028Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP028Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP028Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP028Input2559 5 =
      (batchC05119MinusMidpointP028Center2559, ((12883218269031134100672937127365 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP028Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP028Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP028Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP028Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP028Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP028Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP028DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP028Factor2559 * embedPair2542
          batchC05119MinusMidpointP028Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP028Factor2559 : ℝ) *
            batchC05119MinusMidpointP028Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP028Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP028Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP028BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP028Factor2559)

def batchC05119MinusMidpointP029Input2559 : RatPair2542 := ((((-((770930 * 10^40
        + 4078144998160162885569281880799393625184) * 10^40
        + 2820699973413950829550922422408735603077)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    ((182939534351242879487659 : ℚ) /
        115292150460684697600000000))

def batchC05119MinusMidpointP029Center2559 : RatPair2542 :=
    (((136629090924539850715299277533950707 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((3471718049687465167916743691513269 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC05119MinusMidpointP029Factor2559 : RatPair2542 := ((((-((((((((17401 * 10^40
        + 4878222531198321138479192945132828444880) * 10^40
        + 4626934475634477261250082454726091486852) * 10^40
        + 5545957004085309176456600512411510252300) * 10^40
        + 4517597750254935415620369403667030351920) * 10^40
        + 312616938974112863234388655433999829334) * 10^40
        + 1868066475662434881913942215343517600830) * 10^40
        + 7161802789689847056403763752235671425142) * 10^40
        + 6419582564041962993313370486986947111025)) : ℚ) /
        ((((((((2 * 10^40
        + 7619540592697060269001923570659921895791) * 10^40
        + 8171806307871855144068192820636025323644) * 10^40
        + 3463800349562385697827144899311925365914) * 10^40
        + 7449951064713844717093367463938897608049) * 10^40
        + 1782416199381403310824481093626601310356) * 10^40
        + 5843502859369888587215889830810293324381) * 10^40
        + 7816315397871231036144101913137520848323) * 10^40
        + 9274348846827545287600842530602044358656)),
    ((((((130 * 10^40
        + 7964464672604255710846331803256230891685) * 10^40
        + 2107512617395989357982716345327879779873) * 10^40
        + 3620028281753503718587262458147346384702) * 10^40
        + 6619296433528042042592316769337083300633) : ℚ) /
        ((((1 * 10^40
        + 6619127712577775442805545101412181603410) * 10^40
        + 4543980926964163856964767874319040469675) * 10^40
        + 2134088615800742650491049163894554957944) * 10^40
        + 1255499193383708070102737009755799158784)))

noncomputable def batchC05119MinusMidpointP029Error2559 : ℝ := ((3225038030897760056212065904601 :
    ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchC05119MinusMidpointP029BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP029Center2559‖ ≤
          batchC05119MinusMidpointP029Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05119MinusMidpointP029Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05119MinusMidpointP029Input2559]
  have hs : compactExp2547 batchC05119MinusMidpointP029Input2559 5 =
      (batchC05119MinusMidpointP029Center2559, ((3225038030897760056212065904601 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05119MinusMidpointP029Input2559 5).2 : ℝ) =
      batchC05119MinusMidpointP029Error2559 := by
    rw [hs]
    norm_num [batchC05119MinusMidpointP029Error2559]
  have h := compactExp_error2547 batchC05119MinusMidpointP029Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      batchC05119MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05119MinusMidpointP029Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05119MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05119MinusMidpointP029Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05119MinusMidpointP029DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP029Factor2559 * embedPair2542
          batchC05119MinusMidpointP029Center2559‖ ≤
        (pairMagnitude2542 batchC05119MinusMidpointP029Factor2559 : ℝ) *
            batchC05119MinusMidpointP029Error2559 := by
  have hx : |batchC05119MinusMidpointPosition2559| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC05119MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchC05119MinusMidpointPosition2559 = embedPair2542
          batchC05119MinusMidpointP029Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05119MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05119MinusMidpointP029Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05119MinusMidpointP029BaseError2559
    (embedPair_magnitude2542 batchC05119MinusMidpointP029Factor2559)

theorem batchC05119MinusMidpointGrid2559 :
    -stripRadius2303 + ((10239 : ℝ) /
        2) * (2 * stripRadius2303 / 10240) =
      batchC05119MinusMidpointPosition2559 := by
  norm_num [stripRadius2303, batchC05119MinusMidpointPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP000DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP001DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP002DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP003DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP004DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP005DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP006DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP007DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP008DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP009DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP010DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP011DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP012DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP013DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP014DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP015DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP016DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP017DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP018DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP019DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP020DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP021DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP022DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP023DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP024DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP025DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP026DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP027DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP028DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointP029DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusMidpointGrid2559
