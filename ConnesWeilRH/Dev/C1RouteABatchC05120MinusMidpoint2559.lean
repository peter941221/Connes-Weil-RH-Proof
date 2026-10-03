import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchC05120MinusMidpointPosition2559 : ℝ := ((65536001 : ℝ) /
        102400000000)

theorem batchC05120MinusMidpointZero2559 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchC05120MinusMidpointP000Input2559 : RatPair2542 := ((((-((526567 * 10^40
        + 749980763691683214034395374763772574615) * 10^40
        + 2054768175655092842994978187942826896923)) : ℚ) /
        ((561665 * 10^40
        + 5204615401596259359546075575030701463919) * 10^40
        + 9047602218941736342579897453772800000000)),
    (((-362039942185747774262029) : ℚ) /
        461168601842738790400000000))

def batchC05120MinusMidpointP000Center2559 : RatPair2542 :=
    (((136674661214513424751605319021374411 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-1717102094442097961505733993318367) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC05120MinusMidpointP000Factor2559 : RatPair2542 := ((((-((((((((1655 * 10^40
        + 9441958658553823626817580105978095775221) * 10^40
        + 2937813932375485676734759690575057462611) * 10^40
        + 1768281497080226019323391941540485815881) * 10^40
        + 6679129474521190417109315694419488617095) * 10^40
        + 3411724641962239693598228358210377551998) * 10^40
        + 785361518824030217487672694600189604825) * 10^40
        + 7964177254768010979927761365709797282443) * 10^40
        + 805640513727225769920787882368578590745)) : ℚ) /
        ((((((((1 * 10^40
        + 685895597817881951277366341122894194814) * 10^40
        + 5146952796833891757209349024436226529001) * 10^40
        + 7171023170136239219399965793910298595070) * 10^40
        + 588440008494878316425823259739851674223) * 10^40
        + 2607093650679921623027054120090762412650) * 10^40
        + 5902415663347002120609690196023420346635) * 10^40
        + 6953188595114330823441587866492907370852) * 10^40
        + 5862021925030157126720075609959189970944)),
    ((((((123 * 10^40
        + 1553466512716892434040536509004860063233) * 10^40
        + 3504485970592456574750075415440409972939) * 10^40
        + 9941686399966916055184679554525533995568) * 10^40
        + 3669115870761117483615477016614963319823) : ℚ) /
        ((((3 * 10^40
        + 1011781693472714364753146591009322093985) * 10^40
        + 5597280945859674264716413246412442858283) * 10^40
        + 7411798469021794771778051689090114685404) * 10^40
        + 545894146172216270068548039023196635136)))

noncomputable def batchC05120MinusMidpointP000Error2559 : ℝ := ((6291857933441635047567093496841 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05120MinusMidpointP000BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP000Center2559‖ ≤
          batchC05120MinusMidpointP000Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP000Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP000Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP000Input2559 5 =
      (batchC05120MinusMidpointP000Center2559, ((6291857933441635047567093496841 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP000Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP000Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP000Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP000Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP000Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP000Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP000DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP000Factor2559 * embedPair2542
          batchC05120MinusMidpointP000Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP000Factor2559 : ℝ) *
            batchC05120MinusMidpointP000Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
      (storedWidth ⟨0, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP000Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP000Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨0, by omega⟩) (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP000BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP000Factor2559)

def batchC05120MinusMidpointP001Input2559 : RatPair2542 := ((((-((674 * 10^40
        + 5379188594605106451953677888534090243007) * 10^40
        + 7507041324749863089854188935606647518689)) : ℚ) /
        ((719 * 10^40
        + 4994130785584412590035563316819680975485) * 10^40
        + 8958819876028164556647397385830400000000)),
    (((-362039942185747774262029) : ℚ) /
        461168601842738790400000000))

def batchC05120MinusMidpointP001Center2559 : RatPair2542 :=
    (((136674770959221755290654537633210149 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-3434206946423404050861397946547677) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05120MinusMidpointP001Factor2559 : RatPair2542 :=
    ((((-(((((((44479197632095855397854486690235 *
    10^40
        + 933917103205756602632551196590938339842) * 10^40
        + 9112502828869094424597794629119967768284) * 10^40
        + 1812021435196629615753460231068170476432) * 10^40
        + 6648335245746529704017551108351776885714) * 10^40
        + 9599082159392330563178049982347532904140) * 10^40
        + 3637665059484846349847166307778009154666) * 10^40
        + 4776668843564150955438027963582705416745)) : ℚ) /
        (((((((28775418324532319786967952471 * 10^40
        + 7247443626522465508482203787428130133755) * 10^40
        + 3587965448109955141623234642302009442615) * 10^40
        + 3131429987758643614585588767372245872650) * 10^40
        + 6185919165191365775118962992303050726788) * 10^40
        + 6521124831663484534272997719416531149618) * 10^40
        + 7603540845108823723409040976099340983178) * 10^40
        + 4078516865497767906843283707414282502144)),
    (((((670313160144606443911671700984348769 * 10^40
        + 5483273775041369312337571429094420496529) * 10^40
        + 4889541896577082179127201741474043690336) * 10^40
        + 3698865031615715334156074828254998312909) : ℚ) /
        (((16963318756815341936648765708178539 * 10^40
        + 5105814919489435369552687615131382672370) * 10^40
        + 2794683902922656136241201367600925059266) * 10^40
        + 9128461603094105914686949958279378239488)))

noncomputable def batchC05120MinusMidpointP001Error2559 : ℝ := ((12583725655384421238347043177657
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP001BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP001Center2559‖ ≤
          batchC05120MinusMidpointP001Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP001Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP001Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP001Input2559 5 =
      (batchC05120MinusMidpointP001Center2559, ((12583725655384421238347043177657 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP001Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP001Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP001Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP001Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP001Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP001Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP001DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP001Factor2559 * embedPair2542
          batchC05120MinusMidpointP001Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP001Factor2559 : ℝ) *
            batchC05120MinusMidpointP001Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP001Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP001Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP001BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP001Factor2559)

def batchC05120MinusMidpointP002Input2559 : RatPair2542 := ((((-((17624 * 10^40
        + 1588621405158990846322698853853377706767) * 10^40
        + 9513942085669616475948464691050354439649)) : ℚ) /
        ((18798 * 10^40
        + 9018532842369922254306089281683396764734) * 10^40
        + 566069047467097906358358173286400000000)),
    ((362039942185747774262029 : ℚ) /
        461168601842738790400000000))

def batchC05120MinusMidpointP002Center2559 : RatPair2542 :=
    (((136674827754127574415772533161679837 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((107319011671896308085855652193247 : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)))

def batchC05120MinusMidpointP002Factor2559 : RatPair2542 :=
    ((((-(((((((20701175032930436834833695305197591621
    * 10^40
        + 4178418143109001596046575322306515715882) * 10^40
        + 931725500365919510581336766978911289639) * 10^40
        + 1961070209162348676818365003451804296478) * 10^40
        + 5790163016660995397308690994770855870366) * 10^40
        + 4372834372092629916981901698394782758151) * 10^40
        + 5318962260454974142867010095320944978533) * 10^40
        + 2278673735356076020300200278453920315945)) : ℚ) /
        (((((((13410031310565378882449342305679330 * 10^40
        + 401664902234481302814542192008003684139) * 10^40
        + 852905566929832024718753418406856746614) * 10^40
        + 7877434763023558242133004913500222975218) * 10^40
        + 278028831589967000503241012990574579820) * 10^40
        + 9446022210166289686110292446630587367471) * 10^40
        + 6913050450403786944441411779349472056112) * 10^40
        + 9930369338561747280442649102418060509184)),
    (((-(((456415032683269360464385622138970784600 * 10^40
        + 4763050042413174277537576764511404372922) * 10^40
        + 610233905034898538326898456118124802834) * 10^40
        + 2642244438949182848845858457138210682829)) : ℚ) /
        (((11580168958424302231511249020634879878 * 10^40
        + 4210121338939055992415895206895249975204) * 10^40
        + 5290647308855873800588227128193473645967) * 10^40
        + 3600485467521501550732789319520829308928)))

noncomputable def batchC05120MinusMidpointP002Error2559 : ℝ := ((12583730721113774953929247158851
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP002BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP002Center2559‖ ≤
          batchC05120MinusMidpointP002Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP002Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP002Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP002Input2559 5 =
      (batchC05120MinusMidpointP002Center2559, ((12583730721113774953929247158851 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP002Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP002Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP002Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP002Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP002Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP002Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP002DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP002Factor2559 * embedPair2542
          batchC05120MinusMidpointP002Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP002Factor2559 : ℝ) *
            batchC05120MinusMidpointP002Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP002Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP002Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP002BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP002Factor2559)

def batchC05120MinusMidpointP003Input2559 : RatPair2542 := ((((-((2327693 * 10^40
        + 460744149073196828753692660572439783126) * 10^40
        + 2754730881858548426073776901321733146923)) : ℚ) /
        ((2482846 * 10^40
        + 636835275403096208616850176779124390100) * 10^40
        + 1635094399228984342579897453772800000000)),
    ((362039942185747774262029 : ℚ) /
        461168601842738790400000000))

def batchC05120MinusMidpointP003Center2559 : RatPair2542 := (((68337429753901849397727012965433429
    : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((3434209171370649779596749449237771 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05120MinusMidpointP003Factor2559 : RatPair2542 := ((((-((((((((5664840 * 10^40
        + 6714668135763395195188271681409084950663) * 10^40
        + 7366158314482557184138193238242081742440) * 10^40
        + 8808093342279858013496948822758427283379) * 10^40
        + 5946403836063189419366435561392421526316) * 10^40
        + 4309344451971942859774798167837455053111) * 10^40
        + 5434117774563285650643710741149080432601) * 10^40
        + 3014806478073634789064322380656102865259) * 10^40
        + 1379574269898493262476951829989082316705)) : ℚ) /
        ((((((((3672 * 10^40
        + 3287779048855716809537066613285847618482) * 10^40
        + 218250735350543419281472381851475990008) * 10^40
        + 5041395110736834555187824676417997903913) * 10^40
        + 7750167000640157995043893681458478203901) * 10^40
        + 4024468343049927224229673213608375348585) * 10^40
        + 758291010479280115838670104786290808681) * 10^40
        + 7786739498744472271716234221462351189179) * 10^40
        + 8167986996661568665726120489632709738496)),
    (((-((((2384 * 10^40
        + 9941689031657359242528416238815795516120) * 10^40
        + 441002282205504537040445368500577276861) * 10^40
        + 9185571540178472456154233044923837183782) * 10^40
        + 2681484699580326705950158916029025819823)) : ℚ) /
        ((((60 * 10^40
        + 5997423914069586177573697612318088952245) * 10^40
        + 2919711175873929275085381732187877864721) * 10^40
        + 3867841134428167041263241288726534050566) * 10^40
        + 6977279854411393674976068039023196635136)))

noncomputable def batchC05120MinusMidpointP003Error2559 : ℝ := ((12583733553331300158913363267381
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP003BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP003Center2559‖ ≤
          batchC05120MinusMidpointP003Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP003Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP003Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP003Input2559 5 =
      (batchC05120MinusMidpointP003Center2559, ((12583733553331300158913363267381 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP003Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP003Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP003Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP003Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP003Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP003Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP003DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP003Factor2559 * embedPair2542
          batchC05120MinusMidpointP003Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP003Factor2559 : ℝ) *
            batchC05120MinusMidpointP003Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP003Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP003Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP003BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP003Factor2559)

def batchC05120MinusMidpointP004Input2559 : RatPair2542 := ((((-((40440 * 10^40
        + 3513598751337873513486253242224814861051) * 10^40
        + 6337553455884322119186589276011291939649)) : ℚ) /
        ((43135 * 10^40
        + 9142560649053103021034874848280634595490) * 10^40
        + 6430360174760377906358358173286400000000)),
    (((-362039942185747774262029) : ℚ) /
        461168601842738790400000000))

def batchC05120MinusMidpointP004Center2559 : RatPair2542 := (((34168719594190941501001179587261557
    : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-3434209645488245000788733740453883) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05120MinusMidpointP004Factor2559 : RatPair2542 :=
    ((((-(((((((573208121689293868462046281493527051853 *
    10^40
        + 9182563390738419444992914561755302524365) * 10^40
        + 5957819571828379572374028554304686413219) * 10^40
        + 1426433308330805707250180939544336535339) * 10^40
        + 3977541775345352177156649606183717172661) * 10^40
        + 8367789357138452803461208331578817769710) * 10^40
        + 3478694546674108043294077706930278195177) * 10^40
        + 4835212675748584026905065024547670315945)) : ℚ) /
        (((((((371754212938148354659147433803003664 * 10^40
        + 2275200296478229247172803947590264788504) * 10^40
        + 3744214461033644318096342279782433854401) * 10^40
        + 5958583646481080335765081213521094654813) * 10^40
        + 1710020537322352317460317036562216341031) * 10^40
        + 2349498502665640230877415161379248058499) * 10^40
        + 9282055604377216470126070923508582259216) * 10^40
        + 1932963425659604440429849102418060509184)),
    (((((2397566095070281958213236871231558725629 * 10^40
        + 6441684926525503925072408219638609393841) * 10^40
        + 9622358095931760223389684270923507175194) * 10^40
        + 9599687196672216759963956259872585682829) : ℚ) /
        (((60971650210417329220350949185436832144 * 10^40
        + 8736556519624530247202451315220016226237) * 10^40
        + 5263714786560620305229997810007518251734) * 10^40
        + 2222531371331146615743989319520829308928)))

noncomputable def batchC05120MinusMidpointP004Error2559 : ℝ := ((6291867618158755730162614094847 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05120MinusMidpointP004BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP004Center2559‖ ≤
          batchC05120MinusMidpointP004Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP004Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP004Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP004Input2559 5 =
      (batchC05120MinusMidpointP004Center2559, ((6291867618158755730162614094847 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP004Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP004Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP004Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP004Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP004Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP004Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP004DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP004Factor2559 * embedPair2542
          batchC05120MinusMidpointP004Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP004Factor2559 : ℝ) *
            batchC05120MinusMidpointP004Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP004Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP004Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP004BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP004Factor2559)

def batchC05120MinusMidpointP005Input2559 : RatPair2542 := ((((-((1920136 * 10^40
        + 7121133689532251573463886905273962788066) * 10^40
        + 3286953412541279695516690703965199440769)) : ℚ) /
        ((2048123 * 10^40
        + 8742869729198005596656856045052835367848) * 10^40
        + 8500538745902249027739692361318400000000)),
    ((0 : ℚ) /
        1))

def batchC05120MinusMidpointP005Center2559 : RatPair2542 :=
    (((136717845228877180487045690639617955 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC05120MinusMidpointP005Factor2559 : RatPair2542 := ((((-(((((((2776712609728896 * 10^40
        + 3801639068139881191692587943424012955860) * 10^40
        + 8434438598127657933801639327494597209807) * 10^40
        + 1696170101716000740321641454058546309946) * 10^40
        + 8516039673826778156287686373507565627524) * 10^40
        + 4972849582699083269844632822260029632745) * 10^40
        + 6679119182556598639784306677600548727605) * 10^40
        + 445828665890078510773953466277052551679)) : ℚ) /
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

noncomputable def batchC05120MinusMidpointP005Error2559 : ℝ := ((383866729167967273682297964023 :
    ℝ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))

theorem batchC05120MinusMidpointP005BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP005Center2559‖ ≤
          batchC05120MinusMidpointP005Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP005Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP005Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP005Input2559 5 =
      (batchC05120MinusMidpointP005Center2559, ((383866729167967273682297964023 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP005Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP005Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP005Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP005Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP005Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP005Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP005DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP005Factor2559 * embedPair2542
          batchC05120MinusMidpointP005Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP005Factor2559 : ℝ) *
            batchC05120MinusMidpointP005Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
      (storedWidth ⟨5, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP005Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP005Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨5, by omega⟩) (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP005BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP005Factor2559)

def batchC05120MinusMidpointP006Input2559 : RatPair2542 :=
    ((((-343601048718721352390134813971797333) : ℚ) /
        366503866542833823313644748800000000),
    ((0 : ℚ) /
        1))

def batchC05120MinusMidpointP006Center2559 : RatPair2542 :=
    (((136717951126079978533434157739287323 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC05120MinusMidpointP006Factor2559 : RatPair2542 := ((((-((12315910315668 * 10^40
        + 5822379253145355591755859248738971136101) * 10^40
        + 6405967492515156761567483869353243079111)) : ℚ) /
        ((3521251306724 * 10^40
        + 4693370084997631605252093003549209262592) * 10^40
        + 5503507844426412953730064522587027683556)),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusMidpointP006Error2559 : ℝ := ((12283744550626596015737681746167
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP006BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP006Center2559‖ ≤
          batchC05120MinusMidpointP006Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP006Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP006Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP006Input2559 5 =
      (batchC05120MinusMidpointP006Center2559, ((12283744550626596015737681746167 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP006Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP006Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP006Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP006Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP006Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP006Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP006DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP006Factor2559 * embedPair2542
          batchC05120MinusMidpointP006Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP006Factor2559 : ℝ) *
            batchC05120MinusMidpointP006Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP006Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP006Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP006BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP006Factor2559)

def batchC05120MinusMidpointP007Input2559 : RatPair2542 := ((((-((2327693 * 10^40
        + 460744149073196828753692660572439783126) * 10^40
        + 2754730881858548426073776901321733146923)) : ℚ) /
        ((2482846 * 10^40
        + 636835275403096208616850176779124390100) * 10^40
        + 1635094399228984342579897453772800000000)),
    ((0 : ℚ) /
        1))

def batchC05120MinusMidpointP007Center2559 : RatPair2542 :=
    (((136717998135251400439624042004778503 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC05120MinusMidpointP007Factor2559 : RatPair2542 := ((((-(((((((13495753967386657 * 10^40
        + 3881582945168423187722423217042596439739) * 10^40
        + 6913856415331594350427273444237877328699) * 10^40
        + 6393988883310651420289323001524715559643) * 10^40
        + 1233080759271759226877268499340283711063) * 10^40
        + 9005740600698575586719248876327954752486) * 10^40
        + 9643727782826060835201433862404726454500) * 10^40
        + 1366761421423194466385657051808561394631)) : ℚ) /
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

noncomputable def batchC05120MinusMidpointP007Error2559 : ℝ := ((12283748642286654225159662212635
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP007BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP007Center2559‖ ≤
          batchC05120MinusMidpointP007Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP007Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP007Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP007Input2559 5 =
      (batchC05120MinusMidpointP007Center2559, ((12283748642286654225159662212635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP007Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP007Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP007Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP007Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP007Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP007Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP007DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP007Factor2559 * embedPair2542
          batchC05120MinusMidpointP007Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP007Factor2559 : ℝ) *
            batchC05120MinusMidpointP007Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP007Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP007Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP007BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP007Factor2559)

def batchC05120MinusMidpointP008Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-260739661220379310273297) : ℚ) /
        922337203685477580800000000))

def batchC05120MinusMidpointP008Center2559 : RatPair2542 :=
    (((136712286978400398332148672953907503 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-154595467440959057732820569310575) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)))

def batchC05120MinusMidpointP008Factor2559 : RatPair2542 := ((((-((((((((36376 * 10^40
        + 4133052405602331355743141778668296226479) * 10^40
        + 418449416636219000990341103726155729348) * 10^40
        + 4706089053070609507205662514654758613139) * 10^40
        + 9651190246195170515570198907355099165115) * 10^40
        + 9053546371125156513619079211526896727217) * 10^40
        + 9816430529669764870918959706063147226289) * 10^40
        + 5744188344795328426753917345115257664343) * 10^40
        + 6804806245403171890650820720190319321625)) : ℚ) /
        ((((((((176 * 10^40
        + 7650597932611857216123108522235001330676) * 10^40
        + 2995603703798729220364340520705620713238) * 10^40
        + 1683222371992684660937273555963223418543) * 10^40
        + 6796868141686061893975517692089446915147) * 10^40
        + 4074636760409811892766789992102483862821) * 10^40
        + 3984182999672869581816949171858772760434) * 10^40
        + 244185463758786313222522440801334292731) * 10^40
        + 3558326196962898406453921958530838953984)),
    ((((((189 * 10^40
        + 4296092521640751745713318578018259672621) * 10^40
        + 7749314914614604337192518946067686208688) * 10^40
        + 6071243516356310569761919723292249560469) * 10^40
        + 6601858450481344230249011668354228863739) : ℚ) /
        ((((13 * 10^40
        + 2953021700622203542444360811297452827283) * 10^40
        + 6351847415713310855718142994552323757401) * 10^40
        + 7072708926405941203928393311156439663553) * 10^40
        + 43993547069664560821896078046393270272)))

noncomputable def batchC05120MinusMidpointP008Error2559 : ℝ := ((12391523609044378302653011318789
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP008BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP008Center2559‖ ≤
          batchC05120MinusMidpointP008Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP008Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP008Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP008Input2559 5 =
      (batchC05120MinusMidpointP008Center2559, ((12391523609044378302653011318789 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP008Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP008Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP008Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP008Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP008Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP008Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP008DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP008Factor2559 * embedPair2542
          batchC05120MinusMidpointP008Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP008Factor2559 : ℝ) *
            batchC05120MinusMidpointP008Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP008Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP008Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP008BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP008Factor2559)

def batchC05120MinusMidpointP009Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-387788191040974601829711) : ℚ) /
        922337203685477580800000000))

def batchC05120MinusMidpointP009Center2559 : RatPair2542 :=
    (((136705507370306319352423516275795583 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-919680656402289789750491646132041) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC05120MinusMidpointP009Factor2559 : RatPair2542 := ((((-((((((((79177 * 10^40
        + 5440411042896794680304741209904861452859) * 10^40
        + 2938310096241832875281394521992169667614) * 10^40
        + 206436797596275775650361291251697489876) * 10^40
        + 9982325715717080468299548178189107449428) * 10^40
        + 6583394193084648645156373999830664883271) * 10^40
        + 6221065808048163245906907317496954915636) * 10^40
        + 2993591916625963138112597005007752244135) * 10^40
        + 9531252512813596708114411380805385297753)) : ℚ) /
        ((((((((176 * 10^40
        + 7650597932611857216123108522235001330676) * 10^40
        + 2995603703798729220364340520705620713238) * 10^40
        + 1683222371992684660937273555963223418543) * 10^40
        + 6796868141686061893975517692089446915147) * 10^40
        + 4074636760409811892766789992102483862821) * 10^40
        + 3984182999672869581816949171858772760434) * 10^40
        + 244185463758786313222522440801334292731) * 10^40
        + 3558326196962898406453921958530838953984)),
    ((((((93 * 10^40
        + 9104867510068947893977422701745001341541) * 10^40
        + 5137121876887446848921657791055848427400) * 10^40
        + 2161566888391622510922521174492253832698) * 10^40
        + 1292823707199654851554104001594960686519) : ℚ) /
        ((((4 * 10^40
        + 4317673900207401180814786937099150942427) * 10^40
        + 8783949138571103618572714331517441252467) * 10^40
        + 2357569642135313734642797770385479887851) * 10^40
        + 14664515689888186940632026015464423424)))

noncomputable def batchC05120MinusMidpointP009Error2559 : ℝ := ((6222070607261231094032983378609 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05120MinusMidpointP009BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP009Center2559‖ ≤
          batchC05120MinusMidpointP009Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP009Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP009Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP009Input2559 5 =
      (batchC05120MinusMidpointP009Center2559, ((6222070607261231094032983378609 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP009Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP009Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP009Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP009Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP009Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP009Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP009DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP009Factor2559 * embedPair2542
          batchC05120MinusMidpointP009Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP009Factor2559 : ℝ) *
            batchC05120MinusMidpointP009Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP009Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP009Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP009BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP009Factor2559)

def batchC05120MinusMidpointP010Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-230684447942438333698521) : ℚ) /
        461168601842738790400000000))

def batchC05120MinusMidpointP010Center2559 : RatPair2542 := (((34175091579613779989962700881374889
    : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-2188342709014879311882140902764613) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05120MinusMidpointP010Factor2559 : RatPair2542 := ((((-((((((((27908 * 10^40
        + 6467149882689493951415201840475056121477) * 10^40
        + 4802787395918830098616249671545396831530) * 10^40
        + 7956829113158380725776504792272552361616) * 10^40
        + 255776519090610359270890615918858983334) * 10^40
        + 1356593924662780202321171805932065397155) * 10^40
        + 827958552416903035797073269977828878857) * 10^40
        + 8824785101526594844826163956370148728085) * 10^40
        + 2152934322024789858890846884953107648105)) : ℚ) /
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
        + 2071939993863125096996115616145172175684) * 10^40
        + 2672650958049288896494550572854526198234) * 10^40
        + 333549474491578539094449716415731264699) * 10^40
        + 5300764600679706205380979628651576129001) : ℚ) /
        (((2462092994455966732267488163172175052357 * 10^40
        + 1043552729920616867698484129528746736248) * 10^40
        + 1797642757896406318591266542799193327102) * 10^40
        + 8334148028649438232607812890334192467968)))

noncomputable def batchC05120MinusMidpointP010Error2559 : ℝ := ((12474644023065613090866087387455
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP010BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP010Center2559‖ ≤
          batchC05120MinusMidpointP010Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP010Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP010Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP010Input2559 5 =
      (batchC05120MinusMidpointP010Center2559, ((12474644023065613090866087387455 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP010Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP010Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP010Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP010Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP010Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP010Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP010DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP010Factor2559 * embedPair2542
          batchC05120MinusMidpointP010Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP010Factor2559 : ℝ) *
            batchC05120MinusMidpointP010Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP010Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP010Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP010BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP010Factor2559)

def batchC05120MinusMidpointP011Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-255213677437476200797801) : ℚ) /
        461168601842738790400000000))

def batchC05120MinusMidpointP011Center2559 : RatPair2542 := (((68348221812710163538826452641338097
    : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-1210505635488742196396806136103731) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC05120MinusMidpointP011Factor2559 : RatPair2542 := ((((-((((((((34100 * 10^40
        + 72742818117290959901326141788301642832) * 10^40
        + 2971762581579955578605623188030530998706) * 10^40
        + 6758775164520894376689305279162460261540) * 10^40
        + 7714961185432666282551778183616917552565) * 10^40
        + 1918955554308644586715138031369982709591) * 10^40
        + 542285846505960558556582847154845286169) * 10^40
        + 5382327332202871088191844743011949579048) * 10^40
        + 3661088904539727448625293094928594539145)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((185 * 10^40
        + 4149344465372463576188510732974141227142) * 10^40
        + 4850411072471739681081999239698584307378) * 10^40
        + 8000415730780065522007482668171067453486) * 10^40
        + 738703360090493715438177459009825576387) : ℚ) /
        ((((6 * 10^40
        + 6476510850311101771222180405648726413641) * 10^40
        + 8175923707856655427859071497276161878700) * 10^40
        + 8536354463202970601964196655578219831776) * 10^40
        + 5021996773534832280410948039023196635136)))

noncomputable def batchC05120MinusMidpointP011Error2559 : ℝ := ((12494992957447340218244622976543
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP011BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP011Center2559‖ ≤
          batchC05120MinusMidpointP011Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP011Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP011Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP011Input2559 5 =
      (batchC05120MinusMidpointP011Center2559, ((12494992957447340218244622976543 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP011Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP011Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP011Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP011Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP011Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP011Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP011DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP011Factor2559 * embedPair2542
          batchC05120MinusMidpointP011Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP011Factor2559 : ℝ) *
            batchC05120MinusMidpointP011Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP011Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP011Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP011BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP011Factor2559)

def batchC05120MinusMidpointP012Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-5612399119318874813509) : ℚ) /
        9223372036854775808000000))

def batchC05120MinusMidpointP012Center2559 : RatPair2542 :=
    (((136691963174027820097628144511658459 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-1330995777805086290938257695916357) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC05120MinusMidpointP012Factor2559 : RatPair2542 := ((((-((((((((10292 * 10^40
        + 9437644783608984704957834423452613377499) * 10^40
        + 51119264980677595801659891954600311797) * 10^40
        + 6242090225883335506154734554186813936158) * 10^40
        + 7153681668432013181116183373307467506437) * 10^40
        + 8417755382277334229297022043585554728043) * 10^40
        + 927897530963907496143546781836583006680) * 10^40
        + 9734020206371835465087010027087481119807) * 10^40
        + 8242558928371150874172204209126420571969)) : ℚ) /
        ((((((((11 * 10^40
        + 478162370788241076007694282639687583167) * 10^40
        + 2687225231487420576272771282544101294577) * 10^40
        + 3855201398249542791308579597247701463658) * 10^40
        + 9799804258855378868373469855755590432196) * 10^40
        + 7129664797525613243297924374506405241426) * 10^40
        + 3374011437479554348863559323241173297527) * 10^40
        + 1265261591484924144576407652550083393295) * 10^40
        + 7097395387310181150403370122408177434624)),
    ((((((101 * 10^40
        + 9364072925960840343130784835033123193127) * 10^40
        + 4593171082649087427032932958363164710117) * 10^40
        + 747438175317556035093549172682411014660) * 10^40
        + 6552448890749810739745727508708017364575) : ℚ) /
        ((((3 * 10^40
        + 3238255425155550885611090202824363206820) * 10^40
        + 9087961853928327713929535748638080939350) * 10^40
        + 4268177231601485300982098327789109915888) * 10^40
        + 2510998386767416140205474019511598317568)))

noncomputable def batchC05120MinusMidpointP012Error2559 : ℝ := ((12516079390333272765964057707897
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP012BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP012Center2559‖ ≤
          batchC05120MinusMidpointP012Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP012Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP012Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP012Input2559 5 =
      (batchC05120MinusMidpointP012Center2559, ((12516079390333272765964057707897 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP012Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP012Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP012Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP012Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP012Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP012Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP012DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP012Factor2559 * embedPair2542
          batchC05120MinusMidpointP012Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP012Factor2559 : ℝ) *
            batchC05120MinusMidpointP012Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP012Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP012Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP012BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP012Factor2559)

def batchC05120MinusMidpointP013Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-60754466143128272313291) : ℚ) /
        92233720368547758080000000))

def batchC05120MinusMidpointP013Center2559 : RatPair2542 := (((68343755121165327867851510004436043
    : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-1440793111854515292673524676401477) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC05120MinusMidpointP013Factor2559 : RatPair2542 := ((((-((((((((48200 * 10^40
        + 1833874502219715942687919366043654615328) * 10^40
        + 2725605315123291666930322536539856563783) * 10^40
        + 4895082740973396355450376216531654566880) * 10^40
        + 6762100824002188923356171116765099651885) * 10^40
        + 6037458949931145344119071251778321229652) * 10^40
        + 1922715624947746362616109948598613977674) * 10^40
        + 7577713279564314100418761560650247676096) * 10^40
        + 2411131020233991219254695945407390022601)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((73 * 10^40
        + 5644047396467797211818320821766090900969) * 10^40
        + 2194217885653113595035539862826911469674) * 10^40
        + 2220275339698787881811250789508655541764) * 10^40
        + 9781314492678849018337718681805726161695) : ℚ) /
        ((((2 * 10^40
        + 2158836950103700590407393468549575471213) * 10^40
        + 9391974569285551809286357165758720626233) * 10^40
        + 6178784821067656867321398885192739943925) * 10^40
        + 5007332257844944093470316013007732211712)))

noncomputable def batchC05120MinusMidpointP013Error2559 : ℝ := ((1566912989275375811473118983903 :
    ℝ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))

theorem batchC05120MinusMidpointP013BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP013Center2559‖ ≤
          batchC05120MinusMidpointP013Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP013Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP013Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP013Input2559 5 =
      (batchC05120MinusMidpointP013Center2559, ((1566912989275375811473118983903 : ℚ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP013Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP013Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP013Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP013Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP013Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP013Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP013DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP013Factor2559 * embedPair2542
          batchC05120MinusMidpointP013Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP013Factor2559 : ℝ) *
            batchC05120MinusMidpointP013Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP013Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP013Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP013BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP013Factor2559)

def batchC05120MinusMidpointP014Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-346671309892138695845011) : ℚ) /
        461168601842738790400000000))

def batchC05120MinusMidpointP014Center2559 : RatPair2542 := (((68339163506555969732738196693149977
    : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-1644226285274679615669592232814395) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC05120MinusMidpointP014Factor2559 : RatPair2542 := ((((-((((((((62695 * 10^40
        + 290691080260659659964350710561171737395) * 10^40
        + 3178564916698961088233728479670181405229) * 10^40
        + 660758450775829274591699352782561217707) * 10^40
        + 9361798284881662956919829266691508895558) * 10^40
        + 2757851625145933189681369576681563613805) * 10^40
        + 5944424817716746005011570101432798796849) * 10^40
        + 9152244861314680257646970820646521192127) * 10^40
        + 9212892157748208065329483075343511797025)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((251 * 10^40
        + 8596920178516699216678726748602151561296) * 10^40
        + 2060383695620414135148354905616168990960) * 10^40
        + 9447198702507389188484882579829654326202) * 10^40
        + 6325670338403288369596729384591409200657) : ℚ) /
        ((((6 * 10^40
        + 6476510850311101771222180405648726413641) * 10^40
        + 8175923707856655427859071497276161878700) * 10^40
        + 8536354463202970601964196655578219831776) * 10^40
        + 5021996773534832280410948039023196635136)))

noncomputable def batchC05120MinusMidpointP014Error2559 : ℝ := ((6285473494843581648649466003743 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05120MinusMidpointP014BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP014Center2559‖ ≤
          batchC05120MinusMidpointP014Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP014Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP014Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP014Input2559 5 =
      (batchC05120MinusMidpointP014Center2559, ((6285473494843581648649466003743 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP014Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP014Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP014Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP014Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP014Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP014Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP014DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP014Factor2559 * embedPair2542
          batchC05120MinusMidpointP014Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP014Factor2559 : ℝ) *
            batchC05120MinusMidpointP014Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP014Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP014Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP014BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP014Factor2559)

def batchC05120MinusMidpointP015Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-377408574479356852679047) : ℚ) /
        461168601842738790400000000))

def batchC05120MinusMidpointP015Center2559 : RatPair2542 :=
    (((136671002449549929343890395836274719 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-3579955983952149285608937093251599) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05120MinusMidpointP015Factor2559 : RatPair2542 := ((((-((((((((74256 * 10^40
        + 3821418569773525350526055446501603185496) * 10^40
        + 5332553873417224142344548970570095832384) * 10^40
        + 951555630727009331156572698713593944235) * 10^40
        + 3084940602572472869293132987696779543507) * 10^40
        + 2411093372054716105291864355612131412827) * 10^40
        + 2064212608003595583125173270259392596406) * 10^40
        + 3615443507398958078380995755867001396811) * 10^40
        + 1232237086721447074537495069350659907497)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((274 * 10^40
        + 1905794363017927732711891629805355411469) * 10^40
        + 1842267984341386111274059388560514243334) * 10^40
        + 5084644884439681634576950359486561615017) * 10^40
        + 6330223319432169715462858535357267438989) : ℚ) /
        ((((6 * 10^40
        + 6476510850311101771222180405648726413641) * 10^40
        + 8175923707856655427859071497276161878700) * 10^40
        + 8536354463202970601964196655578219831776) * 10^40
        + 5021996773534832280410948039023196635136)))

noncomputable def batchC05120MinusMidpointP015Error2559 : ℝ := ((12596502879636174355642633976673
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP015BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP015Center2559‖ ≤
          batchC05120MinusMidpointP015Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP015Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP015Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP015Input2559 5 =
      (batchC05120MinusMidpointP015Center2559, ((12596502879636174355642633976673 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP015Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP015Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP015Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP015Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP015Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP015Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP015DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP015Factor2559 * embedPair2542
          batchC05120MinusMidpointP015Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP015Factor2559 : ℝ) *
            batchC05120MinusMidpointP015Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP015Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP015Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP015BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP015Factor2559)

def batchC05120MinusMidpointP016Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-199810861117846303095609) : ℚ) /
        230584300921369395200000000))

def batchC05120MinusMidpointP016Center2559 : RatPair2542 := (((68332661075085678163612285519335941
    : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-1895304527101121983906433241190063) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC05120MinusMidpointP016Factor2559 : RatPair2542 := ((((-((((((((20805 * 10^40
        + 6279978121824984662591952537019314932831) * 10^40
        + 8619919956181554107500480019279209874825) * 10^40
        + 6704179448696825893193359806999699839248) * 10^40
        + 2344098509737643008430590590103315577084) * 10^40
        + 155875843094184293508632358400174125942) * 10^40
        + 8654656569588888442846000489083669592974) * 10^40
        + 1186597845432106807219071577537973097514) * 10^40
        + 8889539267873130561137818655788293083433)) : ℚ) /
        ((((((((11 * 10^40
        + 478162370788241076007694282639687583167) * 10^40
        + 2687225231487420576272771282544101294577) * 10^40
        + 3855201398249542791308579597247701463658) * 10^40
        + 9799804258855378868373469855755590432196) * 10^40
        + 7129664797525613243297924374506405241426) * 10^40
        + 3374011437479554348863559323241173297527) * 10^40
        + 1265261591484924144576407652550083393295) * 10^40
        + 7097395387310181150403370122408177434624)),
    ((((((48 * 10^40
        + 3881037618603003446908510320171804055148) * 10^40
        + 3514801703190978168108540508304771786076) * 10^40
        + 2080330601283490789819146739722454637897) * 10^40
        + 885634900635282946181349068756621135761) : ℚ) /
        ((((1 * 10^40
        + 1079418475051850295203696734274787735606) * 10^40
        + 9695987284642775904643178582879360313116) * 10^40
        + 8089392410533828433660699442596369971962) * 10^40
        + 7503666128922472046735158006503866105856)))

noncomputable def batchC05120MinusMidpointP016Error2559 : ℝ := ((3153745155590972389566349540121 :
    ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchC05120MinusMidpointP016BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP016Center2559‖ ≤
          batchC05120MinusMidpointP016Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP016Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP016Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP016Input2559 5 =
      (batchC05120MinusMidpointP016Center2559, ((3153745155590972389566349540121 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP016Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP016Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP016Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP016Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP016Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP016Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP016DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP016Factor2559 * embedPair2542
          batchC05120MinusMidpointP016Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP016Factor2559 : ℝ) *
            batchC05120MinusMidpointP016Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP016Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP016Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP016BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP016Factor2559)

def batchC05120MinusMidpointP017Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-442769373018475956606027) : ℚ) /
        461168601842738790400000000))

def batchC05120MinusMidpointP017Center2559 : RatPair2542 := (((34163340168713480049815351650326151
    : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-4199763288592075418371338626840233) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05120MinusMidpointP017Factor2559 : RatPair2542 := ((((-((((((((102103 * 10^40
        + 6379156701226602235704654962999270332699) * 10^40
        + 1029210548957268469924012981604442826686) * 10^40
        + 2602011176083428601132163965231063279880) * 10^40
        + 8422198555263005668762431043407604433438) * 10^40
        + 7447106255443875814961036414621148318955) * 10^40
        + 5639218611039421559837446545765446091279) * 10^40
        + 4108733278211073847765268423236591425848) * 10^40
        + 9188429942273689993727862948827292963377)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((107 * 10^40
        + 2252541444968960078022406554301278991588) * 10^40
        + 6414665139451802465409622023825828479455) * 10^40
        + 9965559611566034652854039825663357262902) * 10^40
        + 2725517630840034701686402842754194944083) : ℚ) /
        ((((2 * 10^40
        + 2158836950103700590407393468549575471213) * 10^40
        + 9391974569285551809286357165758720626233) * 10^40
        + 6178784821067656867321398885192739943925) * 10^40
        + 5007332257844944093470316013007732211712)))

noncomputable def batchC05120MinusMidpointP017Error2559 : ℝ := ((12650894121467099808520738574189
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP017BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP017Center2559‖ ≤
          batchC05120MinusMidpointP017Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP017Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP017Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP017Input2559 5 =
      (batchC05120MinusMidpointP017Center2559, ((12650894121467099808520738574189 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP017Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP017Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP017Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP017Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP017Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP017Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP017DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP017Factor2559 * embedPair2542
          batchC05120MinusMidpointP017Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP017Factor2559 : ℝ) *
            batchC05120MinusMidpointP017Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP017Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP017Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP017BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP017Factor2559)

def batchC05120MinusMidpointP018Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-114770645411675231749613) : ℚ) /
        115292150460684697600000000))

def batchC05120MinusMidpointP018Center2559 : RatPair2542 :=
    (((136648519178942797620154914954826245 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-4354446189128991331961035709773819) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05120MinusMidpointP018Factor2559 : RatPair2542 := ((((-((((((((6859 * 10^40
        + 1293964826586444975537145086048301676663) * 10^40
        + 389215073078892669293552880546553445784) * 10^40
        + 3710765846769161556725163287010113608920) * 10^40
        + 8011939381501699471048794765003635100764) * 10^40
        + 9962851698289191225881835860108953095972) * 10^40
        + 4245168115142991520710510686665809585059) * 10^40
        + 5640482767127963007132697037986914196434) * 10^40
        + 4114476958049238035545819974579535128097)) : ℚ) /
        ((((((((2 * 10^40
        + 7619540592697060269001923570659921895791) * 10^40
        + 8171806307871855144068192820636025323644) * 10^40
        + 3463800349562385697827144899311925365914) * 10^40
        + 7449951064713844717093367463938897608049) * 10^40
        + 1782416199381403310824481093626601310356) * 10^40
        + 5843502859369888587215889830810293324381) * 10^40
        + 7816315397871231036144101913137520848323) * 10^40
        + 9274348846827545287600842530602044358656)),
    ((((((83 * 10^40
        + 3818622460227849711584749321695537156814) * 10^40
        + 5847134129544906747150642444985002347151) * 10^40
        + 3453575779761912654725313715166376774941) * 10^40
        + 1837236266726091133725808067892824536431) : ℚ) /
        ((((1 * 10^40
        + 6619127712577775442805545101412181603410) * 10^40
        + 4543980926964163856964767874319040469675) * 10^40
        + 2134088615800742650491049163894554957944) * 10^40
        + 1255499193383708070102737009755799158784)))

noncomputable def batchC05120MinusMidpointP018Error2559 : ℝ := ((6332239834387775298157803784857 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05120MinusMidpointP018BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP018Center2559‖ ≤
          batchC05120MinusMidpointP018Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP018Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP018Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP018Input2559 5 =
      (batchC05120MinusMidpointP018Center2559, ((6332239834387775298157803784857 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP018Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP018Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP018Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP018Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP018Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP018Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP018DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP018Factor2559 * embedPair2542
          batchC05120MinusMidpointP018Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP018Factor2559 : ℝ) *
            batchC05120MinusMidpointP018Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP018Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP018Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP018BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP018Factor2559)

def batchC05120MinusMidpointP019Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-24428249467783476683391) : ℚ) /
        23058430092136939520000000))

def batchC05120MinusMidpointP019Center2559 : RatPair2542 := (((17079915639964808729064984315884481
    : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    (((-4633985999093087265614726463275305) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05120MinusMidpointP019Factor2559 : RatPair2542 := ((((-((((((((7766 * 10^40
        + 2118896244667168402229980534971903357189) * 10^40
        + 1771510319459000246190787250632331514794) * 10^40
        + 1341411891647345125568680946646960731495) * 10^40
        + 3928361528232845924263058754546890282512) * 10^40
        + 8616879011376939162158283875436147012728) * 10^40
        + 660237679724950197507474837255066500222) * 10^40
        + 4214376092769653361116361275586417819413) * 10^40
        + 4682223616302686741747027211952717012561)) : ℚ) /
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
        + 8596297798393366298484363248611856406399) * 10^40
        + 2970251944730223326071959746233657643843) * 10^40
        + 8259425777053173512057909532953214393283) * 10^40
        + 385925728547980040150456686950097592065) : ℚ) /
        (((1846569745841975049200616122379131289267 * 10^40
        + 8282664547440462650773863097146560052186) * 10^40
        + 1348232068422304738943449907099394995327) * 10^40
        + 1250611021487078674455859667750644350976)))

noncomputable def batchC05120MinusMidpointP019Error2559 : ℝ := ((6344521368187855612048771590229 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05120MinusMidpointP019BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP019Center2559‖ ≤
          batchC05120MinusMidpointP019Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP019Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP019Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP019Input2559 5 =
      (batchC05120MinusMidpointP019Center2559, ((6344521368187855612048771590229 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP019Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP019Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP019Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP019Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP019Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP019Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP019DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP019Factor2559 * embedPair2542
          batchC05120MinusMidpointP019Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP019Factor2559 : ℝ) *
            batchC05120MinusMidpointP019Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP019Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP019Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP019BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP019Factor2559)

def batchC05120MinusMidpointP020Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-520624750538575899551419) : ℚ) /
        461168601842738790400000000))

def batchC05120MinusMidpointP020Center2559 : RatPair2542 := (((34157169573789526182696537546078777
    : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-2468970571417883495732711150680131) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC05120MinusMidpointP020Factor2559 : RatPair2542 := ((((-((((((((141066 * 10^40
        + 3854207402048535586403148965020372529621) * 10^40
        + 9225404759390640944761968412967972479946) * 10^40
        + 3789556025523193755303054130074301349949) * 10^40
        + 9645668702597997780966259855543949872491) * 10^40
        + 7058902172766579095894824183730208798546) * 10^40
        + 3132710881776416466389208481862649768131) * 10^40
        + 6603597112923713546489893270947282749214) * 10^40
        + 8808839137812016030032355137012577426385)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((378 * 10^40
        + 2383646581941397827001680237553640572824) * 10^40
        + 4238053382662183288862080467639330354967) * 10^40
        + 6670528677233404555188714971568140005453) * 10^40
        + 358829113018466762726874265194775799753) : ℚ) /
        ((((6 * 10^40
        + 6476510850311101771222180405648726413641) * 10^40
        + 8175923707856655427859071497276161878700) * 10^40
        + 8536354463202970601964196655578219831776) * 10^40
        + 5021996773534832280410948039023196635136)))

noncomputable def batchC05120MinusMidpointP020Error2559 : ℝ := ((6357884045433226213156186124233 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05120MinusMidpointP020BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP020Center2559‖ ≤
          batchC05120MinusMidpointP020Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP020Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP020Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP020Input2559 5 =
      (batchC05120MinusMidpointP020Center2559, ((6357884045433226213156186124233 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP020Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP020Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP020Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP020Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP020Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP020Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP020DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP020Factor2559 * embedPair2542
          batchC05120MinusMidpointP020Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP020Factor2559 : ℝ) *
            batchC05120MinusMidpointP020Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP020Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP020Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP020BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP020Factor2559)

def batchC05120MinusMidpointP021Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-547379874475946380671387) : ℚ) /
        461168601842738790400000000))

def batchC05120MinusMidpointP021Center2559 : RatPair2542 := (((34154818877729339308813137110852065
    : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-5191584949124348730351156681197473) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05120MinusMidpointP021Factor2559 : RatPair2542 := ((((-((((((((155909 * 10^40
        + 9110525557384125666157382254012038743296) * 10^40
        + 5826244042836959888462676480737829608493) * 10^40
        + 5261890884134698709434255284868499860704) * 10^40
        + 5824192200489524769295634763853606463201) * 10^40
        + 8714219662517942784820208213872755602024) * 10^40
        + 2870407005163708445593359487126864410452) * 10^40
        + 6643565067202572629381296013300206297353) * 10^40
        + 4477231911374839072275003180545007909137)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((132 * 10^40
        + 5587308673606270358032713675261729406188) * 10^40
        + 1938003657637860560476871320050660723706) * 10^40
        + 7114838051686137119350964683587595169506) * 10^40
        + 594068173697370890522196126579399263523) : ℚ) /
        ((((2 * 10^40
        + 2158836950103700590407393468549575471213) * 10^40
        + 9391974569285551809286357165758720626233) * 10^40
        + 6178784821067656867321398885192739943925) * 10^40
        + 5007332257844944093470316013007732211712)))

noncomputable def batchC05120MinusMidpointP021Error2559 : ℝ := ((12738083348632132261538161830413
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP021BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP021Center2559‖ ≤
          batchC05120MinusMidpointP021Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP021Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP021Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP021Input2559 5 =
      (batchC05120MinusMidpointP021Center2559, ((12738083348632132261538161830413 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP021Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP021Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP021Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP021Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP021Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP021Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP021DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP021Factor2559 * embedPair2542
          batchC05120MinusMidpointP021Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP021Factor2559 : ℝ) *
            batchC05120MinusMidpointP021Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP021Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP021Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP021BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP021Factor2559)

def batchC05120MinusMidpointP022Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-112214826711468142236233) : ℚ) /
        92233720368547758080000000))

def batchC05120MinusMidpointP022Center2559 : RatPair2542 := (((68307140316008683592897088491784071
    : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-1330350583688423317708909210312437) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchC05120MinusMidpointP022Factor2559 : RatPair2542 := ((((-((((((((163795 * 10^40
        + 1196060501043067963049956145834323690381) * 10^40
        + 8852536259277624071453165095041438828057) * 10^40
        + 6865960644305125577980238338649650911903) * 10^40
        + 8844398645397374012798226876368307131879) * 10^40
        + 8231268139478409019198877231909579166091) * 10^40
        + 2393823553048407940969284709559199309844) * 10^40
        + 9588194404164756070259877859742720808592) * 10^40
        + 4758180080242741693888842035938169306401)) : ℚ) /
        ((((((((44 * 10^40
        + 1912649483152964304030777130558750332669) * 10^40
        + 748900925949682305091085130176405178309) * 10^40
        + 5420805592998171165234318388990805854635) * 10^40
        + 9199217035421515473493879423022361728786) * 10^40
        + 8518659190102452973191697498025620965705) * 10^40
        + 3496045749918217395454237292964693190108) * 10^40
        + 5061046365939696578305630610200333573182) * 10^40
        + 8389581549240724601613480489632709738496)),
    ((((((407 * 10^40
        + 6251897536654840697830850565172544003493) * 10^40
        + 8610216704085693017476382804271372503577) * 10^40
        + 517990461592825800657555234795557970991) * 10^40
        + 7953347088767963532689929035669529231855) : ℚ) /
        ((((6 * 10^40
        + 6476510850311101771222180405648726413641) * 10^40
        + 8175923707856655427859071497276161878700) * 10^40
        + 8536354463202970601964196655578219831776) * 10^40
        + 5021996773534832280410948039023196635136)))

noncomputable def batchC05120MinusMidpointP022Error2559 : ℝ := ((12749509298184080059107279987989
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP022BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP022Center2559‖ ≤
          batchC05120MinusMidpointP022Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP022Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP022Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP022Input2559 5 =
      (batchC05120MinusMidpointP022Center2559, ((12749509298184080059107279987989 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP022Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP022Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP022Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP022Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP022Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP022Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP022DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP022Factor2559 * embedPair2542
          batchC05120MinusMidpointP022Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP022Factor2559 : ℝ) *
            batchC05120MinusMidpointP022Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP022Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP022Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP022BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP022Factor2559)

def batchC05120MinusMidpointP023Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-300278613592663314364333) : ℚ) /
        230584300921369395200000000))

def batchC05120MinusMidpointP023Center2559 : RatPair2542 :=
    (((136599188951292591595608149343550127 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-2847831335463072975337174172688609) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC05120MinusMidpointP023Factor2559 : RatPair2542 := ((((-((((((((46905 * 10^40
        + 787107952714941475475508639299972185711) * 10^40
        + 9859077608720512817446638753200195486810) * 10^40
        + 8779733263532017710070800315990988001895) * 10^40
        + 4362063950282711780333609699546450503097) * 10^40
        + 9853262471518856691735058514849713845334) * 10^40
        + 7479616160289266458920716008464510033060) * 10^40
        + 8164645219544244992836934185576104359116) * 10^40
        + 4830656863558978768224276739993861908385)) : ℚ) /
        ((((((((11 * 10^40
        + 478162370788241076007694282639687583167) * 10^40
        + 2687225231487420576272771282544101294577) * 10^40
        + 3855201398249542791308579597247701463658) * 10^40
        + 9799804258855378868373469855755590432196) * 10^40
        + 7129664797525613243297924374506405241426) * 10^40
        + 3374011437479554348863559323241173297527) * 10^40
        + 1265261591484924144576407652550083393295) * 10^40
        + 7097395387310181150403370122408177434624)),
    ((((((218 * 10^40
        + 1549986427378520923116551614627126726953) * 10^40
        + 3044902165895298036850057699234883329223) * 10^40
        + 4983119074400438698294920112504719252750) * 10^40
        + 3022261890230175464488512210079377361071) : ℚ) /
        ((((3 * 10^40
        + 3238255425155550885611090202824363206820) * 10^40
        + 9087961853928327713929535748638080939350) * 10^40
        + 4268177231601485300982098327789109915888) * 10^40
        + 2510998386767416140205474019511598317568)))

noncomputable def batchC05120MinusMidpointP023Error2559 : ℝ := ((12782468215248698626222522329915
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP023BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP023Center2559‖ ≤
          batchC05120MinusMidpointP023Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP023Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP023Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP023Input2559 5 =
      (batchC05120MinusMidpointP023Center2559, ((12782468215248698626222522329915 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP023Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP023Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP023Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP023Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP023Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP023Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP023DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP023Factor2559 * embedPair2542
          batchC05120MinusMidpointP023Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP023Factor2559 : ℝ) *
            batchC05120MinusMidpointP023Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP023Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP023Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP023BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP023Factor2559)

def batchC05120MinusMidpointP024Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-309351029057948556428147) : ℚ) /
        230584300921369395200000000))

def batchC05120MinusMidpointP024Center2559 : RatPair2542 :=
    (((136591909556798276984073866035230871 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-733455424678251963265638299183583) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)))

def batchC05120MinusMidpointP024Factor2559 : RatPair2542 := ((((-((((((((49778 * 10^40
        + 1471569438003210659521426345160187676662) * 10^40
        + 6493539793541624721849985593484881966195) * 10^40
        + 8337827187860702989821184763007468778498) * 10^40
        + 6200278552253897821386667650099238107335) * 10^40
        + 4187446642888295277867469435538599027460) * 10^40
        + 9089883312622397520696022334320775880695) * 10^40
        + 4644416974215776667266211917573038123479) * 10^40
        + 4203304246331393765616305944330131156065)) : ℚ) /
        ((((((((11 * 10^40
        + 478162370788241076007694282639687583167) * 10^40
        + 2687225231487420576272771282544101294577) * 10^40
        + 3855201398249542791308579597247701463658) * 10^40
        + 9799804258855378868373469855755590432196) * 10^40
        + 7129664797525613243297924374506405241426) * 10^40
        + 3374011437479554348863559323241173297527) * 10^40
        + 1265261591484924144576407652550083393295) * 10^40
        + 7097395387310181150403370122408177434624)),
    ((((((224 * 10^40
        + 7461866059288921996011698242815039267566) * 10^40
        + 5900926046085203000702120394125872051022) * 10^40
        + 1263371421314886154828865507183678866976) * 10^40
        + 9940564508347571340951304328749571680689) : ℚ) /
        ((((3 * 10^40
        + 3238255425155550885611090202824363206820) * 10^40
        + 9087961853928327713929535748638080939350) * 10^40
        + 4268177231601485300982098327789109915888) * 10^40
        + 2510998386767416140205474019511598317568)))

noncomputable def batchC05120MinusMidpointP024Error2559 : ℝ := ((12797622634255177825732382283721
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP024BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP024Center2559‖ ≤
          batchC05120MinusMidpointP024Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP024Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP024Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP024Input2559 5 =
      (batchC05120MinusMidpointP024Center2559, ((12797622634255177825732382283721 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP024Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP024Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP024Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP024Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP024Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP024Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP024DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP024Factor2559 * embedPair2542
          batchC05120MinusMidpointP024Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP024Factor2559 : ℝ) *
            batchC05120MinusMidpointP024Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP024Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP024Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP024BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP024Factor2559)

def batchC05120MinusMidpointP025Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-10022692915539018190833) : ℚ) /
        7205759403792793600000000))

def batchC05120MinusMidpointP025Center2559 : RatPair2542 :=
    (((136582476594986886825917417561778935 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-95050976495552222191239751101993) : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)))

def batchC05120MinusMidpointP025Factor2559 : RatPair2542 := ((((-((((((((52 * 10^40
        + 2473363187877796333195936212508809364375) * 10^40
        + 6456271691961717113328380374216507601302) * 10^40
        + 5831583797892028593922301863545574649723) * 10^40
        + 2804209749796423006256409687198632086042) * 10^40
        + 2482507706769712278777082059712261276518) * 10^40
        + 5269827612949437878026957398359989754276) * 10^40
        + 1249617288096265111931250556169068579776) * 10^40
        + 8047980488894803278000592364704234139097)) : ℚ) /
        (((((((107888830440222891675788763947890319905 * 10^40
        + 4367858618390124434156516378205609473920) * 10^40
        + 4857280470115478069132137284762937208460) * 10^40
        + 6044726371346538455926145966656011318781) * 10^40
        + 4421025063278833606682908129271978911368) * 10^40
        + 5804076183044413627293812069651602708298) * 10^40
        + 3663344982022934496234937898098193440813) * 10^40
        + 7653415425182920098779690791135164235776)),
    ((((((2 * 10^40
        + 4271909047242865972286599878900895108864) * 10^40
        + 4077624463466679972926634354364292772139) * 10^40
        + 1182825156707322407227673881573276918269) * 10^40
        + 5619700234619264243718885251780741438857) : ℚ) /
        (((346231827345370321725115522946087116737 * 10^40
        + 7177999602645086747020099330714980009784) * 10^40
        + 9002793512829182138551896857581136561623) * 10^40
        + 8359489566528827251460473687703245815808)))

noncomputable def batchC05120MinusMidpointP025Error2559 : ℝ := ((12816630442442987178675520420357
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP025BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP025Center2559‖ ≤
          batchC05120MinusMidpointP025Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP025Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP025Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP025Input2559 5 =
      (batchC05120MinusMidpointP025Center2559, ((12816630442442987178675520420357 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP025Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP025Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP025Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP025Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP025Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP025Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP025DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP025Factor2559 * embedPair2542
          batchC05120MinusMidpointP025Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP025Factor2559 : ℝ) *
            batchC05120MinusMidpointP025Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP025Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP025Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP025BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP025Factor2559)

def batchC05120MinusMidpointP026Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-20771944281655350607437) : ℚ) /
        14411518807585587200000000))

def batchC05120MinusMidpointP026Center2559 : RatPair2542 := (((34143121207408061096057536912509707
    : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-3151800393100269606912338225238373) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC05120MinusMidpointP026Factor2559 : RatPair2542 := ((((-((((((((224 * 10^40
        + 3947147427191455112327883166147283911218) * 10^40
        + 3823653622147607787987727710124360817276) * 10^40
        + 4363185290106116190570689180432165757228) * 10^40
        + 2036194807427485982194312519774827313874) * 10^40
        + 8500786565766109217491334218560863077141) * 10^40
        + 4921579483262638312247568543808968352634) * 10^40
        + 6362015919284503783117230288235801233318) * 10^40
        + 7948513730242394186527357481484320226785)) : ℚ) /
        (((((((431555321760891566703155055791561279621 * 10^40
        + 7471434473560497736626065512822437895681) * 10^40
        + 9429121880461912276528549139051748833842) * 10^40
        + 4178905485386153823704583866624045275125) * 10^40
        + 7684100253115334426731632517087915645474) * 10^40
        + 3216304732177654509175248278606410833193) * 10^40
        + 4653379928091737984939751592392773763255) * 10^40
        + 613661700731680395118763164540656943104)),
    ((((((5 * 10^40
        + 303321331642416556247589994514044174802) * 10^40
        + 5627291210277834612703894845067415750499) * 10^40
        + 6762093588721279945640235083815738539122) * 10^40
        + 2619638176429356204703181217906781603973) : ℚ) /
        (((692463654690740643450231045892174233475 * 10^40
        + 4355999205290173494040198661429960019569) * 10^40
        + 8005587025658364277103793715162273123247) * 10^40
        + 6718979133057654502920947375406491631616)))

noncomputable def batchC05120MinusMidpointP026Error2559 : ℝ := ((6418031807171708803062840175333 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05120MinusMidpointP026BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP026Center2559‖ ≤
          batchC05120MinusMidpointP026Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP026Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP026Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP026Input2559 5 =
      (batchC05120MinusMidpointP026Center2559, ((6418031807171708803062840175333 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP026Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP026Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP026Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP026Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP026Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP026Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP026DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP026Factor2559 * embedPair2542
          batchC05120MinusMidpointP026Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP026Factor2559 : ℝ) *
            batchC05120MinusMidpointP026Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP026Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP026Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP026BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP026Factor2559)

def batchC05120MinusMidpointP027Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-43640783619197408678627) : ℚ) /
        28823037615171174400000000))

def batchC05120MinusMidpointP027Center2559 : RatPair2542 :=
    (((136557439837211404921580478069081041 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-6621527053354473171925480835344187) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05120MinusMidpointP027Factor2559 : RatPair2542 := ((((-((((((((990 * 10^40
        + 3675650025872012935356885512083065549707) * 10^40
        + 9288238326293713904196050486441346850217) * 10^40
        + 1290809785057843381786995254326616966188) * 10^40
        + 8994958995379204990985738892926742263362) * 10^40
        + 4975073932169446513144420792020187093397) * 10^40
        + 101529831852914341361124807050757968316) * 10^40
        + 2387510797679852044578930244289320184296) * 10^40
        + 7642109753654556281923992848926450122497)) : ℚ) /
        (((((((1726221287043566266812620223166245118486 * 10^40
        + 9885737894241990946504262051289751582727) * 10^40
        + 7716487521847649106114196556206995335369) * 10^40
        + 6715621941544615294818335466496181100503) * 10^40
        + 736401012461337706926530068351662581897) * 10^40
        + 2865218928710618036700993114425643332773) * 10^40
        + 8613519712366951939759006369571095053020) * 10^40
        + 2454646802926721580475052658162627772416)),
    ((((((31 * 10^40
        + 7054051146273161333019637936329370514321) * 10^40
        + 2705860567684837478263346553770659704008) * 10^40
        + 8548667567547040345038297949355427905582) * 10^40
        + 2904034259867424206032950850012934168449) : ℚ) /
        (((4154781928144443860701386275353045400852 * 10^40
        + 6135995231741040964241191968579760117418) * 10^40
        + 8033522153950185662622762290973638739486) * 10^40
        + 313874798345927017525684252438949789696)))

noncomputable def batchC05120MinusMidpointP027Error2559 : ℝ := ((6432060228422914227434571498065 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC05120MinusMidpointP027BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP027Center2559‖ ≤
          batchC05120MinusMidpointP027Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP027Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP027Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP027Input2559 5 =
      (batchC05120MinusMidpointP027Center2559, ((6432060228422914227434571498065 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP027Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP027Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP027Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP027Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP027Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP027Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP027DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP027Factor2559 * embedPair2542
          batchC05120MinusMidpointP027Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP027Factor2559 : ℝ) *
            batchC05120MinusMidpointP027Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP027Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP027Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP027BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP027Factor2559)

def batchC05120MinusMidpointP028Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-177883892884016178388727) : ℚ) /
        115292150460684697600000000))

def batchC05120MinusMidpointP028Center2559 : RatPair2542 :=
    (((136551278801328968125284211698450933 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-6747388615875296871308154105776601) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05120MinusMidpointP028Factor2559 : RatPair2542 := ((((-((((((((16453 * 10^40
        + 8593685228014259787616263615363417376099) * 10^40
        + 4196284964542797012983862899725482567012) * 10^40
        + 7575933442149569742718242828366994660850) * 10^40
        + 4313755451334278635319838355925629176909) * 10^40
        + 1976757263554126581350448346182949856422) * 10^40
        + 2452065569144705921907190328112316640255) * 10^40
        + 360010547865281602570791459821202983418) * 10^40
        + 9121448296275508262238814842786639598537)) : ℚ) /
        ((((((((2 * 10^40
        + 7619540592697060269001923570659921895791) * 10^40
        + 8171806307871855144068192820636025323644) * 10^40
        + 3463800349562385697827144899311925365914) * 10^40
        + 7449951064713844717093367463938897608049) * 10^40
        + 1782416199381403310824481093626601310356) * 10^40
        + 5843502859369888587215889830810293324381) * 10^40
        + 7816315397871231036144101913137520848323) * 10^40
        + 9274348846827545287600842530602044358656)),
    ((((((129 * 10^40
        + 2341800382737127928973088011632518607697) * 10^40
        + 3561417648494923379847356322736255688560) * 10^40
        + 3137055222141404605647711483932313517172) * 10^40
        + 6880418008828339338515547923876976717149) : ℚ) /
        ((((1 * 10^40
        + 6619127712577775442805545101412181603410) * 10^40
        + 4543980926964163856964767874319040469675) * 10^40
        + 2134088615800742650491049163894554957944) * 10^40
        + 1255499193383708070102737009755799158784)))

noncomputable def batchC05120MinusMidpointP028Error2559 : ℝ := ((12875233149225421318269317110253
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP028BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP028Center2559‖ ≤
          batchC05120MinusMidpointP028Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP028Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP028Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP028Input2559 5 =
      (batchC05120MinusMidpointP028Center2559, ((12875233149225421318269317110253 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP028Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP028Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP028Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP028Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP028Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP028Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP028DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP028Factor2559 * embedPair2542
          batchC05120MinusMidpointP028Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP028Factor2559 : ℝ) *
            batchC05120MinusMidpointP028Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP028Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP028Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP028BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP028Factor2559)

def batchC05120MinusMidpointP029Input2559 : RatPair2542 := ((((-((770946 * 10^40
        + 8545048467636555398699602121832667479770) * 10^40
        + 5547044673152399795449077577591264396923)) : ℚ) /
        ((822334 * 10^40
        + 5047995532150138752490647359331044753526) * 10^40
        + 6704968814767496342579897453772800000000)),
    (((-182939534351242879487659) : ℚ) /
        115292150460684697600000000))

def batchC05120MinusMidpointP029Center2559 : RatPair2542 :=
    (((136541676280684090664405603700946539 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-6938993721915965101614225364819361) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC05120MinusMidpointP029Factor2559 : RatPair2542 := ((((-((((((((17401 * 10^40
        + 4657153940328161084465003294602396740900) * 10^40
        + 6148974008229778341808568522598618903173) * 10^40
        + 6727651367213489619543782099093175301323) * 10^40
        + 2379233008516939686098080957191216422386) * 10^40
        + 8022186886881494381807683212815047093034) * 10^40
        + 8753510496146377678773920895923354777378) * 10^40
        + 1768212747014630707785269256724557236054) * 10^40
        + 7632344982095082993313370486986947111025)) : ℚ) /
        ((((((((2 * 10^40
        + 7619540592697060269001923570659921895791) * 10^40
        + 8171806307871855144068192820636025323644) * 10^40
        + 3463800349562385697827144899311925365914) * 10^40
        + 7449951064713844717093367463938897608049) * 10^40
        + 1782416199381403310824481093626601310356) * 10^40
        + 5843502859369888587215889830810293324381) * 10^40
        + 7816315397871231036144101913137520848323) * 10^40
        + 9274348846827545287600842530602044358656)),
    ((((((132 * 10^40
        + 9071471011799789422123247157443245108521) * 10^40
        + 2162298333998821676996560716134409735895) * 10^40
        + 9549658820515204248089488303949387042625) * 10^40
        + 8492508448447722042592316769337083300633) : ℚ) /
        ((((1 * 10^40
        + 6619127712577775442805545101412181603410) * 10^40
        + 4543980926964163856964767874319040469675) * 10^40
        + 2134088615800742650491049163894554957944) * 10^40
        + 1255499193383708070102737009755799158784)))

noncomputable def batchC05120MinusMidpointP029Error2559 : ℝ := ((12892156508049354513448791227067
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC05120MinusMidpointP029BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP029Center2559‖ ≤
          batchC05120MinusMidpointP029Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchC05120MinusMidpointP029Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC05120MinusMidpointP029Input2559]
  have hs : compactExp2547 batchC05120MinusMidpointP029Input2559 5 =
      (batchC05120MinusMidpointP029Center2559, ((12892156508049354513448791227067 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC05120MinusMidpointP029Input2559 5).2 : ℝ) =
      batchC05120MinusMidpointP029Error2559 := by
    rw [hs]
    norm_num [batchC05120MinusMidpointP029Error2559]
  have h := compactExp_error2547 batchC05120MinusMidpointP029Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      batchC05120MinusMidpointPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchC05120MinusMidpointP029Input2559)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC05120MinusMidpointPosition2559, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC05120MinusMidpointP029Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC05120MinusMidpointP029DerivativeError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP029Factor2559 * embedPair2542
          batchC05120MinusMidpointP029Center2559‖ ≤
        (pairMagnitude2542 batchC05120MinusMidpointP029Factor2559 : ℝ) *
            batchC05120MinusMidpointP029Error2559 := by
  have hx : |batchC05120MinusMidpointPosition2559| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC05120MinusMidpointPosition2559, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchC05120MinusMidpointPosition2559 = embedPair2542
          batchC05120MinusMidpointP029Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC05120MinusMidpointPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchC05120MinusMidpointP029Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC05120MinusMidpointP029BaseError2559
    (embedPair_magnitude2542 batchC05120MinusMidpointP029Factor2559)

theorem batchC05120MinusMidpointGrid2559 :
    -stripRadius2303 + ((10241 : ℝ) /
        2) * (2 * stripRadius2303 / 10240) =
      batchC05120MinusMidpointPosition2559 := by
  norm_num [stripRadius2303, batchC05120MinusMidpointPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP000DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP001DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP002DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP003DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP004DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP005DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP006DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP007DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP008DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP009DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP010DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP011DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP012DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP013DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP014DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP015DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP016DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP017DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP018DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP019DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP020DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP021DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP022DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP023DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP024DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP025DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP026DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP027DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP028DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointP029DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusMidpointGrid2559
