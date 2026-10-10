import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchN02705MinusPosition2654 : ℝ := (((-31653888483) : ℝ) /
        10240000000)

theorem batchN02705MinusZero2654 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchN02705MinusP000Center2654 : RatPair2542 := (0, 0)

def batchN02705MinusP000Factor2654 : RatPair2542 := (0, 0)

noncomputable def batchN02705MinusP000Error2654 : ℝ := 0

theorem batchN02705MinusP000Exterior2654 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02705MinusPosition2654 = 0
        := by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |batchN02705MinusPosition2654| := by
    norm_num [storedWidth, batchN02705MinusPosition2654]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem batchN02705MinusP000BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP000Center2654‖ ≤ batchN02705MinusP000Error2654 := by
  rw [batchN02705MinusP000Exterior2654]
  norm_num [batchN02705MinusP000Center2654, batchN02705MinusP000Error2654,
      batchN02705MinusZero2654]

theorem batchN02705MinusP000DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP000Factor2654 * embedPair2542 batchN02705MinusP000Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP000Factor2654 : ℝ) * batchN02705MinusP000Error2654 :=
            by
  rw [batchN02705MinusP000Exterior2654]
  norm_num [batchN02705MinusP000Factor2654, batchN02705MinusP000Center2654,
      batchN02705MinusP000Error2654,
      batchN02705MinusZero2654, pairMagnitude2542]

def batchN02705MinusP001Input2654 : RatPair2542 := ((((-(2972220902592775860753336338870765187961
    * 10^40
        + 1585476530521012854490327853635425132317)) : ℚ) /
        (8511279604154028674011082907130390598740 * 10^40
        + 8004112173150622382000883902709760000000)),
    ((174865292075716174968560007 : ℚ) /
        737869762948382064640000000))

def batchN02705MinusP001Center2654 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN02705MinusP001Factor2654 : RatPair2542 :=
    (((((((((((((215006331636777590595223681092785369997
    *
    10^40
        + 8849600843316585128119949396276987376160) * 10^40
        + 7686751414503121454877258364101575797479) * 10^40
        + 250082293699002361236257243735940168997) * 10^40
        + 1404145937929569525392381359901165106287) * 10^40
        + 743268910046518409928958622660805388343) * 10^40
        + 8374954746306377237824363704312438632597) * 10^40
        + 2110719821932268024425809396936643366476) * 10^40
        + 7871778716542851205262983419904817215335) * 10^40
        + 6350109041801631828831363034829961993994) * 10^40
        + 407559663942897944864164683883265746427) : ℚ) /
        ((((((((((1132972203575183607657699039993 * 10^40
        + 6491833452607807492952598703079929206110) * 10^40
        + 4509716371142267435601841872568732035532) * 10^40
        + 8289337298834854521985444312821215365469) * 10^40
        + 6338916412706163177396831571512875575047) * 10^40
        + 1783174456681172731430670540738327297622) * 10^40
        + 8433544854179190223047662688073069563968) * 10^40
        + 962997700770929131541885425281157677069) * 10^40
        + 7931630696122394614099791109554383344118) * 10^40
        + 1850803414207391406629327092230594501633) * 10^40
        + 212520284245473216617427760902326714368)),
    (((-(((((((47995858100180079359909564596231527092 * 10^40
        + 2622958051049113340669445151771523374132) * 10^40
        + 8938735628769035139249317670564911646774) * 10^40
        + 920263371619875477201856981874324914527) * 10^40
        + 3196846678915241732723275824678012407172) * 10^40
        + 7922480609197035821873200003811789845417) * 10^40
        + 3858755605774724902575473490292738725988) * 10^40
        + 7900569693221550687638339372374900640363)) : ℚ) /
        (((((((1210066301185917523975673569179 * 10^40
        + 2681722041925626698455166965805257104281) * 10^40
        + 1208170857874247021899808841410698434669) * 10^40
        + 3373386295117667286694977611062069551399) * 10^40
        + 3885236765510692808304426309135639329317) * 10^40
        + 1128953645323180743947564671424632773384) * 10^40
        + 4397914037919657895580364138503991013291) * 10^40
        + 4450464903138141019350243293830422986752)))

noncomputable def batchN02705MinusP001Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP001BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP001Center2654‖ ≤ batchN02705MinusP001Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP001Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP001Input2654]
  have hs : compactExp2547 batchN02705MinusP001Input2654 9 =
      (batchN02705MinusP001Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP001Input2654 9).2 : ℝ) =
      batchN02705MinusP001Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP001Error2654]
  have h := compactExp_error2547 batchN02705MinusP001Input2654 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          batchN02705MinusP001Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP001Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP001DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP001Factor2654 * embedPair2542 batchN02705MinusP001Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP001Factor2654 : ℝ) * batchN02705MinusP001Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP001Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP001Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP001BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP001Factor2654)

def batchN02705MinusP002Input2654 : RatPair2542 := ((((-(1558232809265543759449685049388990963208
    * 10^40
        + 5657148282816822161277233008769014177453)) : ℚ) /
        (6677151314258110391825028471093402075161 * 10^40
        + 8148315816099404395428715739217920000000)),
    (((-174865292075716174968560007) : ℚ) /
        368934881474191032320000000))

def batchN02705MinusP002Center2654 : RatPair2542 := ((((-6232910466508290662095) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-7671910554999950297919) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchN02705MinusP002Factor2654 : RatPair2542 :=
    ((((-((((((((((15259535016456029579412485951127196072
    *
    10^40
        + 4327251058720114730524095994840949329693) * 10^40
        + 4213344893277620923580466576110119894229) * 10^40
        + 6821514925665584911509569336381497705625) * 10^40
        + 9527250316831962254229752151976418166721) * 10^40
        + 9127563346946786143536906899187993811376) * 10^40
        + 1202300462620784153376071674000704061345) * 10^40
        + 1525529174442341480727700237334811837423) * 10^40
        + 7029507896893562183716472828820443087422) * 10^40
        + 5411553980992384270822059469528500256486) * 10^40
        + 8737881427009589848245611851200923674051)) : ℚ) /
        ((((((((((118324705181966213225404177752985 * 10^40
        + 4896477334946327883078790355126404407719) * 10^40
        + 6775601539627349669476792970904997349101) * 10^40
        + 7616502142517740547002435835388749367676) * 10^40
        + 3217841868461481917784293704733390270298) * 10^40
        + 1129528240625711234611254537480891666445) * 10^40
        + 2045631427152956949691144021471144949938) * 10^40
        + 9993415071461812747396106629597852709068) * 10^40
        + 5577346867007241220300999122382192440865) * 10^40
        + 168640111034114447724665945191972786731) * 10^40
        + 4066046135299679783721789859418882441216)),
    (((((((((938171923289654869091478793585848615 * 10^40
        + 5021399694011160778384447852161608935174) * 10^40
        + 6664499289082884799455242102867556053902) * 10^40
        + 2709649198430975721896521425529826595236) * 10^40
        + 7941069218398941860138398879883213136439) * 10^40
        + 5954669359626343294218090843686615311223) * 10^40
        + 6017540073915211270773396481383133500488) * 10^40
        + 1945771760465112990181412068797546240043) : ℚ) /
        (((((((7333555627367605313302747274255 * 10^40
        + 4230621740639485900325535169952920121634) * 10^40
        + 285231706224685509938930898663878477818) * 10^40
        + 8893606292853513743853522146828877857591) * 10^40
        + 2204499809411295592911344401681796604628) * 10^40
        + 3140749146862784358395306427605334919676) * 10^40
        + 2791481135787425155401076860771342770982) * 10^40
        + 2092972309572356174072150004146972393472)))

noncomputable def batchN02705MinusP002Error2654 : ℝ := ((62258049251692668505 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP002BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP002Center2654‖ ≤ batchN02705MinusP002Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP002Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP002Input2654]
  have hs : compactExp2547 batchN02705MinusP002Input2654 8 =
      (batchN02705MinusP002Center2654, ((62258049251692668505 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP002Input2654 8).2 : ℝ) =
      batchN02705MinusP002Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP002Error2654]
  have h := compactExp_error2547 batchN02705MinusP002Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchN02705MinusP002Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP002Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP002DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP002Factor2654 * embedPair2542 batchN02705MinusP002Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP002Factor2654 : ℝ) * batchN02705MinusP002Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP002Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP002Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP002BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP002Factor2654)

def batchN02705MinusP003Input2654 : RatPair2542 := ((((-((550 * 10^40
        + 3595636945123166861610172112009740757253) * 10^40
        + 4707504622032470410174329256036448054837)) : ℚ) /
        ((3259 * 10^40
        + 8976654890313777338921755240451858920673) * 10^40
        + 3765349097629268219761063158087680000000)),
    (((-174865292075716174968560007) : ℚ) /
        368934881474191032320000000))

def batchN02705MinusP003Center2654 : RatPair2542 := ((((-93385857423547319201975676215) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-229891941848088526221276769381) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN02705MinusP003Factor2654 : RatPair2542 := ((((-(((((((((((9858237868584205454 * 10^40
        + 9317000494350809075820620190046312999424) * 10^40
        + 6665915599331299067607337557076570013576) * 10^40
        + 4676324455247164912908933286477768023375) * 10^40
        + 5833797817983916347015878456286504437626) * 10^40
        + 5855855118797407787152817486336609474382) * 10^40
        + 5203987233587545756847450892412039553630) * 10^40
        + 5698869035558916667662510687750846409779) * 10^40
        + 6773150351527702308223378219136510259838) * 10^40
        + 9603208911783488667794055872370237314413) * 10^40
        + 7957055800525144377453048383956125968761) * 10^40
        + 1716448034978255104984182052382191925971)) : ℚ) /
        (((((((((((160232985266930 * 10^40
        + 319046836567256260585280312878523826435) * 10^40
        + 1832878968192066548533219679220439203688) * 10^40
        + 1925988730906863672186401722922884200977) * 10^40
        + 273908342599783083374420468959435409937) * 10^40
        + 1742812261532499794209530716080684505708) * 10^40
        + 3266543410078223199852886526674326246528) * 10^40
        + 4898438188999023381104784781819715569173) * 10^40
        + 1170061631266839351878708594789278933903) * 10^40
        + 6559094179506059716032921456292757580347) * 10^40
        + 2812204674755067826814171930456210721964) * 10^40
        + 2708316968241121237029064766137288359936)),
    (((-((((((((16586906845 * 10^40
        + 548815268554478677278231160528145327798) * 10^40
        + 9445796157367724842048468138000427967935) * 10^40
        + 763366857954535922303731992987856609034) * 10^40
        + 9175353630311913575473036312085599376844) * 10^40
        + 1997078918798566095081625378941941667761) * 10^40
        + 8011664500901912409626060010788654788444) * 10^40
        + 2492042614440439657964854281334538349875) * 10^40
        + 8286291656520476776966730632147300313717)) : ℚ) /
        ((((((((416644 * 10^40
        + 4354296947487680737149243727972695605280) * 10^40
        + 3351563649125468369519960427932317719954) * 10^40
        + 9208396908792724119173932896696091628015) * 10^40
        + 6878887255792533719023297948625738711042) * 10^40
        + 323205126263254295309982701612177901342) * 10^40
        + 5590784271387336653137740259611230204217) * 10^40
        + 442561340593389728581917588026940257276) * 10^40
        + 207865507568609095150666401047413522432)))

noncomputable def batchN02705MinusP003Error2654 : ℝ := ((874492453823048358099631199 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP003BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP003Center2654‖ ≤ batchN02705MinusP003Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP003Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP003Input2654]
  have hs : compactExp2547 batchN02705MinusP003Input2654 8 =
      (batchN02705MinusP003Center2654, ((874492453823048358099631199 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP003Input2654 8).2 : ℝ) =
      batchN02705MinusP003Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP003Error2654]
  have h := compactExp_error2547 batchN02705MinusP003Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchN02705MinusP003Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP003Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP003DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP003Factor2654 * embedPair2542 batchN02705MinusP003Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP003Factor2654 : ℝ) * batchN02705MinusP003Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP003Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP003Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP003BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP003Factor2654)

def batchN02705MinusP004Input2654 : RatPair2542 := ((((-((17 * 10^40
        + 2533280590083662039217955279786228756184) * 10^40
        + 5273242798277482655099909987298882195197)) : ℚ) /
        ((119 * 10^40
        + 2496410941960060508819208543369047417438) * 10^40
        + 2834992468434524816007071221678080000000)),
    ((174865292075716174968560007 : ℚ) /
        368934881474191032320000000))

def batchN02705MinusP004Center2654 : RatPair2542 := ((((-5644135271377406361162294963633) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((55577632561868580858707835001315 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchN02705MinusP004Factor2654 : RatPair2542 := ((((-(((((((((((1673376115 * 10^40
        + 6297679792103935561445022902027351692514) * 10^40
        + 6286308758511569078603901201718693989328) * 10^40
        + 5415133970917329628972381261974408323927) * 10^40
        + 1497310013633544357879695079696135109861) * 10^40
        + 2306911432257691728850042314099553598104) * 10^40
        + 5828610230874487852712069373655501165831) * 10^40
        + 4923476455333642200954265277476816949877) * 10^40
        + 7079982169409429483453466706542975312858) * 10^40
        + 6806487354361747761754323262820601469883) * 10^40
        + 2586104200084236915803245209356596009633) * 10^40
        + 1147584167660597456100174127080982445893)) : ℚ) /
        (((((((((((54849 * 10^40
        + 4865021579547709526671239781442371147558) * 10^40
        + 7992448807111464468600533771953187691298) * 10^40
        + 2459692338126195241091283586598483955709) * 10^40
        + 1241500423805244416879431277388019631184) * 10^40
        + 3124518779058240256281498490371209322749) * 10^40
        + 6042464955272675898922372846825659840074) * 10^40
        + 2576201104617852514911257819341703905212) * 10^40
        + 1015234860272672510434016589553679221920) * 10^40
        + 2452084115319738633966907813220101009221) * 10^40
        + 8163277496452337018673641393906512415445) * 10^40
        + 9641845801044272857926270690189522239488)),
    ((((((((((41679 * 10^40
        + 370861053145150417495809788015806171913) * 10^40
        + 1339034681863945012618597770498097284726) * 10^40
        + 5332529415514800853076616204337962060731) * 10^40
        + 5809598392560011854880901541076366407621) * 10^40
        + 5443910902159069572731506565806742180246) * 10^40
        + 77491813426019529947854561503606077853) * 10^40
        + 1097079590353909800633511921597994351259) * 10^40
        + 9851142003394611985278692035856603873557) : ℚ) /
        (((((((7460673605955816542458117568629812059566 * 10^40
        + 753149658096737297940336376873415714926) * 10^40
        + 2185413610951337288868068116428955357463) * 10^40
        + 1004713682398729590798229364557777041231) * 10^40
        + 4265946591226983634517376571990408243747) * 10^40
        + 4181133674025689065290330092697317026495) * 10^40
        + 3928972981559920228251714141835030032291) * 10^40
        + 3331119694468934350883640470600859779072)))

noncomputable def batchN02705MinusP004Error2654 : ℝ := ((412739842713913026403732476439 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP004BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP004Center2654‖ ≤ batchN02705MinusP004Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP004Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP004Input2654]
  have hs : compactExp2547 batchN02705MinusP004Input2654 8 =
      (batchN02705MinusP004Center2654, ((412739842713913026403732476439 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP004Input2654 8).2 : ℝ) =
      batchN02705MinusP004Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP004Error2654]
  have h := compactExp_error2547 batchN02705MinusP004Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchN02705MinusP004Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP004Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP004DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP004Factor2654 * embedPair2542 batchN02705MinusP004Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP004Factor2654 : ℝ) * batchN02705MinusP004Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP004Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP004Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP004BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP004Factor2654)

def batchN02705MinusP005Center2654 : RatPair2542 := (0, 0)

def batchN02705MinusP005Factor2654 : RatPair2542 := (0, 0)

noncomputable def batchN02705MinusP005Error2654 : ℝ := 0

theorem batchN02705MinusP005Exterior2654 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02705MinusPosition2654 = 0
        := by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |batchN02705MinusPosition2654| := by
    norm_num [storedWidth, batchN02705MinusPosition2654]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem batchN02705MinusP005BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP005Center2654‖ ≤ batchN02705MinusP005Error2654 := by
  rw [batchN02705MinusP005Exterior2654]
  norm_num [batchN02705MinusP005Center2654, batchN02705MinusP005Error2654,
      batchN02705MinusZero2654]

theorem batchN02705MinusP005DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP005Factor2654 * embedPair2542 batchN02705MinusP005Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP005Factor2654 : ℝ) * batchN02705MinusP005Error2654 :=
            by
  rw [batchN02705MinusP005Exterior2654]
  norm_num [batchN02705MinusP005Factor2654, batchN02705MinusP005Center2654,
      batchN02705MinusP005Error2654,
      batchN02705MinusZero2654, pairMagnitude2542]

def batchN02705MinusP006Input2654 : RatPair2542 := ((((-1009401942711546853650056001574587) : ℚ) /
        1771445797272420243763363840000000),
    ((0 : ℚ) /
        1))

def batchN02705MinusP006Center2654 : RatPair2542 := (((30816524370707993 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN02705MinusP006Factor2654 : RatPair2542 := ((((((246528499761 * 10^40
        + 5945895148954727966707887400945487153689) * 10^40
        + 3268008384153569414535656602412829739156) * 10^40
        + 9303291604334919664912712379248637316239) : ℚ) /
        (((761759 * 10^40
        + 1249009437650804866752069399632787087383) * 10^40
        + 4447336227782188969496765165778824044969) * 10^40
        + 1424534633143992440698300966010901470088)),
    ((0 : ℚ) /
        1))

noncomputable def batchN02705MinusP006Error2654 : ℝ := ((4933337008969 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN02705MinusP006BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP006Center2654‖ ≤ batchN02705MinusP006Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP006Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP006Input2654]
  have hs : compactExp2547 batchN02705MinusP006Input2654 7 =
      (batchN02705MinusP006Center2654, ((4933337008969 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP006Input2654 7).2 : ℝ) =
      batchN02705MinusP006Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP006Error2654]
  have h := compactExp_error2547 batchN02705MinusP006Input2654 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          batchN02705MinusP006Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP006Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP006DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP006Factor2654 * embedPair2542 batchN02705MinusP006Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP006Factor2654 : ℝ) * batchN02705MinusP006Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP006Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP006Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP006BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP006Factor2654)

def batchN02705MinusP007Input2654 : RatPair2542 := ((((-((550 * 10^40
        + 3595636945123166861610172112009740757253) * 10^40
        + 4707504622032470410174329256036448054837)) : ℚ) /
        ((814 * 10^40
        + 9744163722578444334730438810112964730168) * 10^40
        + 3441337274407317054940265789521920000000)),
    ((0 : ℚ) /
        1))

def batchN02705MinusP007Center2654 : RatPair2542 := (((248135493820243347566162584705 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN02705MinusP007Factor2654 : RatPair2542 := (((((((((((((664981004326827406090034792546 *
    10^40
        + 1449544998765484708584397445412555443563) * 10^40
        + 1661110661181633124823857580292168626836) * 10^40
        + 6517513012040955246644667449749318309679) * 10^40
        + 3551047856974121996605642118797613337448) * 10^40
        + 2015454813060361985178616047122619027325) * 10^40
        + 7513616056573771728867233071390135394764) * 10^40
        + 4242858411322607684242579765583896168652) * 10^40
        + 47446801401683165391988541514925673213) * 10^40
        + 8946582846839630156969482144928996127961) * 10^40
        + 8326756842866085299297203248179311889673) : ℚ) /
        ((((((((((323587936778074810624928597 * 10^40
        + 7041391562582372665447892040056688658435) * 10^40
        + 5579675248922695717904893237989490718119) * 10^40
        + 6421496300048400024609620363514139515367) * 10^40
        + 5898035918737446932060028034075904744237) * 10^40
        + 1386844588073865612980154142897600739696) * 10^40
        + 3577214040509855348205558657108766117753) * 10^40
        + 3101849454267883533369397027076878051402) * 10^40
        + 6073546179323562633695403356015981162282) * 10^40
        + 5933023177067042834718823669622690887173) * 10^40
        + 7650974889071317605622374014565504882616)),
    ((0 : ℚ) /
        1))

noncomputable def batchN02705MinusP007Error2654 : ℝ := ((17152272637126015450671225 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN02705MinusP007BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP007Center2654‖ ≤ batchN02705MinusP007Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP007Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP007Input2654]
  have hs : compactExp2547 batchN02705MinusP007Input2654 6 =
      (batchN02705MinusP007Center2654, ((17152272637126015450671225 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP007Input2654 6).2 : ℝ) =
      batchN02705MinusP007Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP007Error2654]
  have h := compactExp_error2547 batchN02705MinusP007Input2654 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          batchN02705MinusP007Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP007Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP007DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP007Factor2654 * embedPair2542 batchN02705MinusP007Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP007Factor2654 : ℝ) * batchN02705MinusP007Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP007Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP007Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP007BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP007Factor2654)

def batchN02705MinusP008Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((125937256369443206862002451 : ℚ) /
        23611832414348226068480000000))

def batchN02705MinusP008Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP008Factor2654 : RatPair2542 := ((((((((((((((133269921672168654406649066 *
    10^40
        + 2192059775414773617662552238122131674878) * 10^40
        + 6660552761385713327725546965595761650509) * 10^40
        + 2818538173696335907968447382715254104762) * 10^40
        + 7143990081756831490041357005187760698332) * 10^40
        + 2489291199467073249611896502662765215081) * 10^40
        + 7405188190892211212945649297958368325229) * 10^40
        + 2440696882129893764987754753233778804940) * 10^40
        + 6495770437439892111805394278851911596055) * 10^40
        + 7412882614830186173971408178590756334655) * 10^40
        + 6133580248613198482956734918662623135101) * 10^40
        + 9396831565070691718506252595687347082323) : ℚ) /
        (((((((((((91370075 * 10^40
        + 5369856382079511145362760177770391954073) * 10^40
        + 6863799733247935183422311886099187510088) * 10^40
        + 56722424169355064983529350378976658020) * 10^40
        + 1870937184641896054643156099467659118938) * 10^40
        + 2785646246247786246192559242102071235980) * 10^40
        + 6016104248240819238798931282190638826) * 10^40
        + 2520840650270430477395536088515291595) * 10^40
        + 3625651238273108947730478640746288596230) * 10^40
        + 3830938543665613328311817787431081294147) * 10^40
        + 96004409712652253572673266082485308163) * 10^40
        + 3388025918557163832192551534416250273792)),
    (((-((((((((18157779151134227 * 10^40
        + 6708593852921886773362170846804041841852) * 10^40
        + 4602824485306164686647203864002559137784) * 10^40
        + 8802865831109086736841263549314350616252) * 10^40
        + 2562900843463122151709275238213613929435) * 10^40
        + 9010515268357587339689344724679022613076) * 10^40
        + 9764444797852607585254321911877198779955) * 10^40
        + 7506404062002894563429116009498422210624) * 10^40
        + 2769915166613050473338803579604025827311)) : ℚ) /
        ((((((((332 * 10^40
        + 8503198671069134801066570549085920337757) * 10^40
        + 4203644419032788885390778162383072654747) * 10^40
        + 9018590182506974425683821990136498606967) * 10^40
        + 9256339635336733243781980967902582107569) * 10^40
        + 3296995131750770409092462938544724331530) * 10^40
        + 8597807270330783543151352678104397121653) * 10^40
        + 5126559930285918110399220738075516490025) * 10^40
        + 347107616111286168755562644172236128256)))

noncomputable def batchN02705MinusP008Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP008BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP008Center2654‖ ≤ batchN02705MinusP008Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP008Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP008Input2654]
  have hs : compactExp2547 batchN02705MinusP008Input2654 13 =
      (batchN02705MinusP008Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP008Input2654 13).2 : ℝ) =
      batchN02705MinusP008Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP008Error2654]
  have h := compactExp_error2547 batchN02705MinusP008Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP008Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP008Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP008DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP008Factor2654 * embedPair2542 batchN02705MinusP008Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP008Factor2654 : ℝ) * batchN02705MinusP008Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP008Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP008Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP008BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP008Factor2654)

def batchN02705MinusP009Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((187301696272790732683750413 : ℚ) /
        23611832414348226068480000000))

def batchN02705MinusP009Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP009Factor2654 : RatPair2542 := ((((((((((((((133269921596877067795358705 *
    10^40
        + 1250855895735437700443724768078203198717) * 10^40
        + 7884414083153485789627141327580304878214) * 10^40
        + 3213379928441107184763328793984586039530) * 10^40
        + 1965259175402897349876423799087624627576) * 10^40
        + 4485210246982425728954261356872721283352) * 10^40
        + 9832065478003159463959672063905374407492) * 10^40
        + 2579871687158002115819336423824224280903) * 10^40
        + 8490254889517043991176197351032349719940) * 10^40
        + 5743107435737823589369666180118680849316) * 10^40
        + 5422491890586880748467878877766183816426) * 10^40
        + 7291108529798013728468267321330240652819) : ℚ) /
        (((((((((((91370075 * 10^40
        + 5369856382079511145362760177770391954073) * 10^40
        + 6863799733247935183422311886099187510088) * 10^40
        + 56722424169355064983529350378976658020) * 10^40
        + 1870937184641896054643156099467659118938) * 10^40
        + 2785646246247786246192559242102071235980) * 10^40
        + 6016104248240819238798931282190638826) * 10^40
        + 2520840650270430477395536088515291595) * 10^40
        + 3625651238273108947730478640746288596230) * 10^40
        + 3830938543665613328311817787431081294147) * 10^40
        + 96004409712652253572673266082485308163) * 10^40
        + 3388025918557163832192551534416250273792)),
    (((-((((((((27005375004866161 * 10^40
        + 694861080784000789836236512666815818505) * 10^40
        + 2657902407794857423834234723326191985220) * 10^40
        + 6297952231994898511793533136189374318158) * 10^40
        + 3847232153254395609037492699496053668115) * 10^40
        + 8011764809852419037976797269013524705449) * 10^40
        + 4980476083195296166007007487754748262304) * 10^40
        + 1830856940839774628841597467354922153143) * 10^40
        + 3125480412163218028611155996839525604081)) : ℚ) /
        ((((((((332 * 10^40
        + 8503198671069134801066570549085920337757) * 10^40
        + 4203644419032788885390778162383072654747) * 10^40
        + 9018590182506974425683821990136498606967) * 10^40
        + 9256339635336733243781980967902582107569) * 10^40
        + 3296995131750770409092462938544724331530) * 10^40
        + 8597807270330783543151352678104397121653) * 10^40
        + 5126559930285918110399220738075516490025) * 10^40
        + 347107616111286168755562644172236128256)))

noncomputable def batchN02705MinusP009Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP009BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP009Center2654‖ ≤ batchN02705MinusP009Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP009Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP009Input2654]
  have hs : compactExp2547 batchN02705MinusP009Input2654 13 =
      (batchN02705MinusP009Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP009Input2654 13).2 : ℝ) =
      batchN02705MinusP009Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP009Error2654]
  have h := compactExp_error2547 batchN02705MinusP009Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP009Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP009Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP009DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP009Factor2654 * embedPair2542 batchN02705MinusP009Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP009Factor2654 : ℝ) * batchN02705MinusP009Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP009Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP009Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP009BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP009Factor2654)

def batchN02705MinusP010Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((111420588356197715176385643 : ℚ) /
        11805916207174113034240000000))

def batchN02705MinusP010Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP010Factor2654 : RatPair2542 := ((((((((((((((33317480384945448661055144 *
    10^40
        + 7102864609955907076935660539657554442853) * 10^40
        + 6204307205902731994811109671029380187081) * 10^40
        + 394768047282874358477564511923547574359) * 10^40
        + 9049195884117908606764176839481200741929) * 10^40
        + 2797806073199567219281093908567346092300) * 10^40
        + 9317044300534680221482618259916829089928) * 10^40
        + 9292925173344299509311608228742172988564) * 10^40
        + 3152681640365150526406453832389472352052) * 10^40
        + 1250358366550255607887372045189782049555) * 10^40
        + 7563115754298305901173446643403362905177) * 10^40
        + 1071387165828310731838188417058784657347) : ℚ) /
        (((((((((((22842518 * 10^40
        + 8842464095519877786340690044442597988518) * 10^40
        + 4215949933311983795855577971524796877522) * 10^40
        + 14180606042338766245882337594744164505) * 10^40
        + 467734296160474013660789024866914779734) * 10^40
        + 5696411561561946561548139810525517808995) * 10^40
        + 1504026062060204809699732820547659706) * 10^40
        + 5000630210162567607619348884022128822898) * 10^40
        + 8406412809568277236932619660186572149057) * 10^40
        + 5957734635916403332077954446857770323536) * 10^40
        + 7524001102428163063393168316520621327040) * 10^40
        + 8347006479639290958048137883604062568448)),
    (((-((((((((4016187295090583 * 10^40
        + 7748280399853878898706991640684606250265) * 10^40
        + 9695243050519168730016924476005141277138) * 10^40
        + 360700143505131153485022863756097843390) * 10^40
        + 9889478430078505068388343675771291769949) * 10^40
        + 4554537523671897495847520359990572474228) * 10^40
        + 7941481762209185004829602018890452090521) * 10^40
        + 9183141130582792321218161007770879078157) * 10^40
        + 3233252679173033389045940321115794788567)) : ℚ) /
        ((((((((41 * 10^40
        + 6062899833883641850133321318635740042219) * 10^40
        + 6775455552379098610673847270297884081843) * 10^40
        + 4877323772813371803210477748767062325870) * 10^40
        + 9907042454417091655472747620987822763446) * 10^40
        + 1662124391468846301136557867318090541441) * 10^40
        + 3574725908791347942893919084763049640206) * 10^40
        + 6890819991285739763799902592259439561253) * 10^40
        + 1293388452013910771094445330521529516032)))

noncomputable def batchN02705MinusP010Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP010BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP010Center2654‖ ≤ batchN02705MinusP010Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP010Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP010Input2654]
  have hs : compactExp2547 batchN02705MinusP010Input2654 13 =
      (batchN02705MinusP010Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP010Input2654 13).2 : ℝ) =
      batchN02705MinusP010Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP010Error2654]
  have h := compactExp_error2547 batchN02705MinusP010Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP010Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP010Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP010DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP010Factor2654 * embedPair2542 batchN02705MinusP010Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP010Factor2654 : ℝ) * batchN02705MinusP010Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP010Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP010Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP010BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP010Factor2654)

def batchN02705MinusP011Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((123268206202301004985337883 : ℚ) /
        11805916207174113034240000000))

def batchN02705MinusP011Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP011Factor2654 : RatPair2542 := ((((((((((((((33317480374054209299446960 *
    10^40
        + 7097407021386180573811881353184355410663) * 10^40
        + 5812120126025752573125915844607090225801) * 10^40
        + 9195122375590835186482131950409452437593) * 10^40
        + 3682611507176234693179727353927638930906) * 10^40
        + 7612532400948089162452929549586913667865) * 10^40
        + 9006059864635879957243951626486388772249) * 10^40
        + 6619244726785686709141651702463226245237) * 10^40
        + 8152339578496269155477138850619849311807) * 10^40
        + 5730704752641017548593839244200232602530) * 10^40
        + 2793599781021576570297492345959591601750) * 10^40
        + 654809478690735729798414169732645262627) : ℚ) /
        (((((((((((22842518 * 10^40
        + 8842464095519877786340690044442597988518) * 10^40
        + 4215949933311983795855577971524796877522) * 10^40
        + 14180606042338766245882337594744164505) * 10^40
        + 467734296160474013660789024866914779734) * 10^40
        + 5696411561561946561548139810525517808995) * 10^40
        + 1504026062060204809699732820547659706) * 10^40
        + 5000630210162567607619348884022128822898) * 10^40
        + 8406412809568277236932619660186572149057) * 10^40
        + 5957734635916403332077954446857770323536) * 10^40
        + 7524001102428163063393168316520621327040) * 10^40
        + 8347006479639290958048137883604062568448)),
    (((-((((((((4443238102796986 * 10^40
        + 4082705840986762563427128272519751797504) * 10^40
        + 7335140982070341018687402104945321979742) * 10^40
        + 3534874869474142431238001939522405967201) * 10^40
        + 6116134783172145595582445613775801714498) * 10^40
        + 9367979607234200744832698090952815281223) * 10^40
        + 1187431591731329426904777984352745067816) * 10^40
        + 636623597955291895472492860769062091409) * 10^40
        + 8155849607477942837635499505100552374567)) : ℚ) /
        ((((((((41 * 10^40
        + 6062899833883641850133321318635740042219) * 10^40
        + 6775455552379098610673847270297884081843) * 10^40
        + 4877323772813371803210477748767062325870) * 10^40
        + 9907042454417091655472747620987822763446) * 10^40
        + 1662124391468846301136557867318090541441) * 10^40
        + 3574725908791347942893919084763049640206) * 10^40
        + 6890819991285739763799902592259439561253) * 10^40
        + 1293388452013910771094445330521529516032)))

noncomputable def batchN02705MinusP011Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP011BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP011Center2654‖ ≤ batchN02705MinusP011Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP011Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP011Input2654]
  have hs : compactExp2547 batchN02705MinusP011Input2654 13 =
      (batchN02705MinusP011Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP011Input2654 13).2 : ℝ) =
      batchN02705MinusP011Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP011Error2654]
  have h := compactExp_error2547 batchN02705MinusP011Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP011Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP011Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP011DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP011Factor2654 * embedPair2542 batchN02705MinusP011Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP011Factor2654 : ℝ) * batchN02705MinusP011Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP011Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP011Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP011BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP011Factor2654)

def batchN02705MinusP012Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((2710788774631016534924847 : ℚ) /
        236118324143482260684800000))

def batchN02705MinusP012Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP012Factor2654 : RatPair2542 := ((((((((((((((8329370090403560792966939 *
    10^40
        + 6425466074105509925436931091623940130150) * 10^40
        + 5484791463864086028390333782907471098367) * 10^40
        + 43586198867330583862608903605667549705) * 10^40
        + 7332607759134205368829052994078107792736) * 10^40
        + 619800987108924619739760709544436929726) * 10^40
        + 8957483082504128492565042747083883366167) * 10^40
        + 6670278525558688029257088350222572889109) * 10^40
        + 4661899429342461910896198754924630469265) * 10^40
        + 2538884715514618558679877360235460233205) * 10^40
        + 6395936461771309487760765759488320652713) * 10^40
        + 2850650520496831313391918253118672121611) : ℚ) /
        (((((((((((5710629 * 10^40
        + 7210616023879969446585172511110649497129) * 10^40
        + 6053987483327995948963894492881199219380) * 10^40
        + 5003545151510584691561470584398686041126) * 10^40
        + 2616933574040118503415197256216728694933) * 10^40
        + 6424102890390486640387034952631379452248) * 10^40
        + 7500376006515515051202424933205136914926) * 10^40
        + 6250157552540641901904837221005532205724) * 10^40
        + 7101603202392069309233154915046643037264) * 10^40
        + 3989433658979100833019488611714442580884) * 10^40
        + 1881000275607040765848292079130155331760) * 10^40
        + 2086751619909822739512034470901015642112)),
    (((-((((((((610694778009526 * 10^40
        + 841430041204964325752091652161248179001) * 10^40
        + 4813036252672628056014585554007829182343) * 10^40
        + 7372070142746339141916144730961959612391) * 10^40
        + 3910162368897913013873600473563891387560) * 10^40
        + 3275901503934637340273592260072255878772) * 10^40
        + 9096678901210194040844144195315154795297) * 10^40
        + 3246374761144720053669682977173535463886) * 10^40
        + 1165800480960383634301462826160453886075)) : ℚ) /
        ((((((((5 * 10^40
        + 2007862479235455231266665164829467505277) * 10^40
        + 4596931944047387326334230908787235510230) * 10^40
        + 4359665471601671475401309718595882790733) * 10^40
        + 8738380306802136456934093452623477845430) * 10^40
        + 7707765548933605787642069733414761317680) * 10^40
        + 1696840738598918492861739885595381205025) * 10^40
        + 8361352498910717470474987824032429945156) * 10^40
        + 6411673556501738846386805666315191189504)))

noncomputable def batchN02705MinusP012Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP012BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP012Center2654‖ ≤ batchN02705MinusP012Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP012Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP012Input2654]
  have hs : compactExp2547 batchN02705MinusP012Input2654 13 =
      (batchN02705MinusP012Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP012Input2654 13).2 : ℝ) =
      batchN02705MinusP012Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP012Error2654]
  have h := compactExp_error2547 batchN02705MinusP012Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP012Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP012Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP012DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP012Factor2654 * embedPair2542 batchN02705MinusP012Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP012Factor2654 : ℝ) * batchN02705MinusP012Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP012Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP012Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP012BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP012Factor2654)

def batchN02705MinusP013Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((29344407147130955527319553 : ℚ) /
        2361183241434822606848000000))

def batchN02705MinusP013Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP013Factor2654 : RatPair2542 := ((((((((((((((33317480349250550779053826 *
    10^40
        + 7612688632602459047385311658507590046680) * 10^40
        + 7220656506005886534794380226424025702975) * 10^40
        + 5434129036558655859598403576214075349791) * 10^40
        + 3207162918687224474145599536817355429269) * 10^40
        + 9159319180628077315971239337034628476053) * 10^40
        + 5234724379495534012734236096442435905676) * 10^40
        + 1146421784240571888100853426905253331066) * 10^40
        + 870675108368495376982044090528754105173) * 10^40
        + 8828981680018563417404390164320715831228) * 10^40
        + 2812806062291100290309167515758042756782) * 10^40
        + 4802601218217337598929541444611208162019) : ℚ) /
        (((((((((((22842518 * 10^40
        + 8842464095519877786340690044442597988518) * 10^40
        + 4215949933311983795855577971524796877522) * 10^40
        + 14180606042338766245882337594744164505) * 10^40
        + 467734296160474013660789024866914779734) * 10^40
        + 5696411561561946561548139810525517808995) * 10^40
        + 1504026062060204809699732820547659706) * 10^40
        + 5000630210162567607619348884022128822898) * 10^40
        + 8406412809568277236932619660186572149057) * 10^40
        + 5957734635916403332077954446857770323536) * 10^40
        + 7524001102428163063393168316520621327040) * 10^40
        + 8347006479639290958048137883604062568448)),
    (((-((((((((5288638163329882 * 10^40
        + 474798591603662220888988714471222603537) * 10^40
        + 2296214966870001881758044059206131374145) * 10^40
        + 3806205643091312181691914230353299464838) * 10^40
        + 5731078380435193623022230483408844337206) * 10^40
        + 3933901731580092716774382525599527628166) * 10^40
        + 8458097172176542476451826996684095718782) * 10^40
        + 2441117123414431551632088434445453606693) * 10^40
        + 2648876717317827323602634694411001774265)) : ℚ) /
        ((((((((41 * 10^40
        + 6062899833883641850133321318635740042219) * 10^40
        + 6775455552379098610673847270297884081843) * 10^40
        + 4877323772813371803210477748767062325870) * 10^40
        + 9907042454417091655472747620987822763446) * 10^40
        + 1662124391468846301136557867318090541441) * 10^40
        + 3574725908791347942893919084763049640206) * 10^40
        + 6890819991285739763799902592259439561253) * 10^40
        + 1293388452013910771094445330521529516032)))

noncomputable def batchN02705MinusP013Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP013BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP013Center2654‖ ≤ batchN02705MinusP013Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP013Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP013Input2654]
  have hs : compactExp2547 batchN02705MinusP013Input2654 13 =
      (batchN02705MinusP013Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP013Input2654 13).2 : ℝ) =
      batchN02705MinusP013Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP013Error2654]
  have h := compactExp_error2547 batchN02705MinusP013Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP013Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP013Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP013DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP013Factor2654 * embedPair2542 batchN02705MinusP013Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP013Factor2654 : ℝ) * batchN02705MinusP013Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP013Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP013Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP013BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP013Factor2654)

def batchN02705MinusP014Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((167442242677902990093140313 : ℚ) /
        11805916207174113034240000000))

def batchN02705MinusP014Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP014Factor2654 : RatPair2542 := ((((((((((((((33317480323752627936950591 *
    10^40
        + 7634597761479054238442847612287365327001) * 10^40
        + 2885181489470602252743450505939973743097) * 10^40
        + 5284338605031911618425989297395021803680) * 10^40
        + 2268772316295644945084584615762240903903) * 10^40
        + 4554930723110501766424014755892132227900) * 10^40
        + 8020875167443802314851642649743359521893) * 10^40
        + 1117340340030991547433756502646572438149) * 10^40
        + 7761606570519356479416564670473562435550) * 10^40
        + 3769238891181354336617710352512426439792) * 10^40
        + 5164967911304815142172668615417703909900) * 10^40
        + 1891105269509443570843906575947331663787) : ℚ) /
        (((((((((((22842518 * 10^40
        + 8842464095519877786340690044442597988518) * 10^40
        + 4215949933311983795855577971524796877522) * 10^40
        + 14180606042338766245882337594744164505) * 10^40
        + 467734296160474013660789024866914779734) * 10^40
        + 5696411561561946561548139810525517808995) * 10^40
        + 1504026062060204809699732820547659706) * 10^40
        + 5000630210162567607619348884022128822898) * 10^40
        + 8406412809568277236932619660186572149057) * 10^40
        + 5957734635916403332077954446857770323536) * 10^40
        + 7524001102428163063393168316520621327040) * 10^40
        + 8347006479639290958048137883604062568448)),
    (((-((((((((6035504007728591 * 10^40
        + 6144617872703913571992825302269739224710) * 10^40
        + 8611491491330440462830476594174734943096) * 10^40
        + 5816562036698271544012914491889613397601) * 10^40
        + 1103211065264933250727651204000419609250) * 10^40
        + 5172534413159160475109721016122397857797) * 10^40
        + 484663408755683929576189394314320656448) * 10^40
        + 7636185725043841096881746109209186462049) * 10^40
        + 6539825134915475931251294938574895204117)) : ℚ) /
        ((((((((41 * 10^40
        + 6062899833883641850133321318635740042219) * 10^40
        + 6775455552379098610673847270297884081843) * 10^40
        + 4877323772813371803210477748767062325870) * 10^40
        + 9907042454417091655472747620987822763446) * 10^40
        + 1662124391468846301136557867318090541441) * 10^40
        + 3574725908791347942893919084763049640206) * 10^40
        + 6890819991285739763799902592259439561253) * 10^40
        + 1293388452013910771094445330521529516032)))

noncomputable def batchN02705MinusP014Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP014BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP014Center2654‖ ≤ batchN02705MinusP014Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP014Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP014Input2654]
  have hs : compactExp2547 batchN02705MinusP014Input2654 13 =
      (batchN02705MinusP014Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP014Input2654 13).2 : ℝ) =
      batchN02705MinusP014Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP014Error2654]
  have h := compactExp_error2547 batchN02705MinusP014Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP014Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP014Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP014DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP014Factor2654 * embedPair2542 batchN02705MinusP014Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP014Factor2654 : ℝ) * batchN02705MinusP014Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP014Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP014Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP014BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP014Factor2654)

def batchN02705MinusP015Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((182288341473529359843979701 : ℚ) /
        11805916207174113034240000000))

def batchN02705MinusP015Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP015Factor2654 : RatPair2542 := ((((((((((((((33317480303415019998681728 *
    10^40
        + 5042891083971304131923279644564544399015) * 10^40
        + 1119138671023286069989569497747822851493) * 10^40
        + 6546569003332654325750063826178478865429) * 10^40
        + 8784491423638217934418055497910628875476) * 10^40
        + 2597452832992609191845325351453310189342) * 10^40
        + 2122372487493533248373394048095192455400) * 10^40
        + 9702937599823812839805604473766246281068) * 10^40
        + 7603075104617579888675137577380019875803) * 10^40
        + 9894126864284367332973896679718889101253) * 10^40
        + 9079443256581380114487429933471621043265) * 10^40
        + 7867944275311291101507879353926687919491) : ℚ) /
        (((((((((((22842518 * 10^40
        + 8842464095519877786340690044442597988518) * 10^40
        + 4215949933311983795855577971524796877522) * 10^40
        + 14180606042338766245882337594744164505) * 10^40
        + 467734296160474013660789024866914779734) * 10^40
        + 5696411561561946561548139810525517808995) * 10^40
        + 1504026062060204809699732820547659706) * 10^40
        + 5000630210162567607619348884022128822898) * 10^40
        + 8406412809568277236932619660186572149057) * 10^40
        + 5957734635916403332077954446857770323536) * 10^40
        + 7524001102428163063393168316520621327040) * 10^40
        + 8347006479639290958048137883604062568448)),
    (((-((((((((6570635927084943 * 10^40
        + 4406918130608690456231975906897096003623) * 10^40
        + 2175163499250220028282490089714280497155) * 10^40
        + 3636267193792802473091117722632406483965) * 10^40
        + 7893425426191648933279574059713086135503) * 10^40
        + 6027600208091736645668664082038893991751) * 10^40
        + 2923073540202602817573875604991566099149) * 10^40
        + 1795069117550696165821918199185546421286) * 10^40
        + 3660248691391142200695780851561972602633)) : ℚ) /
        ((((((((41 * 10^40
        + 6062899833883641850133321318635740042219) * 10^40
        + 6775455552379098610673847270297884081843) * 10^40
        + 4877323772813371803210477748767062325870) * 10^40
        + 9907042454417091655472747620987822763446) * 10^40
        + 1662124391468846301136557867318090541441) * 10^40
        + 3574725908791347942893919084763049640206) * 10^40
        + 6890819991285739763799902592259439561253) * 10^40
        + 1293388452013910771094445330521529516032)))

noncomputable def batchN02705MinusP015Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP015BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP015Center2654‖ ≤ batchN02705MinusP015Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP015Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP015Input2654]
  have hs : compactExp2547 batchN02705MinusP015Input2654 13 =
      (batchN02705MinusP015Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP015Input2654 13).2 : ℝ) =
      batchN02705MinusP015Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP015Error2654]
  have h := compactExp_error2547 batchN02705MinusP015Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP015Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP015Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP015DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP015Factor2654 * embedPair2542 batchN02705MinusP015Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP015Factor2654 : ℝ) * batchN02705MinusP015Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP015Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP015Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP015BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP015Factor2654)

def batchN02705MinusP016Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((96508645919919764395179147 : ℚ) /
        5902958103587056517120000000))

def batchN02705MinusP016Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP016Factor2654 : RatPair2542 := ((((((((((((((8329370071910669089805089 *
    10^40
        + 130884994482913374134627451295383720297) * 10^40
        + 6536175672322122541682129034260693782481) * 10^40
        + 2784679083929440332249126964977962411690) * 10^40
        + 926145412282272431787036836468306211496) * 10^40
        + 8274123920463531734294718300566355091307) * 10^40
        + 7645188477198765803761369487881223963794) * 10^40
        + 682674943480900378173461501142970620114) * 10^40
        + 113952277580799205595526245770612501406) * 10^40
        + 6248125983110323047400064661900352441168) * 10^40
        + 6124540118829327679911957430379291272591) * 10^40
        + 1949127975011655584340241871878281350659) : ℚ) /
        (((((((((((5710629 * 10^40
        + 7210616023879969446585172511110649497129) * 10^40
        + 6053987483327995948963894492881199219380) * 10^40
        + 5003545151510584691561470584398686041126) * 10^40
        + 2616933574040118503415197256216728694933) * 10^40
        + 6424102890390486640387034952631379452248) * 10^40
        + 7500376006515515051202424933205136914926) * 10^40
        + 6250157552540641901904837221005532205724) * 10^40
        + 7101603202392069309233154915046643037264) * 10^40
        + 3989433658979100833019488611714442580884) * 10^40
        + 1881000275607040765848292079130155331760) * 10^40
        + 2086751619909822739512034470901015642112)),
    (((-((((((((869670505250731 * 10^40
        + 1681159754811329462143020197362438351032) * 10^40
        + 865756123954373138825281218116691022965) * 10^40
        + 6918556587595623468289858967728939323068) * 10^40
        + 6549210735229971713434519746726209640601) * 10^40
        + 5734138111359779441497965963791930644098) * 10^40
        + 9433083484918721764986523504228395890896) * 10^40
        + 6058279348591145077964576403782867031660) * 10^40
        + 7723363640231313956120666513428628164279)) : ℚ) /
        ((((((((5 * 10^40
        + 2007862479235455231266665164829467505277) * 10^40
        + 4596931944047387326334230908787235510230) * 10^40
        + 4359665471601671475401309718595882790733) * 10^40
        + 8738380306802136456934093452623477845430) * 10^40
        + 7707765548933605787642069733414761317680) * 10^40
        + 1696840738598918492861739885595381205025) * 10^40
        + 8361352498910717470474987824032429945156) * 10^40
        + 6411673556501738846386805666315191189504)))

noncomputable def batchN02705MinusP016Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP016BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP016Center2654‖ ≤ batchN02705MinusP016Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP016Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP016Input2654]
  have hs : compactExp2547 batchN02705MinusP016Input2654 13 =
      (batchN02705MinusP016Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP016Input2654 13).2 : ℝ) =
      batchN02705MinusP016Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP016Error2654]
  have h := compactExp_error2547 batchN02705MinusP016Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP016Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP016Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP016DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP016Factor2654 * embedPair2542 batchN02705MinusP016Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP016Factor2654 : ℝ) * batchN02705MinusP016Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP016Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP016Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP016BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP016Factor2654)

def batchN02705MinusP017Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((213857607167923887040711041 : ℚ) /
        11805916207174113034240000000))

def batchN02705MinusP017Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP017Factor2654 : RatPair2542 := ((((((((((((((33317480254428835897148617 *
    10^40
        + 3219418366529747047793146584447566845861) * 10^40
        + 8253637043207189687654249082860767779852) * 10^40
        + 8110534441702306172597921613682592984274) * 10^40
        + 4356965516608346026879031689757468479845) * 10^40
        + 1727189857573849723450634055231735956562) * 10^40
        + 8209214539808405606172050109114331777836) * 10^40
        + 3137690146493176589453131834370225163114) * 10^40
        + 7644352299228037729457368353163356787375) * 10^40
        + 2839068815086653000813444882172204830471) * 10^40
        + 991679679596921641811440429421091557372) * 10^40
        + 2536812353518069937120409941982361506651) : ℚ) /
        (((((((((((22842518 * 10^40
        + 8842464095519877786340690044442597988518) * 10^40
        + 4215949933311983795855577971524796877522) * 10^40
        + 14180606042338766245882337594744164505) * 10^40
        + 467734296160474013660789024866914779734) * 10^40
        + 5696411561561946561548139810525517808995) * 10^40
        + 1504026062060204809699732820547659706) * 10^40
        + 5000630210162567607619348884022128822898) * 10^40
        + 8406412809568277236932619660186572149057) * 10^40
        + 5957734635916403332077954446857770323536) * 10^40
        + 7524001102428163063393168316520621327040) * 10^40
        + 8347006479639290958048137883604062568448)),
    (((-((((((((7708559227374389 * 10^40
        + 8513340059527313948883712267680045585371) * 10^40
        + 2819793789480753069423489916993907612744) * 10^40
        + 5714394433205494684434594510028999343057) * 10^40
        + 2899779825288809847438795632606489585109) * 10^40
        + 5123529200993618213013732290738390754125) * 10^40
        + 651002270012519931078347464615494680533) * 10^40
        + 1028051339644808526487726935127081871800) * 10^40
        + 242009010960323275796774695934395311213)) : ℚ) /
        ((((((((41 * 10^40
        + 6062899833883641850133321318635740042219) * 10^40
        + 6775455552379098610673847270297884081843) * 10^40
        + 4877323772813371803210477748767062325870) * 10^40
        + 9907042454417091655472747620987822763446) * 10^40
        + 1662124391468846301136557867318090541441) * 10^40
        + 3574725908791347942893919084763049640206) * 10^40
        + 6890819991285739763799902592259439561253) * 10^40
        + 1293388452013910771094445330521529516032)))

noncomputable def batchN02705MinusP017Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP017BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP017Center2654‖ ≤ batchN02705MinusP017Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP017Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP017Input2654]
  have hs : compactExp2547 batchN02705MinusP017Input2654 13 =
      (batchN02705MinusP017Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP017Input2654 13).2 : ℝ) =
      batchN02705MinusP017Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP017Error2654]
  have h := compactExp_error2547 batchN02705MinusP017Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP017Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP017Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP017DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP017Factor2654 * embedPair2542 batchN02705MinusP017Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP017Factor2654 : ℝ) * batchN02705MinusP017Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP017Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP017Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP017BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP017Factor2654)

def batchN02705MinusP018Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((55434221733839136935063079 : ℚ) /
        2951479051793528258560000000))

def batchN02705MinusP018Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP018Factor2654 : RatPair2542 := ((((((((((((((2082342515061563251656125 *
    10^40
        + 1225452083125266637710052833618508847810) * 10^40
        + 6552394215950432891150432231551018840449) * 10^40
        + 582523181210709562362891370341458856104) * 10^40
        + 1023122760152500216072402039135289355496) * 10^40
        + 2223912457848146876415058356049020718047) * 10^40
        + 7778980639622725891237411242161925419654) * 10^40
        + 9381501624581543286533486238796123836327) * 10^40
        + 8217459956176592258647555058909519685828) * 10^40
        + 2813940488272086867413083356044181153910) * 10^40
        + 8425149682495573725856723378947736084306) * 10^40
        + 7893538395981544221205247523501751319211) : ℚ) /
        (((((((((((1427657 * 10^40
        + 4302654005969992361646293127777662374282) * 10^40
        + 4013496870831998987240973623220299804845) * 10^40
        + 1250886287877646172890367646099671510281) * 10^40
        + 5654233393510029625853799314054182173733) * 10^40
        + 4106025722597621660096758738157844863062) * 10^40
        + 1875094001628878762800606233301284228731) * 10^40
        + 6562539388135160475476209305251383051431) * 10^40
        + 1775400800598017327308288728761660759316) * 10^40
        + 997358414744775208254872152928610645221) * 10^40
        + 470250068901760191462073019782538832940) * 10^40
        + 521687904977455684878008617725253910528)),
    (((-((((((((124883908473740 * 10^40
        + 8704451287733896061157100699354604143982) * 10^40
        + 5213357729040792050010082322620082174406) * 10^40
        + 1626484867470242173513560151151634567639) * 10^40
        + 6131083201026313432923366129231941408462) * 10^40
        + 449478183100436677393595140803908624348) * 10^40
        + 978259813402632600530564020576873756679) * 10^40
        + 8689090775987702339599840629644711271869) * 10^40
        + 9023287266880986855317404743540367023467)) : ℚ) /
        (((((((6500982809904431903908333145603683438159 * 10^40
        + 6824616493005923415791778863598404438778) * 10^40
        + 8044958183950208934425163714824485348841) * 10^40
        + 7342297538350267057116761681577934730678) * 10^40
        + 8463470693616700723455258716676845164710) * 10^40
        + 212105092324864811607717485699422650628) * 10^40
        + 2295169062363839683809373478004053743144) * 10^40
        + 5801459194562717355798350708289398898688)))

noncomputable def batchN02705MinusP018Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP018BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP018Center2654‖ ≤ batchN02705MinusP018Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP018Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP018Input2654]
  have hs : compactExp2547 batchN02705MinusP018Input2654 13 =
      (batchN02705MinusP018Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP018Input2654 13).2 : ℝ) =
      batchN02705MinusP018Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP018Error2654]
  have h := compactExp_error2547 batchN02705MinusP018Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP018Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP018Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP018DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP018Factor2654 * embedPair2542 batchN02705MinusP018Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP018Factor2654 : ℝ) * batchN02705MinusP018Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP018Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP018Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP018BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP018Factor2654)

def batchN02705MinusP019Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((11798844492939419238077853 : ℚ) /
        590295810358705651712000000))

def batchN02705MinusP019Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP019Factor2654 : RatPair2542 := ((((((((((((((2082342513465911947080995 *
    10^40
        + 5040390488942602410106491541149424954400) * 10^40
        + 6305028896667398026627584420103473082775) * 10^40
        + 9610848919753157013803622536668531246164) * 10^40
        + 357822759482270563409201710449475031751) * 10^40
        + 533617991341372291413291369158021479268) * 10^40
        + 900528760249354685955256732251281763783) * 10^40
        + 7606270515600147632787549139443434464668) * 10^40
        + 7617553254125888184379955057859970559051) * 10^40
        + 5074386967137310929475532720031488383832) * 10^40
        + 7156888188156940181722710067889500822697) * 10^40
        + 1426595700611903591932991482844080259259) : ℚ) /
        (((((((((((1427657 * 10^40
        + 4302654005969992361646293127777662374282) * 10^40
        + 4013496870831998987240973623220299804845) * 10^40
        + 1250886287877646172890367646099671510281) * 10^40
        + 5654233393510029625853799314054182173733) * 10^40
        + 4106025722597621660096758738157844863062) * 10^40
        + 1875094001628878762800606233301284228731) * 10^40
        + 6562539388135160475476209305251383051431) * 10^40
        + 1775400800598017327308288728761660759316) * 10^40
        + 997358414744775208254872152928610645221) * 10^40
        + 470250068901760191462073019782538832940) * 10^40
        + 521687904977455684878008617725253910528)),
    (((-((((((((132903986882104 * 10^40
        + 1326656603309444716169587614252796368867) * 10^40
        + 8702739971541087449828290184301764684421) * 10^40
        + 1673804500895594188582010609213985412837) * 10^40
        + 1823001446947688912891098235972754432126) * 10^40
        + 1242518255559513650260117264741128304352) * 10^40
        + 9566727342025478236444943379287570507968) * 10^40
        + 8013787108006730626501175399521446946845) * 10^40
        + 4341776218458983080042307006153477155165)) : ℚ) /
        (((((((6500982809904431903908333145603683438159 * 10^40
        + 6824616493005923415791778863598404438778) * 10^40
        + 8044958183950208934425163714824485348841) * 10^40
        + 7342297538350267057116761681577934730678) * 10^40
        + 8463470693616700723455258716676845164710) * 10^40
        + 212105092324864811607717485699422650628) * 10^40
        + 2295169062363839683809373478004053743144) * 10^40
        + 5801459194562717355798350708289398898688)))

noncomputable def batchN02705MinusP019Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP019BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP019Center2654‖ ≤ batchN02705MinusP019Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP019Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP019Input2654]
  have hs : compactExp2547 batchN02705MinusP019Input2654 13 =
      (batchN02705MinusP019Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP019Input2654 13).2 : ℝ) =
      batchN02705MinusP019Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP019Error2654]
  have h := compactExp_error2547 batchN02705MinusP019Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP019Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP019Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP019DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP019Factor2654 * embedPair2542 batchN02705MinusP019Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP019Factor2654 : ℝ) * batchN02705MinusP019Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP019Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP019Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP019BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP019Factor2654)

def batchN02705MinusP020Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((251461754510132159483335377 : ℚ) /
        11805916207174113034240000000))

def batchN02705MinusP020Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP020Factor2654 : RatPair2542 := ((((((((((((((33317480185889359767520567 *
    10^40
        + 7346083212309615412947870671076007200671) * 10^40
        + 1256223773510910081439990881792994992379) * 10^40
        + 3911681297929636078368755325301598254173) * 10^40
        + 5039671116570060528338991401686304395055) * 10^40
        + 2232022444016769682229956577668379949554) * 10^40
        + 6568264281650115377414452639354666429762) * 10^40
        + 8448538868911506647045926623746249667020) * 10^40
        + 5130002835010811781517209371494477234160) * 10^40
        + 6171252628472995362610322164255368171527) * 10^40
        + 4614330092392548077871253992383985496392) * 10^40
        + 1121487463831149777556791080485399381307) : ℚ) /
        (((((((((((22842518 * 10^40
        + 8842464095519877786340690044442597988518) * 10^40
        + 4215949933311983795855577971524796877522) * 10^40
        + 14180606042338766245882337594744164505) * 10^40
        + 467734296160474013660789024866914779734) * 10^40
        + 5696411561561946561548139810525517808995) * 10^40
        + 1504026062060204809699732820547659706) * 10^40
        + 5000630210162567607619348884022128822898) * 10^40
        + 8406412809568277236932619660186572149057) * 10^40
        + 5957734635916403332077954446857770323536) * 10^40
        + 7524001102428163063393168316520621327040) * 10^40
        + 8347006479639290958048137883604062568448)),
    (((-((((((((9064011578956571 * 10^40
        + 8741109473056864631670704776593631113436) * 10^40
        + 2654650199321785008285921112655817041456) * 10^40
        + 1801487874797902405701613216340936477474) * 10^40
        + 332904088592422777437477735874443300821) * 10^40
        + 9133339955279034385692928333596350247417) * 10^40
        + 4043963304640478686461925430574152067493) * 10^40
        + 2413075923419019483619669956519111638055) * 10^40
        + 2231362045231908164453341581140046258333)) : ℚ) /
        ((((((((41 * 10^40
        + 6062899833883641850133321318635740042219) * 10^40
        + 6775455552379098610673847270297884081843) * 10^40
        + 4877323772813371803210477748767062325870) * 10^40
        + 9907042454417091655472747620987822763446) * 10^40
        + 1662124391468846301136557867318090541441) * 10^40
        + 3574725908791347942893919084763049640206) * 10^40
        + 6890819991285739763799902592259439561253) * 10^40
        + 1293388452013910771094445330521529516032)))

noncomputable def batchN02705MinusP020Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP020BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP020Center2654‖ ≤ batchN02705MinusP020Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP020Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP020Input2654]
  have hs : compactExp2547 batchN02705MinusP020Input2654 13 =
      (batchN02705MinusP020Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP020Input2654 13).2 : ℝ) =
      batchN02705MinusP020Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP020Error2654]
  have h := compactExp_error2547 batchN02705MinusP020Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP020Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP020Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP020DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP020Factor2654 * embedPair2542 batchN02705MinusP020Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP020Factor2654 : ℝ) * batchN02705MinusP020Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP020Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP020Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP020BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP020Factor2654)

def batchN02705MinusP021Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((264384479371882101864279921 : ℚ) /
        11805916207174113034240000000))

def batchN02705MinusP021Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP021Factor2654 : RatPair2542 := ((((((((((((((33317480159778073067604025 *
    10^40
        + 5116978848234071165549761284326124073878) * 10^40
        + 7251330761041861837891235795163206920673) * 10^40
        + 2272581141871732439219253698524895281150) * 10^40
        + 2478070929537889530997260255100812994481) * 10^40
        + 2266045343375532082494625120392151641629) * 10^40
        + 98502080779136533981398186146627530589) * 10^40
        + 5393923306173893050905779533896237665640) * 10^40
        + 4165216417028876557431278211013999056129) * 10^40
        + 2105546658434504008693081437543570710562) * 10^40
        + 7159479607717162673954448229805036966999) * 10^40
        + 3914977825442440153890185862597828318971) : ℚ) /
        (((((((((((22842518 * 10^40
        + 8842464095519877786340690044442597988518) * 10^40
        + 4215949933311983795855577971524796877522) * 10^40
        + 14180606042338766245882337594744164505) * 10^40
        + 467734296160474013660789024866914779734) * 10^40
        + 5696411561561946561548139810525517808995) * 10^40
        + 1504026062060204809699732820547659706) * 10^40
        + 5000630210162567607619348884022128822898) * 10^40
        + 8406412809568277236932619660186572149057) * 10^40
        + 5957734635916403332077954446857770323536) * 10^40
        + 7524001102428163063393168316520621327040) * 10^40
        + 8347006479639290958048137883604062568448)),
    (((-((((((((733062686819048 * 10^40
        + 9239572030144545982991954756661247546736) * 10^40
        + 6617058734244367443551850566267110404595) * 10^40
        + 7727772499639970800899713658802048574232) * 10^40
        + 3732312581409580005886898129829418859956) * 10^40
        + 6586530299800137560742099823815323643788) * 10^40
        + 9023345992003622912740850668081278788756) * 10^40
        + 4440989503739902316207106312494887109364) * 10^40
        + 3415033059824453215762331747441323372721)) : ℚ) /
        ((((((((3 * 10^40
        + 2004838448760280142317947793741210772478) * 10^40
        + 4367342734798392200821065174638298775526) * 10^40
        + 4221332597908720907939267519135927871220) * 10^40
        + 8454387881109007050420980586229832520265) * 10^40
        + 897086491651449715472042912870622349341) * 10^40
        + 6428825069907026764837993775751003818477) * 10^40
        + 4376216922406595366446146353250726120096) * 10^40
        + 3945645265539531597776495794655502270464)))

noncomputable def batchN02705MinusP021Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP021BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP021Center2654‖ ≤ batchN02705MinusP021Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP021Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP021Input2654]
  have hs : compactExp2547 batchN02705MinusP021Input2654 13 =
      (batchN02705MinusP021Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP021Input2654 13).2 : ℝ) =
      batchN02705MinusP021Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP021Error2654]
  have h := compactExp_error2547 batchN02705MinusP021Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP021Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP021Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP021DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP021Factor2654 * embedPair2542 batchN02705MinusP021Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP021Factor2654 : ℝ) * batchN02705MinusP021Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP021Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP021Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP021BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP021Factor2654)

def batchN02705MinusP022Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((54199761301639112700100539 : ℚ) /
        2361183241434822606848000000))

def batchN02705MinusP022Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP022Factor2654 : RatPair2542 := ((((((((((((((33317480145907181048014302 *
    10^40
        + 178038008316979748768570001796206465666) * 10^40
        + 8870964084017180947694585080204520889686) * 10^40
        + 6602016720567652825510338111135610649482) * 10^40
        + 7414140017449824801695230273364165508625) * 10^40
        + 4052827509434411462900222774583852294245) * 10^40
        + 8822488369228999826196271955451761067301) * 10^40
        + 3660674721949513334017077452699891850310) * 10^40
        + 6955336808021045286238150558038060122772) * 10^40
        + 3880208607738205084444767459268053057232) * 10^40
        + 289584127282495887179475516447970353115) * 10^40
        + 6898715655245105947500003633658417608619) : ℚ) /
        (((((((((((22842518 * 10^40
        + 8842464095519877786340690044442597988518) * 10^40
        + 4215949933311983795855577971524796877522) * 10^40
        + 14180606042338766245882337594744164505) * 10^40
        + 467734296160474013660789024866914779734) * 10^40
        + 5696411561561946561548139810525517808995) * 10^40
        + 1504026062060204809699732820547659706) * 10^40
        + 5000630210162567607619348884022128822898) * 10^40
        + 8406412809568277236932619660186572149057) * 10^40
        + 5957734635916403332077954446857770323536) * 10^40
        + 7524001102428163063393168316520621327040) * 10^40
        + 8347006479639290958048137883604062568448)),
    (((-((((((((9768230260428657 * 10^40
        + 161013328748374221657542310310492762909) * 10^40
        + 8042918847652277261449691826875761792388) * 10^40
        + 6686289395251733428657144069111269232495) * 10^40
        + 9446556167616550581045672881269446408547) * 10^40
        + 3630668665647726672172424254765832132781) * 10^40
        + 6621554485627243729412620591098877435790) * 10^40
        + 9608271777993934417423982995312163455189) * 10^40
        + 5329306821157466072289177892473308969195)) : ℚ) /
        ((((((((41 * 10^40
        + 6062899833883641850133321318635740042219) * 10^40
        + 6775455552379098610673847270297884081843) * 10^40
        + 4877323772813371803210477748767062325870) * 10^40
        + 9907042454417091655472747620987822763446) * 10^40
        + 1662124391468846301136557867318090541441) * 10^40
        + 3574725908791347942893919084763049640206) * 10^40
        + 6890819991285739763799902592259439561253) * 10^40
        + 1293388452013910771094445330521529516032)))

noncomputable def batchN02705MinusP022Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP022BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP022Center2654‖ ≤ batchN02705MinusP022Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP022Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP022Input2654]
  have hs : compactExp2547 batchN02705MinusP022Input2654 13 =
      (batchN02705MinusP022Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP022Input2654 13).2 : ℝ) =
      batchN02705MinusP022Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP022Error2654]
  have h := compactExp_error2547 batchN02705MinusP022Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP022Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP022Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP022DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP022Factor2654 * embedPair2542 batchN02705MinusP022Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP022Factor2654 : ℝ) * batchN02705MinusP022Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP022Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP022Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP022BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP022Factor2654)

def batchN02705MinusP023Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((145034570365256380837972839 : ℚ) /
        5902958103587056517120000000))

def batchN02705MinusP023Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP023Factor2654 : RatPair2542 := ((((((((((((((8329370025999053670329536 *
    10^40
        + 2676213098512554006315014815882349404210) * 10^40
        + 7215762282643118393902597125619091218232) * 10^40
        + 490036882378842744839550397304738761029) * 10^40
        + 8273141101393143914545468547013882514848) * 10^40
        + 32189975573223889796167232529699105584) * 10^40
        + 6852785055215411911780979465385368266816) * 10^40
        + 2768632331942183222238161159878862482630) * 10^40
        + 9428145348767946291726434836618784548495) * 10^40
        + 1189108214756180824815502628050189532847) * 10^40
        + 4133341461391412560824170293947777792085) * 10^40
        + 1618211367165565957176029711253328423723) : ℚ) /
        (((((((((((5710629 * 10^40
        + 7210616023879969446585172511110649497129) * 10^40
        + 6053987483327995948963894492881199219380) * 10^40
        + 5003545151510584691561470584398686041126) * 10^40
        + 2616933574040118503415197256216728694933) * 10^40
        + 6424102890390486640387034952631379452248) * 10^40
        + 7500376006515515051202424933205136914926) * 10^40
        + 6250157552540641901904837221005532205724) * 10^40
        + 7101603202392069309233154915046643037264) * 10^40
        + 3989433658979100833019488611714442580884) * 10^40
        + 1881000275607040765848292079130155331760) * 10^40
        + 2086751619909822739512034470901015642112)),
    (((-((((((((1306953245575838 * 10^40
        + 8019477858888447434526241953206612578570) * 10^40
        + 2739171158651842780154108169110580540648) * 10^40
        + 4536717419990483693148888566216876409005) * 10^40
        + 3712991716987869811646246861708921786755) * 10^40
        + 7197506404903075791188495997482285504718) * 10^40
        + 7784183579670333332784761787269680122751) * 10^40
        + 6157966204832143132109275316547199434974) * 10^40
        + 8948773461519632902356793956382867693099)) : ℚ) /
        ((((((((5 * 10^40
        + 2007862479235455231266665164829467505277) * 10^40
        + 4596931944047387326334230908787235510230) * 10^40
        + 4359665471601671475401309718595882790733) * 10^40
        + 8738380306802136456934093452623477845430) * 10^40
        + 7707765548933605787642069733414761317680) * 10^40
        + 1696840738598918492861739885595381205025) * 10^40
        + 8361352498910717470474987824032429945156) * 10^40
        + 6411673556501738846386805666315191189504)))

noncomputable def batchN02705MinusP023Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP023BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP023Center2654‖ ≤ batchN02705MinusP023Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP023Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP023Input2654]
  have hs : compactExp2547 batchN02705MinusP023Input2654 13 =
      (batchN02705MinusP023Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP023Input2654 13).2 : ℝ) =
      batchN02705MinusP023Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP023Error2654]
  have h := compactExp_error2547 batchN02705MinusP023Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP023Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP023Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP023DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP023Factor2654 * embedPair2542 batchN02705MinusP023Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP023Factor2654 : ℝ) * batchN02705MinusP023Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP023Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP023Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP023BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP023Factor2654)

def batchN02705MinusP024Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((149416547034989152754795001 : ℚ) /
        5902958103587056517120000000))

def batchN02705MinusP024Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP024Factor2654 : RatPair2542 := ((((((((((((((8329370020945031077134322 *
    10^40
        + 4799243640681809346200945910909234964258) * 10^40
        + 1030189780263586491836045314334614481585) * 10^40
        + 742186449892557038191492926692086439283) * 10^40
        + 8756533166240927927669174366792749654705) * 10^40
        + 8901396337336185502497783851520756370800) * 10^40
        + 7808398685333066926989833337674881738812) * 10^40
        + 113982592554132385111010684619165896257) * 10^40
        + 37474772457658903898674752486684635210) * 10^40
        + 6127415407421923362975895932878631516196) * 10^40
        + 9490901501316708368661412736656234600872) * 10^40
        + 8806617338220686649947483488540473413483) : ℚ) /
        (((((((((((5710629 * 10^40
        + 7210616023879969446585172511110649497129) * 10^40
        + 6053987483327995948963894492881199219380) * 10^40
        + 5003545151510584691561470584398686041126) * 10^40
        + 2616933574040118503415197256216728694933) * 10^40
        + 6424102890390486640387034952631379452248) * 10^40
        + 7500376006515515051202424933205136914926) * 10^40
        + 6250157552540641901904837221005532205724) * 10^40
        + 7101603202392069309233154915046643037264) * 10^40
        + 3989433658979100833019488611714442580884) * 10^40
        + 1881000275607040765848292079130155331760) * 10^40
        + 2086751619909822739512034470901015642112)),
    (((-((((((((1346440649185636 * 10^40
        + 5324338459473961900971680028073562532720) * 10^40
        + 5371648666446211278812344470475114798145) * 10^40
        + 9372939351037801390667381768137130354765) * 10^40
        + 901407331086278094218994339490960942958) * 10^40
        + 2768312634495206840250925047331991337968) * 10^40
        + 5937156864203099597085485015759976319922) * 10^40
        + 4207707848404216780219817297036076200969) * 10^40
        + 6683024372739988556323851775305304086901)) : ℚ) /
        ((((((((5 * 10^40
        + 2007862479235455231266665164829467505277) * 10^40
        + 4596931944047387326334230908787235510230) * 10^40
        + 4359665471601671475401309718595882790733) * 10^40
        + 8738380306802136456934093452623477845430) * 10^40
        + 7707765548933605787642069733414761317680) * 10^40
        + 1696840738598918492861739885595381205025) * 10^40
        + 8361352498910717470474987824032429945156) * 10^40
        + 6411673556501738846386805666315191189504)))

noncomputable def batchN02705MinusP024Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP024BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP024Center2654‖ ≤ batchN02705MinusP024Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP024Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP024Input2654]
  have hs : compactExp2547 batchN02705MinusP024Input2654 13 =
      (batchN02705MinusP024Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP024Input2654 13).2 : ℝ) =
      batchN02705MinusP024Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP024Error2654]
  have h := compactExp_error2547 batchN02705MinusP024Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP024Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP024Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP024DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP024Factor2654 * embedPair2542 batchN02705MinusP024Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP024Factor2654 : ℝ) * batchN02705MinusP024Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP024Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP024Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP024BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP024Factor2654)

def batchN02705MinusP025Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((4840960678205345786172339 : ℚ) /
        184467440737095516160000000))

def batchN02705MinusP025Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP025Factor2654 : RatPair2542 := ((((((((((((((8134150404683272709984 * 10^40
        + 2899183839272264291530130857891792770275) * 10^40
        + 9451704287763102940364679695778042069602) * 10^40
        + 8163080834415025367982566445147860111978) * 10^40
        + 6168804562417657317439859709058248569326) * 10^40
        + 6703992604433309633793266391419803705916) * 10^40
        + 1926038438661538050055928283432817418719) * 10^40
        + 9052930524723689830680821307804356055376) * 10^40
        + 1804278159927957082996336741006523795415) * 10^40
        + 7019817347781475312703499130408806697019) * 10^40
        + 118756141727983961694319000333265765403) * 10^40
        + 3887685713996083686861123686861736936851) : ℚ) /
        (((((((((((5576 * 10^40
        + 7868369742210820282662680832530381493649) * 10^40
        + 5406302722151687496043910053215704296112) * 10^40
        + 6762698774562022055362852998617576841837) * 10^40
        + 373649349193398553225991403570524149116) * 10^40
        + 1461351662978896959609752963820929081496) * 10^40
        + 3366699585943862807667189868098833141518) * 10^40
        + 4830322419484902970607328942598638215044) * 10^40
        + 6530372659377336005184798002846725237341) * 10^40
        + 785145931307596778157245594347377385332) * 10^40
        + 8947149414331647500747898722733525542316) * 10^40
        + 1720787843378818186269054721162989273088)),
    (((-((((((((42601031723 * 10^40
        + 3451972864265043594924545704104070551723) * 10^40
        + 2257283444942186481631688144478210547847) * 10^40
        + 9586844117986781774761898747007141346045) * 10^40
        + 4131085960485553859312861625528131313482) * 10^40
        + 4534417892076599931451920808959197916401) * 10^40
        + 2689606783282081030264180024521309073949) * 10^40
        + 2842405219027531553243813621276550492204) * 10^40
        + 1282466781306478216024263564822344441167)) : ℚ) /
        (((((((1587154006324324195290120396875899276 * 10^40
        + 8944537259885987774271433539761620704208) * 10^40
        + 6862315663619128468978131143485064571618) * 10^40
        + 3695640209359948795668241396894916487971) * 10^40
        + 3571402214524808764825062319022626182901) * 10^40
        + 5405325220969805875198146415401782085608) * 10^40
        + 635325969009366171797805022821778333433) * 10^40
        + 3849072621873672538416942956715890966528)))

noncomputable def batchN02705MinusP025Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP025BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP025Center2654‖ ≤ batchN02705MinusP025Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP025Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP025Input2654]
  have hs : compactExp2547 batchN02705MinusP025Input2654 13 =
      (batchN02705MinusP025Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP025Input2654 13).2 : ℝ) =
      batchN02705MinusP025Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP025Error2654]
  have h := compactExp_error2547 batchN02705MinusP025Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP025Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP025Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP025DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP025Factor2654 * embedPair2542 batchN02705MinusP025Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP025Factor2654 : ℝ) * batchN02705MinusP025Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP025Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP025Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP025BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP025Factor2654)

def batchN02705MinusP026Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((10032849088039534343392071 : ℚ) /
        368934881474191032320000000))

def batchN02705MinusP026Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP026Factor2654 : RatPair2542 := ((((((((((((((32536601591633463105699 * 10^40
        + 9316481097396727729598597390168896943346) * 10^40
        + 2692645141984008582259428227402721185625) * 10^40
        + 2598371423118182208346647603472702598377) * 10^40
        + 7318933766306976716234606072146870687656) * 10^40
        + 9874987941600660376751249633061799475752) * 10^40
        + 8107864101500200140252872396221416195579) * 10^40
        + 3997809383692314873533934441050954700524) * 10^40
        + 3103162732531295984510080848653891415322) * 10^40
        + 1170469820707851377502512100968452689745) * 10^40
        + 7853838730934384065079786162706723013373) * 10^40
        + 358347757708975616138427730956309295083) : ℚ) /
        (((((((((((22307 * 10^40
        + 1473478968843281130650723330121525974598) * 10^40
        + 1625210888606749984175640212862817184450) * 10^40
        + 7050795098248088221451411994470307367348) * 10^40
        + 1494597396773594212903965614282096596464) * 10^40
        + 5845406651915587838439011855283716325985) * 10^40
        + 3466798343775451230668759472395332566073) * 10^40
        + 9321289677939611882429315770394552860178) * 10^40
        + 6121490637509344020739192011386900949364) * 10^40
        + 3140583725230387112628982377389509541331) * 10^40
        + 5788597657326590002991594890934102169264) * 10^40
        + 6883151373515272745076218884651957092352)),
    (((-((((((((353161077436 * 10^40
        + 4109856116123585023428387608680046361963) * 10^40
        + 6295502901394585591344857264922082485247) * 10^40
        + 73902538032104504990978217583782783785) * 10^40
        + 5378542200175391717488725481533126593843) * 10^40
        + 5924324443208217707883205424001873932415) * 10^40
        + 3989823758211982224178369462026084516635) * 10^40
        + 8839348901602036784738375862198529692591) * 10^40
        + 6089921054245020106088547579405073344331)) : ℚ) /
        (((((((12697232050594593562320963175007194215 * 10^40
        + 1556298079087902194171468318092965633669) * 10^40
        + 4898525308953027751825049147880516572946) * 10^40
        + 9565121674879590365345931175159331903770) * 10^40
        + 8571217716198470118600498552181009463212) * 10^40
        + 3242601767758447001585171323214256684864) * 10^40
        + 5082607752074929374382440182574226667467) * 10^40
        + 792580974989380307335543653727127732224)))

noncomputable def batchN02705MinusP026Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP026BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP026Center2654‖ ≤ batchN02705MinusP026Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP026Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP026Input2654]
  have hs : compactExp2547 batchN02705MinusP026Input2654 13 =
      (batchN02705MinusP026Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP026Input2654 13).2 : ℝ) =
      batchN02705MinusP026Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP026Error2654]
  have h := compactExp_error2547 batchN02705MinusP026Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP026Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP026Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP026DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP026Factor2654 * embedPair2542 batchN02705MinusP026Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP026Factor2654 : ℝ) * batchN02705MinusP026Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP026Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP026Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP026BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP026Factor2654)

def batchN02705MinusP027Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((21078498488072348391776841 : ℚ) /
        737869762948382064640000000))

def batchN02705MinusP027Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP027Factor2654 : RatPair2542 := ((((((((((((((130146406203308984840452 * 10^40
        + 2363668271614903749271625088109837955482) * 10^40
        + 9673769028997070427337739909692918059198) * 10^40
        + 5887820764810445636668643924457549706913) * 10^40
        + 4879352893317207414592523862942689182603) * 10^40
        + 165190256973911222013321252417419522062) * 10^40
        + 3921145453486545319309563898399454173958) * 10^40
        + 778294608048292325249004764784046061624) * 10^40
        + 2393537108350286162114988548736460864327) * 10^40
        + 2852272299599602705725128138070130158611) * 10^40
        + 3882179264754382217590919974665595784896) * 10^40
        + 4356604184383917474131272943838626374731) : ℚ) /
        (((((((((((89228 * 10^40
        + 5893915875373124522602893320486103898392) * 10^40
        + 6500843554426999936702560851451268737802) * 10^40
        + 8203180392992352885805647977881229469392) * 10^40
        + 5978389587094376851615862457128386385858) * 10^40
        + 3381626607662351353756047421134865303941) * 10^40
        + 3867193375101804922675037889581330264295) * 10^40
        + 7285158711758447529717263081578211440714) * 10^40
        + 4485962550037376082956768045547603797457) * 10^40
        + 2562334900921548450515929509558038165326) * 10^40
        + 3154390629306360011966379563736408677058) * 10^40
        + 7532605494061090980304875538607828369408)),
    (((-((((((((2967892836991 * 10^40
        + 6218472298142735777028274899238228584835) * 10^40
        + 2518093788142784203569678509127058080338) * 10^40
        + 1788438821922516405205222194640094274355) * 10^40
        + 6292487781906471902725990805911415711481) * 10^40
        + 8549904943502597345358514381317669821898) * 10^40
        + 9282003800031413560277293352115015839918) * 10^40
        + 9871418502598387279222754193769766715477) * 10^40
        + 3590039582140783225803926665723141044133)) : ℚ) /
        (((((((101577856404756748498567705400057553721 * 10^40
        + 2450384632703217553371746544743725069355) * 10^40
        + 9188202471624222014600393183044132583575) * 10^40
        + 6520973399036722922767449401274655230166) * 10^40
        + 8569741729587760948803988417448075705698) * 10^40
        + 5940814142067576012681370585714053478916) * 10^40
        + 660862016599434995059521460593813339736) * 10^40
        + 6340647799915042458684349229817021857792)))

noncomputable def batchN02705MinusP027Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP027BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP027Center2654‖ ≤ batchN02705MinusP027Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP027Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP027Input2654]
  have hs : compactExp2547 batchN02705MinusP027Input2654 13 =
      (batchN02705MinusP027Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP027Input2654 13).2 : ℝ) =
      batchN02705MinusP027Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP027Error2654]
  have h := compactExp_error2547 batchN02705MinusP027Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP027Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP027Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP027DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP027Factor2654 * embedPair2542 batchN02705MinusP027Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP027Factor2654 : ℝ) * batchN02705MinusP027Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP027Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP027Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP027BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP027Factor2654)

def batchN02705MinusP028Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((85917920262979814161755141 : ℚ) /
        2951479051793528258560000000))

def batchN02705MinusP028Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP028Factor2654 : RatPair2542 := ((((((((((((((2082342498183447410279724 *
    10^40
        + 8772547500524573394663558692495481531340) * 10^40
        + 6701834488983863560655813521571617429554) * 10^40
        + 933838856843380196851301403369870497206) * 10^40
        + 329541740648740731673166200892879314260) * 10^40
        + 1901543050519840052352100676760612104149) * 10^40
        + 294694236435353010837771555126050956578) * 10^40
        + 8934794688604234902918203896304856448116) * 10^40
        + 5820705576921017839024156456592199872246) * 10^40
        + 2845746540173780647217181972124706568153) * 10^40
        + 5704480499156556050124651823599301411659) * 10^40
        + 3136368892848124301375792771624055960291) : ℚ) /
        (((((((((((1427657 * 10^40
        + 4302654005969992361646293127777662374282) * 10^40
        + 4013496870831998987240973623220299804845) * 10^40
        + 1250886287877646172890367646099671510281) * 10^40
        + 5654233393510029625853799314054182173733) * 10^40
        + 4106025722597621660096758738157844863062) * 10^40
        + 1875094001628878762800606233301284228731) * 10^40
        + 6562539388135160475476209305251383051431) * 10^40
        + 1775400800598017327308288728761660759316) * 10^40
        + 997358414744775208254872152928610645221) * 10^40
        + 470250068901760191462073019782538832940) * 10^40
        + 521687904977455684878008617725253910528)),
    (((-((((((((193558515752886 * 10^40
        + 2838834691356396070736921710442445314856) * 10^40
        + 6686700150409300909642435456898502477971) * 10^40
        + 3789658354348650771380828683886384160105) * 10^40
        + 7958832302019273601328631271407186152641) * 10^40
        + 1658291444762533922675026879625728301654) * 10^40
        + 4828776000808228198015542099641957687964) * 10^40
        + 3530089296497094756204746559609327970458) * 10^40
        + 382094744915045231812107498653460825273)) : ℚ) /
        (((((((6500982809904431903908333145603683438159 * 10^40
        + 6824616493005923415791778863598404438778) * 10^40
        + 8044958183950208934425163714824485348841) * 10^40
        + 7342297538350267057116761681577934730678) * 10^40
        + 8463470693616700723455258716676845164710) * 10^40
        + 212105092324864811607717485699422650628) * 10^40
        + 2295169062363839683809373478004053743144) * 10^40
        + 5801459194562717355798350708289398898688)))

noncomputable def batchN02705MinusP028Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP028BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP028Center2654‖ ≤ batchN02705MinusP028Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP028Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP028Input2654]
  have hs : compactExp2547 batchN02705MinusP028Input2654 13 =
      (batchN02705MinusP028Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP028Input2654 13).2 : ℝ) =
      batchN02705MinusP028Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP028Error2654]
  have h := compactExp_error2547 batchN02705MinusP028Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP028Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP028Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP028DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP028Factor2654 * embedPair2542 batchN02705MinusP028Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP028Factor2654 : ℝ) * batchN02705MinusP028Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP028Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP028Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP028BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP028Factor2654)

def batchN02705MinusP029Input2654 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((88359795091650310792539297 : ℚ) /
        2951479051793528258560000000))

def batchN02705MinusP029Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02705MinusP029Factor2654 : RatPair2542 := ((((((((((((((2082342496516510483328839 *
    10^40
        + 4386703752408959708502479039611620286070) * 10^40
        + 5655616962127727240709004646542629057915) * 10^40
        + 5123821671065420439789206957985344136907) * 10^40
        + 8055756164109780527253169534186012318798) * 10^40
        + 6046146632128584092028909273566769395874) * 10^40
        + 2171232383172358208739926572801075465384) * 10^40
        + 3588170922949252964143675353963650715425) * 10^40
        + 1087439201553004290457043023755250599235) * 10^40
        + 8580791767601314829586910596387163416696) * 10^40
        + 1363321364057255910255467820875702391312) * 10^40
        + 6060203963562822543592479025622870497307) : ℚ) /
        (((((((((((1427657 * 10^40
        + 4302654005969992361646293127777662374282) * 10^40
        + 4013496870831998987240973623220299804845) * 10^40
        + 1250886287877646172890367646099671510281) * 10^40
        + 5654233393510029625853799314054182173733) * 10^40
        + 4106025722597621660096758738157844863062) * 10^40
        + 1875094001628878762800606233301284228731) * 10^40
        + 6562539388135160475476209305251383051431) * 10^40
        + 1775400800598017327308288728761660759316) * 10^40
        + 997358414744775208254872152928610645221) * 10^40
        + 470250068901760191462073019782538832940) * 10^40
        + 521687904977455684878008617725253910528)),
    (((-((((((((199059645953951 * 10^40
        + 7746301494369431546237102048628105070912) * 10^40
        + 7678942983326961568460157444971823325167) * 10^40
        + 5529777956414874247637203742458353296315) * 10^40
        + 4021137621290258329506194614127701439592) * 10^40
        + 6215279195647853491245005969771116871030) * 10^40
        + 9377775936402418467297215039441477868237) * 10^40
        + 1534315888250385532243418680903195712689) * 10^40
        + 9021875561609217820755172744134372773453)) : ℚ) /
        (((((((6500982809904431903908333145603683438159 * 10^40
        + 6824616493005923415791778863598404438778) * 10^40
        + 8044958183950208934425163714824485348841) * 10^40
        + 7342297538350267057116761681577934730678) * 10^40
        + 8463470693616700723455258716676845164710) * 10^40
        + 212105092324864811607717485699422650628) * 10^40
        + 2295169062363839683809373478004053743144) * 10^40
        + 5801459194562717355798350708289398898688)))

noncomputable def batchN02705MinusP029Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02705MinusP029BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP029Center2654‖ ≤ batchN02705MinusP029Error2654 := by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02705MinusP029Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02705MinusP029Input2654]
  have hs : compactExp2547 batchN02705MinusP029Input2654 13 =
      (batchN02705MinusP029Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02705MinusP029Input2654 13).2 : ℝ) =
      batchN02705MinusP029Error2654 := by
    rw [hs]
    norm_num [batchN02705MinusP029Error2654]
  have h := compactExp_error2547 batchN02705MinusP029Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      batchN02705MinusPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchN02705MinusP029Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02705MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02705MinusP029Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02705MinusP029DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02705MinusPosition2654 -
      embedPair2542 batchN02705MinusP029Factor2654 * embedPair2542 batchN02705MinusP029Center2654‖
          ≤
        (pairMagnitude2542 batchN02705MinusP029Factor2654 : ℝ) * batchN02705MinusP029Error2654 :=
            by
  have hx : |batchN02705MinusPosition2654| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchN02705MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchN02705MinusPosition2654 = embedPair2542
          batchN02705MinusP029Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02705MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02705MinusP029Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02705MinusP029BaseError2654
    (embedPair_magnitude2542 batchN02705MinusP029Factor2654)

theorem batchN02705MinusGrid2654 :
    -stripRadius2303 + (2705 : ℝ) * (2 * stripRadius2303 / 10240) =
      batchN02705MinusPosition2654 := by
  norm_num [stripRadius2303, batchN02705MinusPosition2654]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchN02705MinusP000DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP001DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP002DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP003DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP004DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP005DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP006DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP007DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP008DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP009DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP010DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP011DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP012DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP013DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP014DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP015DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP016DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP017DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP018DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP019DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP020DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP021DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP022DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP023DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP024DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP025DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP026DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP027DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP028DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusP029DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02705MinusGrid2654
