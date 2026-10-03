import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def neighborMidpointPosition2557 : ℝ := (((-316997636837) : ℝ) /
        102400000000)

theorem neighborMidpointZero2557 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def neighborMidpointP000Center2557 : RatPair2542 := (0, 0)

def neighborMidpointP000Factor2557 : RatPair2542 := (0, 0)

noncomputable def neighborMidpointP000Error2557 : ℝ := 0

theorem neighborMidpointP000Exterior2557 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩ neighborMidpointPosition2557 = 0
        :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |neighborMidpointPosition2557| := by
    norm_num [storedWidth, neighborMidpointPosition2557]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem neighborMidpointP000BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP000Center2557‖ ≤ neighborMidpointP000Error2557 := by
  rw [neighborMidpointP000Exterior2557]
  norm_num [neighborMidpointP000Center2557, neighborMidpointP000Error2557,
      neighborMidpointZero2557]

theorem neighborMidpointP000DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP000Factor2557 * embedPair2542 neighborMidpointP000Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP000Factor2557 : ℝ) * neighborMidpointP000Error2557 :=
            by
  rw [neighborMidpointP000Exterior2557]
  norm_num [neighborMidpointP000Factor2557, neighborMidpointP000Center2557,
      neighborMidpointP000Error2557,
      neighborMidpointZero2557, pairMagnitude2542]

def neighborMidpointP001Input2557 : RatPair2542 := ((((-((680 * 10^40
        + 2359669581322474996551422944228839689461) * 10^40
        + 9496472096148730365866155936046153909317)) : ℚ) /
        ((1887 * 10^40
        + 2004981127838775906823533063469056624951) * 10^40
        + 8551390361977395865728009214361600000000)),
    ((1751187200352461984105434273 : ℚ) /
        7378697629483820646400000000))

def neighborMidpointP001Center2557 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def neighborMidpointP001Factor2557 : RatPair2542 := ((((((((((7449920545663679375646215124656 *
    10^40
        + 8046308662392504222519462926541674434271) * 10^40
        + 6770568193965929931162765146404267927017) * 10^40
        + 4124758036927893173340865271610747265000) * 10^40
        + 5957992693034805066681772774695319042961) * 10^40
        + 7933949590138730702780202839767412187345) * 10^40
        + 7209987982163304857684217658982018019444) * 10^40
        + 8550303230375391786103643098547792528855) : ℚ) /
        (((((((20782228201096786123743073 * 10^40
        + 2525599440192868318545638888635957745059) * 10^40
        + 9405355048679421823974805922620803083835) * 10^40
        + 134384377627067432611882467793770205759) * 10^40
        + 2248084014968038169560658099908606349519) * 10^40
        + 5965338320913338551455551611648447457580) * 10^40
        + 1784933801424422902630966861891637528253) * 10^40
        + 8972691837633318734907394330777484263424)),
    (((-(((21597506101958355329589622747273366925 * 10^40
        + 4089250819837615411493885140640216663263) * 10^40
        + 2150348960396294007482353587144191119000) * 10^40
        + 2174515399371684962836720706024792012749)) : ℚ) /
        (((455875292169873866742237920983486 * 10^40
        + 6783956086599694778299636289552455319313) * 10^40
        + 140164076794329784882985441410357394279) * 10^40
        + 7962190625717799044169771443964103098368)))

noncomputable def neighborMidpointP001Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP001BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP001Center2557‖ ≤ neighborMidpointP001Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP001Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP001Input2557]
  have hs : compactExp2547 neighborMidpointP001Input2557 9 =
      (neighborMidpointP001Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP001Input2557 9).2 : ℝ) =
      neighborMidpointP001Error2557 := by
    rw [hs]
    norm_num [neighborMidpointP001Error2557]
  have h := compactExp_error2547 neighborMidpointP001Input2557 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          neighborMidpointP001Input2557)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP001Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP001DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP001Factor2557 * embedPair2542 neighborMidpointP001Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP001Factor2557 : ℝ) * neighborMidpointP001Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP001Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP001Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP001BaseError2557
    (embedPair_magnitude2542 neighborMidpointP001Factor2557)

def neighborMidpointP002Input2557 : RatPair2542 := ((((-((368 * 10^40
        + 7290339766846001116902218265993779498897) * 10^40
        + 7088111836939023189208002063625267770453)) : ℚ) /
        ((1497 * 10^40
        + 8141619820548260689071119881802050250108) * 10^40
        + 126749615182671161751511708467200000000)),
    (((-1751187200352461984105434273) : ℚ) /
        3689348814741910323200000000))

def neighborMidpointP002Center2557 : RatPair2542 := ((((-166060058513088863589) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-527738651359980139471) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def neighborMidpointP002Factor2557 : RatPair2542 := ((((((((((22079543943086867215242797137 *
    10^40
        + 1536219876398788159610145350689506108328) * 10^40
        + 2053539105792306798878184424101091211743) * 10^40
        + 7711540973932728206890069121057813893266) * 10^40
        + 7228276477947848938737039020111110617650) * 10^40
        + 5984539870966973169292764996420551504397) * 10^40
        + 3631395510566730237276726014194963657379) * 10^40
        + 7280741795392549156550614342199757781655) : ℚ) /
        (((((((131938533391840953334720621 * 10^40
        + 8825347156182027895959798474464112489693) * 10^40
        + 9671792158414417939027950473923060014877) * 10^40
        + 4289176939882047705810305489157946560841) * 10^40
        + 718066265242911267693960887873068942621) * 10^40
        + 1971332196028535473014904982177198305062) * 10^40
        + 433556986168407453096854955400435249183) * 10^40
        + 3338731144756634898574251359112280408064)),
    (((((3802366451646914591224252247326548159 * 10^40
        + 2869423934301185848299644988981539694517) * 10^40
        + 5394971154794363712231172465122031016006) * 10^40
        + 9752910571903196108010819493197086796269) : ℚ) /
        (((1148644999083010648418935679828095 * 10^40
        + 8725964118606440136677067135257354069503) * 10^40
        + 3424071534709150559522883614032650462252) * 10^40
        + 6050307411681401024348246517973681963008)))

noncomputable def neighborMidpointP002Error2557 : ℝ := ((2329981941229747173 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP002BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP002Center2557‖ ≤ neighborMidpointP002Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP002Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP002Input2557]
  have hs : compactExp2547 neighborMidpointP002Input2557 8 =
      (neighborMidpointP002Center2557, ((2329981941229747173 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP002Input2557 8).2 : ℝ) =
      neighborMidpointP002Error2557 := by
    rw [hs]
    norm_num [neighborMidpointP002Error2557]
  have h := compactExp_error2547 neighborMidpointP002Input2557 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          neighborMidpointP002Input2557)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP002Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP002DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP002Factor2557 * embedPair2542 neighborMidpointP002Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP002Factor2557 : ℝ) * neighborMidpointP002Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP002Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP002Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP002BaseError2557
    (embedPair_magnitude2542 neighborMidpointP002Factor2557)

def neighborMidpointP003Input2557 : RatPair2542 := ((((-((49143 * 10^40
        + 6011416000909434456699560500431832804347) * 10^40
        + 9266203793363679842003296495853985813031)) : ℚ) /
        ((271270 * 10^40
        + 3087127989071126638748716684898100330217) * 10^40
        + 4625034212383035136128999122534400000000)),
    (((-1751187200352461984105434273) : ℚ) /
        3689348814741910323200000000))

def neighborMidpointP003Center2557 : RatPair2542 := ((((-2810770862962537528992455579) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-279144567819279970950042617) : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)))

def neighborMidpointP003Factor2557 : RatPair2542 :=
    ((((-(((((((1705574261520951096475213538755440112082 *
    10^40
        + 8114288590789858302727792223712113451387) * 10^40
        + 6187028730493642526899321626563369712011) * 10^40
        + 8357341282027668724160379750936954223405) * 10^40
        + 2578375042919846742451975030354769756701) * 10^40
        + 2543693128737940413752387626463495651889) * 10^40
        + 1376146822730081718704797212803930694017) * 10^40
        + 325033288560433376738036968116818862305)) : ℚ) /
        (((((((1277589923764623072860491930669287246 * 10^40
        + 5323592583042906058469514251362729734024) * 10^40
        + 7201655151557055716567626270175597351831) * 10^40
        + 1673047929909420137682320047349742412503) * 10^40
        + 7471100543210785281194830378611615594163) * 10^40
        + 1121952845627529378910118456416393472063) * 10^40
        + 4269302007342068507065934778311564815491) * 10^40
        + 8617433083633748807303403993846268297216)),
    ((((((13 * 10^40
        + 1473879505161986395632534360798430359345) * 10^40
        + 3656245912575621509673646265841227067488) * 10^40
        + 2882307445346057951614023736360997431626) * 10^40
        + 4416593663006876375596334911866620121103) : ℚ) /
        (((113030523477714774001326677076218828015 * 10^40
        + 3676547668716266699841468297573921341466) * 10^40
        + 8043997324608289989815148230992554401246) * 10^40
        + 1396662453661173234325213974407042564096)))

noncomputable def neighborMidpointP003Error2557 : ℝ := ((18477611950782990587381195 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem neighborMidpointP003BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP003Center2557‖ ≤ neighborMidpointP003Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP003Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP003Input2557]
  have hs : compactExp2547 neighborMidpointP003Input2557 8 =
      (neighborMidpointP003Center2557, ((18477611950782990587381195 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP003Input2557 8).2 : ℝ) =
      neighborMidpointP003Error2557 := by
    rw [hs]
    norm_num [neighborMidpointP003Error2557]
  have h := compactExp_error2547 neighborMidpointP003Input2557 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          neighborMidpointP003Input2557)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP003Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP003DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP003Factor2557 * embedPair2542 neighborMidpointP003Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP003Factor2557 : ℝ) * neighborMidpointP003Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP003Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP003Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP003BaseError2557
    (embedPair_magnitude2542 neighborMidpointP003Factor2557)

def neighborMidpointP004Input2557 : RatPair2542 := ((((-((42060 * 10^40
        + 8531003492838714641689709026109695523485) * 10^40
        + 5895779372635132614000718573692808252197)) : ℚ) /
        ((268088 * 10^40
        + 9931593660330219898315158741078364901345) * 10^40
        + 3125060162297126925824073714892800000000)),
    ((1751187200352461984105434273 : ℚ) /
        3689348814741910323200000000))

def neighborMidpointP004Center2557 : RatPair2542 := ((((-1403158774414137969603370370841) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((4459236771826582470471890528117 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def neighborMidpointP004Factor2557 : RatPair2542 :=
    ((((-(((((((201352774864914554944676663004177237771 *
    10^40
        + 8192128092948390589295904056678192074991) * 10^40
        + 5473469602854731706287663902183015105162) * 10^40
        + 8736793383937841785206284506757880056969) * 10^40
        + 941962940086535188603320723385093138835) * 10^40
        + 1031595450363300739245304220976244134741) * 10^40
        + 4866000987962212496766137829767580588690) * 10^40
        + 7667030570363583416142337240234307474345)) : ℚ) /
        (((((((135411595928757123875702755020406882 * 10^40
        + 7430206676041205504495923201060692890263) * 10^40
        + 9944180713238354832764943125854335799997) * 10^40
        + 9802366833398097661468701168259199408964) * 10^40
        + 9205313068610634292439206368383520502624) * 10^40
        + 3548336412481610697271534007440803450732) * 10^40
        + 4549188198565622983408235211953852997623) * 10^40
        + 1643313470550144096294061833208687755264)),
    (((-((((2 * 10^40
        + 2144510628675820975537671222597019818734) * 10^40
        + 1839415316833907068980174520006605333693) * 10^40
        + 7386502382502951480190423567427315731976) * 10^40
        + 4533528219281191910004500968939772841869)) : ℚ) /
        (((36798314625639735115744017436583249715 * 10^40
        + 1212116575041651561384933503454207921239) * 10^40
        + 8756483739036199863969920337379582093071) * 10^40
        + 3615121170672903486712689654810393182208)))

noncomputable def neighborMidpointP004Error2557 : ℝ := ((9002995936150092295044756665 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem neighborMidpointP004BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP004Center2557‖ ≤ neighborMidpointP004Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP004Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP004Input2557]
  have hs : compactExp2547 neighborMidpointP004Input2557 8 =
      (neighborMidpointP004Center2557, ((9002995936150092295044756665 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP004Input2557 8).2 : ℝ) =
      neighborMidpointP004Error2557 := by
    rw [hs]
    norm_num [neighborMidpointP004Error2557]
  have h := compactExp_error2547 neighborMidpointP004Input2557 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          neighborMidpointP004Input2557)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP004Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP004DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP004Factor2557 * embedPair2542 neighborMidpointP004Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP004Factor2557 : ℝ) * neighborMidpointP004Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP004Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP004Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP004BaseError2557
    (embedPair_magnitude2542 neighborMidpointP004Factor2557)

def neighborMidpointP005Center2557 : RatPair2542 := (0, 0)

def neighborMidpointP005Factor2557 : RatPair2542 := (0, 0)

noncomputable def neighborMidpointP005Error2557 : ℝ := 0

theorem neighborMidpointP005Exterior2557 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩ neighborMidpointPosition2557 = 0
        :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |neighborMidpointPosition2557| := by
    norm_num [storedWidth, neighborMidpointPosition2557]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem neighborMidpointP005BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP005Center2557‖ ≤ neighborMidpointP005Error2557 := by
  rw [neighborMidpointP005Exterior2557]
  norm_num [neighborMidpointP005Center2557, neighborMidpointP005Error2557,
      neighborMidpointZero2557]

theorem neighborMidpointP005DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP005Factor2557 * embedPair2542 neighborMidpointP005Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP005Factor2557 : ℝ) * neighborMidpointP005Error2557 :=
            by
  rw [neighborMidpointP005Exterior2557]
  norm_num [neighborMidpointP005Factor2557, neighborMidpointP005Center2557,
      neighborMidpointP005Error2557,
      neighborMidpointZero2557, pairMagnitude2542]

def neighborMidpointP006Input2557 : RatPair2542 := ((((-350707076232462765060490559797657249) : ℚ)
    /
        587942314986765992027147468800000000),
    ((0 : ℚ) /
        1))

def neighborMidpointP006Center2557 : RatPair2542 := (((1012967903212591 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def neighborMidpointP006Factor2557 : RatPair2542 := (((((466324943756667 * 10^40
        + 368611304423822037147767235561645605759) * 10^40
        + 6118146822495087720715763336846810476569) : ℚ) /
        ((91092303659 * 10^40
        + 3734186146287179594316829867022364143218) * 10^40
        + 2946903179357630882863053347387241906276)),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP006Error2557 : ℝ := ((1228940677751 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem neighborMidpointP006BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP006Center2557‖ ≤ neighborMidpointP006Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP006Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP006Input2557]
  have hs : compactExp2547 neighborMidpointP006Input2557 7 =
      (neighborMidpointP006Center2557, ((1228940677751 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP006Input2557 7).2 : ℝ) =
      neighborMidpointP006Error2557 := by
    rw [hs]
    norm_num [neighborMidpointP006Error2557]
  have h := compactExp_error2547 neighborMidpointP006Input2557 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          neighborMidpointP006Input2557)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP006Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP006DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP006Factor2557 * embedPair2542 neighborMidpointP006Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP006Factor2557 : ℝ) * neighborMidpointP006Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP006Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP006Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP006BaseError2557
    (embedPair_magnitude2542 neighborMidpointP006Factor2557)

def neighborMidpointP007Input2557 : RatPair2542 := ((((-((49143 * 10^40
        + 6011416000909434456699560500431832804347) * 10^40
        + 9266203793363679842003296495853985813031)) : ℚ) /
        ((67817 * 10^40
        + 5771781997267781659687179171224525082554) * 10^40
        + 3656258553095758784032249780633600000000)),
    ((0 : ℚ) /
        1))

def neighborMidpointP007Center2557 : RatPair2542 := (((5277156944633198255707934881 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def neighborMidpointP007Factor2557 : RatPair2542 := ((((((((((53087878924 * 10^40
        + 9983878103656465979179116670866002199381) * 10^40
        + 7719808836311761339923844546683821109588) * 10^40
        + 286145645146966168301824783177664179806) * 10^40
        + 7930748280658700185558571689914796291110) * 10^40
        + 5045940064124529814361151288631740963422) * 10^40
        + 3823383092297244679800898972460876354838) * 10^40
        + 7468958067722347600804545065601535683449) : ℚ) /
        (((((((258007230 * 10^40
        + 4031242290861211161553580853642871953942) * 10^40
        + 17085347620107399223438183325373725783) * 10^40
        + 8014599759851950543489692413636564878887) * 10^40
        + 8722658837265336781184268085360952162911) * 10^40
        + 6396645507960309336759777893881761399800) * 10^40
        + 4570394229397507350607064815239371617398) * 10^40
        + 5651320270889390403218180262406142733796)),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP007Error2557 : ℝ := ((95807326048565708797629 : ℝ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))

theorem neighborMidpointP007BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP007Center2557‖ ≤ neighborMidpointP007Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP007Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP007Input2557]
  have hs : compactExp2547 neighborMidpointP007Input2557 6 =
      (neighborMidpointP007Center2557, ((95807326048565708797629 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP007Input2557 6).2 : ℝ) =
      neighborMidpointP007Error2557 := by
    rw [hs]
    norm_num [neighborMidpointP007Error2557]
  have h := compactExp_error2547 neighborMidpointP007Input2557 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          neighborMidpointP007Input2557)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP007Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP007DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP007Factor2557 * embedPair2542 neighborMidpointP007Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP007Factor2557 : ℝ) * neighborMidpointP007Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP007Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP007Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP007BaseError2557
    (embedPair_magnitude2542 neighborMidpointP007Factor2557)

def neighborMidpointP008Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1261197741322974723791937589 : ℚ) /
        944473296573929042739200000000))

def neighborMidpointP008Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP008Factor2557 : RatPair2542 := (((((((((((66232 * 10^40
        + 9249565126966123692841214322552506932484) * 10^40
        + 1087317328248965656706057424880005071651) * 10^40
        + 9221276610437498612793121322207144796741) * 10^40
        + 2591850751463395812112297102422747656585) * 10^40
        + 2826197276567578559729683383266419203005) * 10^40
        + 9951718546284428489282129033778812271657) * 10^40
        + 5210325568265885407154923253866256375162) * 10^40
        + 8085465048502080122245254642964337958375) : ℚ) /
        (((((((4169066886545017168806093577099 * 10^40
        + 2804841626764728485775059918649364161105) * 10^40
        + 7156297582235054199635008787006296965286) * 10^40
        + 684020108796962676512317814233549069182) * 10^40
        + 956436925361386995735136373577472584497) * 10^40
        + 8294342970545963682423715151865053193691) * 10^40
        + 7217764807399723230526878725170332382082) * 10^40
        + 9463760507013221333253475845304236376064)),
    (((-((((7275 * 10^40
        + 6580122055820529065832288323097895407868) * 10^40
        + 4257519228355414581475693469830066826461) * 10^40
        + 27132549859309090568438589694553093618) * 10^40
        + 3063714530797200223502711157743984624379)) : ℚ) /
        (((204182929907106024189758774225541583 * 10^40
        + 8214588488908717377422432983680743599465) * 10^40
        + 4242336465525581924812698515115500599032) * 10^40
        + 9199626782652513119530945102618392788992)))

noncomputable def neighborMidpointP008Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP008BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP008Center2557‖ ≤ neighborMidpointP008Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP008Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP008Input2557]
  have hs : compactExp2547 neighborMidpointP008Input2557 15 =
      (neighborMidpointP008Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP008Input2557 15).2 : ℝ) =
      neighborMidpointP008Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP008Error2557]
  have h := compactExp_error2547 neighborMidpointP008Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP008Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP008Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP008DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP008Factor2557 * embedPair2542 neighborMidpointP008Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP008Factor2557 : ℝ) * neighborMidpointP008Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP008Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP008Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP008BaseError2557
    (embedPair_magnitude2542 neighborMidpointP008Factor2557)

def neighborMidpointP009Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1875731480065194149050312107 : ℚ) /
        944473296573929042739200000000))

def neighborMidpointP009Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP009Factor2557 : RatPair2542 := (((((((((((66232 * 10^40
        + 9249564117486212525598558952223316925057) * 10^40
        + 562391673534930544265558236808511744103) * 10^40
        + 9980629436389025577350793239345607380889) * 10^40
        + 3363847929144732865237568996713782374964) * 10^40
        + 3726011930506835641450533710146091607022) * 10^40
        + 4071626266233375309818201596107448493311) * 10^40
        + 241045711701614314270001310949219352197) * 10^40
        + 2373286793969378769140895108306010398887) : ℚ) /
        (((((((4169066886545017168806093577099 * 10^40
        + 2804841626764728485775059918649364161105) * 10^40
        + 7156297582235054199635008787006296965286) * 10^40
        + 684020108796962676512317814233549069182) * 10^40
        + 956436925361386995735136373577472584497) * 10^40
        + 8294342970545963682423715151865053193691) * 10^40
        + 7217764807399723230526878725170332382082) * 10^40
        + 9463760507013221333253475845304236376064)),
    (((-((((3606 * 10^40
        + 9365716240783086899922985439674197296168) * 10^40
        + 2495802569896390337100802537672132216722) * 10^40
        + 9738515792484286776153702172760882025864) * 10^40
        + 8676801114522618409531438289768396139959)) : ℚ) /
        (((68060976635702008063252924741847194 * 10^40
        + 6071529496302905792474144327893581199821) * 10^40
        + 8080778821841860641604232838371833533010) * 10^40
        + 9733208927550837706510315034206130929664)))

noncomputable def neighborMidpointP009Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP009BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP009Center2557‖ ≤ neighborMidpointP009Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP009Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP009Input2557]
  have hs : compactExp2547 neighborMidpointP009Input2557 15 =
      (neighborMidpointP009Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP009Input2557 15).2 : ℝ) =
      neighborMidpointP009Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP009Error2557]
  have h := compactExp_error2547 neighborMidpointP009Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP009Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP009Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP009DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP009Factor2557 * embedPair2542 neighborMidpointP009Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP009Factor2557 : ℝ) * neighborMidpointP009Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP009Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP009Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP009BaseError2557
    (embedPair_magnitude2542 neighborMidpointP009Factor2557)

def neighborMidpointP010Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1115820674697574220099746077 : ℚ) /
        472236648286964521369600000000))

def neighborMidpointP010Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP010Factor2557 : RatPair2542 := (((((((((((16558 * 10^40
        + 2312390837993824680006254828453377700910) * 10^40
        + 5573127893375043823768141196158058287750) * 10^40
        + 2097157179169092325116889302550668349316) * 10^40
        + 1618851194195414411692338198179603518651) * 10^40
        + 9237766839310911631861524951678725533530) * 10^40
        + 485261008039358315089184890250820581675) * 10^40
        + 4998285833815105459206887772583541406155) * 10^40
        + 5846654606616998333105457989156452774295) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((2145 * 10^40
        + 6666061823781890121257139222451578474102) * 10^40
        + 1374665947283086830292766292345604948783) * 10^40
        + 3813933232947581050634450538265927791615) * 10^40
        + 3417453811148397864839834108250113516849)) : ℚ) /
        (((34030488317851004031626462370923597 * 10^40
        + 3035764748151452896237072163946790599910) * 10^40
        + 9040389410920930320802116419185916766505) * 10^40
        + 4866604463775418853255157517103065464832)))

noncomputable def neighborMidpointP010Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP010BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP010Center2557‖ ≤ neighborMidpointP010Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP010Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP010Input2557]
  have hs : compactExp2547 neighborMidpointP010Input2557 15 =
      (neighborMidpointP010Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP010Input2557 15).2 : ℝ) =
      neighborMidpointP010Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP010Error2557]
  have h := compactExp_error2547 neighborMidpointP010Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP010Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP010Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP010DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP010Factor2557 * embedPair2542 neighborMidpointP010Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP010Factor2557 : ℝ) * neighborMidpointP010Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP010Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP010Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP010BaseError2557
    (embedPair_magnitude2542 neighborMidpointP010Factor2557)

def neighborMidpointP011Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1234468557765072383258963437 : ℚ) /
        472236648286964521369600000000))

def neighborMidpointP011Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP011Factor2557 : RatPair2542 := (((((((((((16558 * 10^40
        + 2312390691968380960525302831491952019268) * 10^40
        + 6147393225604588089498079135350172073139) * 10^40
        + 4751585622076805519258734175385388907789) * 10^40
        + 3047029058638263414657979298779489009930) * 10^40
        + 7213986167913798791779411126023337172372) * 10^40
        + 4463875863454445070997953225968739380528) * 10^40
        + 1842356024362969767701630189446810858312) * 10^40
        + 7189433602398298484647502306164630318455) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((7121 * 10^40
        + 4614162706990175754009016401413440239079) * 10^40
        + 923662576033759063830390439736320540017) * 10^40
        + 3251276507372735673586103064733013699180) * 10^40
        + 8400964132335516420987819275459434157507)) : ℚ) /
        (((102091464953553012094879387112770791 * 10^40
        + 9107294244454358688711216491840371799732) * 10^40
        + 7121168232762790962406349257557750299516) * 10^40
        + 4599813391326256559765472551309196394496)))

noncomputable def neighborMidpointP011Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP011BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP011Center2557‖ ≤ neighborMidpointP011Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP011Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP011Input2557]
  have hs : compactExp2547 neighborMidpointP011Input2557 15 =
      (neighborMidpointP011Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP011Input2557 15).2 : ℝ) =
      neighborMidpointP011Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP011Error2557]
  have h := compactExp_error2547 neighborMidpointP011Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP011Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP011Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP011DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP011Factor2557 * embedPair2542 neighborMidpointP011Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP011Factor2557 : ℝ) * neighborMidpointP011Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP011Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP011Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP011BaseError2557
    (embedPair_magnitude2542 neighborMidpointP011Factor2557)

def neighborMidpointP012Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((27147174540145397472943033 : ℚ) /
        9444732965739290427392000000))

def neighborMidpointP012Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP012Factor2557 : RatPair2542 := (((((((((((4139 * 10^40
        + 5578097631294554828926073469023182862839) * 10^40
        + 9348812517503306566884993090034016073547) * 10^40
        + 280974804375242679356775023435510228782) * 10^40
        + 7494311933671910988325661568439871133146) * 10^40
        + 4000532331670340779090263889577769060970) * 10^40
        + 2412425814344701097627222799661465319721) * 10^40
        + 23264715229843458240685519203953047041) * 10^40
        + 2578205206008826364296959731514528962751) : ℚ) /
        (((((((260566680409063573050380848568 * 10^40
        + 7050302601672795530360941244915585260069) * 10^40
        + 1072268598889690887477188049187893560330) * 10^40
        + 3792751256799810167282019863389596816823) * 10^40
        + 8809777307835086687233446023348592036531) * 10^40
        + 1143396435659122730151482196991565824605) * 10^40
        + 7326110300462482701907929920323145773880) * 10^40
        + 1841485031688326333328342240331514773504)),
    (((-((((3915 * 10^40
        + 1980589610778603149190775002059583307258) * 10^40
        + 3678340157910554025777883043004095443626) * 10^40
        + 3275143977313112994776842369993538574416) * 10^40
        + 7224909828145746544190319255683810516575)) : ℚ) /
        (((51045732476776506047439693556385395 * 10^40
        + 9553647122227179344355608245920185899866) * 10^40
        + 3560584116381395481203174628778875149758) * 10^40
        + 2299906695663128279882736275654598197248)))

noncomputable def neighborMidpointP012Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP012BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP012Center2557‖ ≤ neighborMidpointP012Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP012Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP012Input2557]
  have hs : compactExp2547 neighborMidpointP012Input2557 15 =
      (neighborMidpointP012Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP012Input2557 15).2 : ℝ) =
      neighborMidpointP012Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP012Error2557]
  have h := compactExp_error2547 neighborMidpointP012Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP012Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP012Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP012DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP012Factor2557 * embedPair2542 neighborMidpointP012Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP012Factor2557 : ℝ) * neighborMidpointP012Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP012Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP012Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP012BaseError2557
    (embedPair_magnitude2542 neighborMidpointP012Factor2557)

def neighborMidpointP013Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((293869352734311453179388567 : ℚ) /
        94447329657392904273920000000))

def neighborMidpointP013Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP013Factor2557 : RatPair2542 := (((((((((((16558 * 10^40
        + 2312390359410705837307936332250618754821) * 10^40
        + 8695504581664242543105807727004439385259) * 10^40
        + 536657448722020678270646249763375007704) * 10^40
        + 9562140705699998951495510398272794887218) * 10^40
        + 5804203485234123976396678197234490433782) * 10^40
        + 5211550477520769503109076255261887981579) * 10^40
        + 6882940036130754382695848777766070940538) * 10^40
        + 5595711484702106945392887656773628724279) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((2825 * 10^40
        + 4793581116508508053628026293401903084745) * 10^40
        + 5968002808392886135300754806926167843974) * 10^40
        + 4442057353555236162087185599471485172968) * 10^40
        + 2517804878475868355209474388645008644895)) : ℚ) /
        (((34030488317851004031626462370923597 * 10^40
        + 3035764748151452896237072163946790599910) * 10^40
        + 9040389410920930320802116419185916766505) * 10^40
        + 4866604463775418853255157517103065464832)))

noncomputable def neighborMidpointP013Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP013BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP013Center2557‖ ≤ neighborMidpointP013Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP013Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP013Input2557]
  have hs : compactExp2547 neighborMidpointP013Input2557 15 =
      (neighborMidpointP013Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP013Input2557 15).2 : ℝ) =
      neighborMidpointP013Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP013Error2557]
  have h := compactExp_error2547 neighborMidpointP013Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP013Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP013Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP013DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP013Factor2557 * embedPair2542 neighborMidpointP013Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP013Factor2557 : ℝ) * neighborMidpointP013Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP013Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP013Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP013BaseError2557
    (embedPair_magnitude2542 neighborMidpointP013Factor2557)

def neighborMidpointP014Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1676849125948274871802318207 : ℚ) /
        472236648286964521369600000000))

def neighborMidpointP014Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP014Factor2557 : RatPair2542 := (((((((((((16558 * 10^40
        + 2312390017544608387638980161030728423081) * 10^40
        + 8720593589227908806183012332302290914156) * 10^40
        + 8749337648811752269050829106869184494863) * 10^40
        + 7603174526444017470012822287471886883797) * 10^40
        + 5922075097617987304647200258558763329502) * 10^40
        + 9165194306336883452937112537644620429411) * 10^40
        + 2069546374789927452390843525951328434433) * 10^40
        + 9267466253193450266814581478659297034975) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((9673 * 10^40
        + 4876528304860415669112331297156627472914) * 10^40
        + 3077273272622615362170772826707544592675) * 10^40
        + 3068941983308385453968538249937349715353) * 10^40
        + 3671704379209452015263409682082225896977)) : ℚ) /
        (((102091464953553012094879387112770791 * 10^40
        + 9107294244454358688711216491840371799732) * 10^40
        + 7121168232762790962406349257557750299516) * 10^40
        + 4599813391326256559765472551309196394496)))

noncomputable def neighborMidpointP014Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP014BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP014Center2557‖ ≤ neighborMidpointP014Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP014Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP014Input2557]
  have hs : compactExp2547 neighborMidpointP014Input2557 15 =
      (neighborMidpointP014Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP014Input2557 15).2 : ℝ) =
      neighborMidpointP014Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP014Error2557]
  have h := compactExp_error2547 neighborMidpointP014Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP014Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP014Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP014DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP014Factor2557 * embedPair2542 neighborMidpointP014Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP014Factor2557 : ℝ) * neighborMidpointP014Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP014Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP014Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP014BaseError2557
    (embedPair_magnitude2542 neighborMidpointP014Factor2557)

def neighborMidpointP015Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1825525274756649096408550339 : ℚ) /
        472236648286964521369600000000))

def neighborMidpointP015Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP015Factor2557 : RatPair2542 := (((((((((((16558 * 10^40
        + 2312389744865978823479670201871272902544) * 10^40
        + 5517685519887677823979017283457224381402) * 10^40
        + 1318523583651039310399628297918869333183) * 10^40
        + 137345931854119200932223448405762061021) * 10^40
        + 1617467702719628997558183999781725448649) * 10^40
        + 3519201402553569880046343043236166371572) * 10^40
        + 705007157390995491703807527189975865907) * 10^40
        + 3505469491302549003523660992441629515863) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((10531 * 10^40
        + 1777499970215671086182281015806120013471) * 10^40
        + 8118446593215336798766585778858260827) * 10^40
        + 7703690300510109083394723930378981554257) * 10^40
        + 5426606636633454429842347189318220639629)) : ℚ) /
        (((102091464953553012094879387112770791 * 10^40
        + 9107294244454358688711216491840371799732) * 10^40
        + 7121168232762790962406349257557750299516) * 10^40
        + 4599813391326256559765472551309196394496)))

noncomputable def neighborMidpointP015Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP015BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP015Center2557‖ ≤ neighborMidpointP015Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP015Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP015Input2557]
  have hs : compactExp2547 neighborMidpointP015Input2557 15 =
      (neighborMidpointP015Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP015Input2557 15).2 : ℝ) =
      neighborMidpointP015Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP015Error2557]
  have h := compactExp_error2547 neighborMidpointP015Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP015Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP015Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP015DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP015Factor2557 * embedPair2542 neighborMidpointP015Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP015Factor2557 : ℝ) * neighborMidpointP015Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP015Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP015Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP015BaseError2557
    (embedPair_magnitude2542 neighborMidpointP015Factor2557)

def neighborMidpointP016Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((966485135227022568073460733 : ℚ) /
        236118324143482260684800000000))

def neighborMidpointP016Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP016Factor2557 : RatPair2542 := (((((((((((4139 * 10^40
        + 5578097383349153304688960485962767958813) * 10^40
        + 3208972174805501949499844604895349373051) * 10^40
        + 5606874636587436638579835635969000582813) * 10^40
        + 9363199965842200072796918024983824411944) * 10^40
        + 6272650852112882149614190752538368767754) * 10^40
        + 335006545790701864226006440250963049050) * 10^40
        + 7733584049451786490219021579558871568307) * 10^40
        + 9629998744806929309861350467241363451607) : ℚ) /
        (((((((260566680409063573050380848568 * 10^40
        + 7050302601672795530360941244915585260069) * 10^40
        + 1072268598889690887477188049187893560330) * 10^40
        + 3792751256799810167282019863389596816823) * 10^40
        + 8809777307835086687233446023348592036531) * 10^40
        + 1143396435659122730151482196991565824605) * 10^40
        + 7326110300462482701907929920323145773880) * 10^40
        + 1841485031688326333328342240331514773504)),
    (((-((((109 * 10^40
        + 3236430766050688163341440358664778402913) * 10^40
        + 1068467805555312333609550501767942063801) * 10^40
        + 2704135582825048772881155863622586161969) * 10^40
        + 30768078308703876121902466825838499713)) : ℚ) /
        (((1000896715230911883283131246203635 * 10^40
        + 2148110727886807438124619769527846782350) * 10^40
        + 3207070276791792068258885777034879904897) * 10^40
        + 2201958954816924083919269338738325454848)))

noncomputable def neighborMidpointP016Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP016BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP016Center2557‖ ≤ neighborMidpointP016Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP016Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP016Input2557]
  have hs : compactExp2547 neighborMidpointP016Input2557 15 =
      (neighborMidpointP016Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP016Input2557 15).2 : ℝ) =
      neighborMidpointP016Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP016Error2557]
  have h := compactExp_error2547 neighborMidpointP016Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP016Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP016Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP016DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP016Factor2557 * embedPair2542 neighborMidpointP016Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP016Factor2557 : ℝ) * neighborMidpointP016Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP016Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP016Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP016BaseError2557
    (embedPair_magnitude2542 neighborMidpointP016Factor2557)

def neighborMidpointP017Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((2141675457290368202103352599 : ℚ) /
        472236648286964521369600000000))

def neighborMidpointP017Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP017Factor2557 : RatPair2542 := (((((((((((16558 * 10^40
        + 2312389088078534158015917932483838903545) * 10^40
        + 7001382692710255544491579292253915689195) * 10^40
        + 2059802333265897139643872575470906017868) * 10^40
        + 8430197294682606504581962809067902188187) * 10^40
        + 1262962252036688799896348864950449320077) * 10^40
        + 7979751783943435492184076944192080582355) * 10^40
        + 4743119459464835411923585693403574656134) * 10^40
        + 2717477956336946391567987474724766674383) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((4118 * 10^40
        + 3333614371389621111091628348488489378599) * 10^40
        + 5884948262122449270683310401096584850291) * 10^40
        + 2129183731347577197575052137402710061201) * 10^40
        + 4873394656440295171765626133633295790163)) : ℚ) /
        (((34030488317851004031626462370923597 * 10^40
        + 3035764748151452896237072163946790599910) * 10^40
        + 9040389410920930320802116419185916766505) * 10^40
        + 4866604463775418853255157517103065464832)))

noncomputable def neighborMidpointP017Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP017BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP017Center2557‖ ≤ neighborMidpointP017Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP017Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP017Input2557]
  have hs : compactExp2547 neighborMidpointP017Input2557 15 =
      (neighborMidpointP017Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP017Input2557 15).2 : ℝ) =
      neighborMidpointP017Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP017Error2557]
  have h := compactExp_error2547 neighborMidpointP017Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP017Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP017Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP017DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP017Factor2557 * embedPair2542 neighborMidpointP017Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP017Factor2557 : ℝ) * neighborMidpointP017Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP017Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP017Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP017BaseError2557
    (embedPair_magnitude2542 neighborMidpointP017Factor2557)

def neighborMidpointP018Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((555145611856273095972878081 : ℚ) /
        118059162071741130342400000000))

def neighborMidpointP018Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP018Factor2557 : RatPair2542 := (((((((((((1034 * 10^40
        + 8894524306739315227737175131075809094774) * 10^40
        + 6621261822717069065864923887878084346738) * 10^40
        + 80049873008138647876352264435939996793) * 10^40
        + 9356282773773532677225643951355707828921) * 10^40
        + 8471791092589082514985569162181325940300) * 10^40
        + 4633654508068074561388228150616631630874) * 10^40
        + 4880746441199238276635393582518427566667) * 10^40
        + 7847977203142638015620019439358543223263) : ℚ) /
        (((((((65141670102265893262595212142 * 10^40
        + 1762575650418198882590235311228896315017) * 10^40
        + 2768067149722422721869297012296973390082) * 10^40
        + 5948187814199952541820504965847399204205) * 10^40
        + 9702444326958771671808361505837148009132) * 10^40
        + 7785849108914780682537870549247891456151) * 10^40
        + 4331527575115620675476982480080786443470) * 10^40
        + 460371257922081583332085560082878693376)),
    (((-((((3202 * 10^40
        + 5506282670392232556068396706170274769251) * 10^40
        + 141842559371065194465350912379696517966) * 10^40
        + 591195450094635048093182354466881572156) * 10^40
        + 192187289428721427054277115309080474991)) : ℚ) /
        (((25522866238388253023719846778192697 * 10^40
        + 9776823561113589672177804122960092949933) * 10^40
        + 1780292058190697740601587314389437574879) * 10^40
        + 1149953347831564139941368137827299098624)))

noncomputable def neighborMidpointP018Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP018BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP018Center2557‖ ≤ neighborMidpointP018Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP018Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP018Input2557]
  have hs : compactExp2547 neighborMidpointP018Input2557 15 =
      (neighborMidpointP018Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP018Input2557 15).2 : ℝ) =
      neighborMidpointP018Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP018Error2557]
  have h := compactExp_error2547 neighborMidpointP018Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP018Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP018Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP018DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP018Factor2557 * embedPair2542 neighborMidpointP018Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP018Factor2557 : ℝ) * neighborMidpointP018Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP018Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP018Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP018BaseError2557
    (embedPair_magnitude2542 neighborMidpointP018Factor2557)

def neighborMidpointP019Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((118159442675668676717562267 : ℚ) /
        23611832414348226068480000000))

def neighborMidpointP019Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP019Factor2557 : RatPair2542 := (((((((((((1034 * 10^40
        + 8894524285345451587800913572309783753553) * 10^40
        + 4760468255355070533884909053252321917836) * 10^40
        + 9676621714145413708351073934303337134718) * 10^40
        + 5973698174286297636514762928566692210219) * 10^40
        + 2763056611228504292847948845901047739729) * 10^40
        + 4696579967782011311680355878299251656995) * 10^40
        + 2659927421215351592748418300298800260428) * 10^40
        + 7708055007959753273685285825893950579119) : ℚ) /
        (((((((65141670102265893262595212142 * 10^40
        + 1762575650418198882590235311228896315017) * 10^40
        + 2768067149722422721869297012296973390082) * 10^40
        + 5948187814199952541820504965847399204205) * 10^40
        + 9702444326958771671808361505837148009132) * 10^40
        + 7785849108914780682537870549247891456151) * 10^40
        + 4331527575115620675476982480080786443470) * 10^40
        + 460371257922081583332085560082878693376)),
    (((-((((1136 * 10^40
        + 730989458446453209547636918217537739392) * 10^40
        + 626754128417955158302037291508890054148) * 10^40
        + 7665974345220917004069123061705066052739) * 10^40
        + 2400056869584591367212804168263506779395)) : ℚ) /
        (((8507622079462751007906615592730899 * 10^40
        + 3258941187037863224059268040986697649977) * 10^40
        + 7260097352730232580200529104796479191626) * 10^40
        + 3716651115943854713313789379275766366208)))

noncomputable def neighborMidpointP019Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP019BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP019Center2557‖ ≤ neighborMidpointP019Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP019Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP019Input2557]
  have hs : compactExp2547 neighborMidpointP019Input2557 15 =
      (neighborMidpointP019Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP019Input2557 15).2 : ℝ) =
      neighborMidpointP019Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP019Error2557]
  have h := compactExp_error2547 neighborMidpointP019Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP019Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP019Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP019DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP019Factor2557 * embedPair2542 neighborMidpointP019Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP019Factor2557 : ℝ) * neighborMidpointP019Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP019Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP019Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP019BaseError2557
    (embedPair_magnitude2542 neighborMidpointP019Factor2557)

def neighborMidpointP020Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((2518261918355091626130213703 : ℚ) /
        472236648286964521369600000000))

def neighborMidpointP020Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP020Factor2557 : RatPair2542 := (((((((((((16558 * 10^40
        + 2312388169128258452031638596374551987674) * 10^40
        + 9387275409362366436941724902717625273243) * 10^40
        + 4636049122923046961865740150760210215407) * 10^40
        + 8708517226649479638485525796455060907059) * 10^40
        + 7646952627074592508179122327176708181736) * 10^40
        + 7448775125759084217444606706786430263386) * 10^40
        + 1550434720050693474188412192165287264185) * 10^40
        + 927712838778365879853505618094168122415) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((14527 * 10^40
        + 4701205006488003343044177976627787033860) * 10^40
        + 9542308783921127177362851497435369709426) * 10^40
        + 1666092156288869496724553196098676427860) * 10^40
        + 7389868136081125389316761869336920025033)) : ℚ) /
        (((102091464953553012094879387112770791 * 10^40
        + 9107294244454358688711216491840371799732) * 10^40
        + 7121168232762790962406349257557750299516) * 10^40
        + 4599813391326256559765472551309196394496)))

noncomputable def neighborMidpointP020Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP020BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP020Center2557‖ ≤ neighborMidpointP020Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP020Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP020Input2557]
  have hs : compactExp2547 neighborMidpointP020Input2557 15 =
      (neighborMidpointP020Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP020Input2557 15).2 : ℝ) =
      neighborMidpointP020Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP020Error2557]
  have h := compactExp_error2547 neighborMidpointP020Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP020Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP020Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP020DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP020Factor2557 * embedPair2542 neighborMidpointP020Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP020Factor2557 : ℝ) * neighborMidpointP020Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP020Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP020Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP020BaseError2557
    (embedPair_magnitude2542 neighborMidpointP020Factor2557)

def neighborMidpointP021Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((2647676452840152643307498919 : ℚ) /
        472236648286964521369600000000))

def neighborMidpointP021Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP021Factor2557 : RatPair2542 := (((((((((((16558 * 10^40
        + 2312387819038420202541024405725746360263) * 10^40
        + 4676352017276986950716567825542397323961) * 10^40
        + 4704113359857659179612386773161233543586) * 10^40
        + 1808468400200597121454065435192092087871) * 10^40
        + 6394640290124687695290232320525783476451) * 10^40
        + 4747836275368271933797315462377675565308) * 10^40
        + 4192500984720436140987351618358984050339) * 10^40
        + 7696197789680819808358919173065938077423) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((5091 * 10^40
        + 3476310826402256079754881045911672842723) * 10^40
        + 9744453375060173884247919360192058694533) * 10^40
        + 2053186016338112431555826927030377602945) * 10^40
        + 6644945477538500116019126942934059124003)) : ℚ) /
        (((34030488317851004031626462370923597 * 10^40
        + 3035764748151452896237072163946790599910) * 10^40
        + 9040389410920930320802116419185916766505) * 10^40
        + 4866604463775418853255157517103065464832)))

noncomputable def neighborMidpointP021Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP021BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP021Center2557‖ ≤ neighborMidpointP021Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP021Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP021Input2557]
  have hs : compactExp2547 neighborMidpointP021Input2557 15 =
      (neighborMidpointP021Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP021Input2557 15).2 : ℝ) =
      neighborMidpointP021Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP021Error2557]
  have h := compactExp_error2547 neighborMidpointP021Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP021Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP021Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP021DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP021Factor2557 * embedPair2542 neighborMidpointP021Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP021Factor2557 : ℝ) * neighborMidpointP021Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP021Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP021Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP021BaseError2557
    (embedPair_magnitude2542 neighborMidpointP021Factor2557)

def neighborMidpointP022Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((542783116803371403996659021 : ℚ) /
        94447329657392904273920000000))

def neighborMidpointP022Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP022Factor2557 : RatPair2542 := (((((((((((16558 * 10^40
        + 2312387633062968309937141672135034980575) * 10^40
        + 4575697246972013148628355954307116402224) * 10^40
        + 3383488214566807282380689367744228209402) * 10^40
        + 8505465229978206795740669605064100789341) * 10^40
        + 1472826721903385736349740048389334187658) * 10^40
        + 9712743877179110622806506559458956230950) * 10^40
        + 2352889125109095767656287262546002849717) * 10^40
        + 4821692457894848609211984092381479584479) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((15656 * 10^40
        + 1663697471618360340430840329356868913762) * 10^40
        + 1327798168730811159864709548089029045792) * 10^40
        + 3142436834178987915532699005020196952093) * 10^40
        + 1921863490391085423216233054303170396655)) : ℚ) /
        (((102091464953553012094879387112770791 * 10^40
        + 9107294244454358688711216491840371799732) * 10^40
        + 7121168232762790962406349257557750299516) * 10^40
        + 4599813391326256559765472551309196394496)))

noncomputable def neighborMidpointP022Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP022BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP022Center2557‖ ≤ neighborMidpointP022Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP022Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP022Input2557]
  have hs : compactExp2547 neighborMidpointP022Input2557 15 =
      (neighborMidpointP022Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP022Input2557 15).2 : ℝ) =
      neighborMidpointP022Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP022Error2557]
  have h := compactExp_error2547 neighborMidpointP022Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP022Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP022Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP022DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP022Factor2557 * embedPair2542 neighborMidpointP022Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP022Factor2557 : ℝ) * neighborMidpointP022Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP022Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP022Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP022BaseError2557
    (embedPair_magnitude2542 neighborMidpointP022Factor2557)

def neighborMidpointP023Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1452447653947712451580278721 : ℚ) /
        236118324143482260684800000000))

def neighborMidpointP023Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP023Factor2557 : RatPair2542 := (((((((((((4139 * 10^40
        + 5578096767784313444522701107404293387552) * 10^40
        + 3462653566340891266026467036185326700666) * 10^40
        + 8230646928256733203398631588009567159804) * 10^40
        + 88847803078371908613656247263652049846) * 10^40
        + 826000979240512900343685685097591711953) * 10^40
        + 1116957624904239381406175879419161933195) * 10^40
        + 970779951821780237891219296739168532354) * 10^40
        + 302438511171657398242989250759183800415) : ℚ) /
        (((((((260566680409063573050380848568 * 10^40
        + 7050302601672795530360941244915585260069) * 10^40
        + 1072268598889690887477188049187893560330) * 10^40
        + 3792751256799810167282019863389596816823) * 10^40
        + 8809777307835086687233446023348592036531) * 10^40
        + 1143396435659122730151482196991565824605) * 10^40
        + 7326110300462482701907929920323145773880) * 10^40
        + 1841485031688326333328342240331514773504)),
    (((-((((8378 * 10^40
        + 9496797454902350382457758253862101775145) * 10^40
        + 3006985796924949258771812318510720436811) * 10^40
        + 4870556706135586012870799950395002818918) * 10^40
        + 5198289282713258347379612847520105466031)) : ℚ) /
        (((51045732476776506047439693556385395 * 10^40
        + 9553647122227179344355608245920185899866) * 10^40
        + 3560584116381395481203174628778875149758) * 10^40
        + 2299906695663128279882736275654598197248)))

noncomputable def neighborMidpointP023Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP023BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP023Center2557‖ ≤ neighborMidpointP023Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP023Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP023Input2557]
  have hs : compactExp2547 neighborMidpointP023Input2557 15 =
      (neighborMidpointP023Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP023Input2557 15).2 : ℝ) =
      neighborMidpointP023Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP023Error2557]
  have h := compactExp_error2547 neighborMidpointP023Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP023Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP023Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP023DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP023Factor2557 * embedPair2542 neighborMidpointP023Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP023Factor2557 : ℝ) * neighborMidpointP023Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP023Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP023Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP023BaseError2557
    (embedPair_magnitude2542 neighborMidpointP023Factor2557)

def neighborMidpointP024Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1496330927553297167442947039 : ℚ) /
        236118324143482260684800000000))

def neighborMidpointP024Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP024Factor2557 : RatPair2542 := (((((((((((4139 * 10^40
        + 5578096700021970956565614232236773986087) * 10^40
        + 3000335400771583491108441910239049277053) * 10^40
        + 8916285981356749517426512518171889750351) * 10^40
        + 3167324076829558122944099215771180665745) * 10^40
        + 385843063142490730465852342927521008208) * 10^40
        + 1856963468047342537777703964059912887520) * 10^40
        + 7952660828055276249852635737331679613896) * 10^40
        + 1909818820987168446717246526120057951135) : ℚ) /
        (((((((260566680409063573050380848568 * 10^40
        + 7050302601672795530360941244915585260069) * 10^40
        + 1072268598889690887477188049187893560330) * 10^40
        + 3792751256799810167282019863389596816823) * 10^40
        + 8809777307835086687233446023348592036531) * 10^40
        + 1143396435659122730151482196991565824605) * 10^40
        + 7326110300462482701907929920323145773880) * 10^40
        + 1841485031688326333328342240331514773504)),
    (((-((((8632 * 10^40
        + 1056129898388004954209447751043958885026) * 10^40
        + 9102574087039006190296774262708836682746) * 10^40
        + 7863164841291412601192159936955636625872) * 10^40
        + 1839959672619548559984020555819064273329)) : ℚ) /
        (((51045732476776506047439693556385395 * 10^40
        + 9553647122227179344355608245920185899866) * 10^40
        + 3560584116381395481203174628778875149758) * 10^40
        + 2299906695663128279882736275654598197248)))

noncomputable def neighborMidpointP024Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP024BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP024Center2557‖ ≤ neighborMidpointP024Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP024Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP024Input2557]
  have hs : compactExp2547 neighborMidpointP024Input2557 15 =
      (neighborMidpointP024Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP024Input2557 15).2 : ℝ) =
      neighborMidpointP024Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP024Error2557]
  have h := compactExp_error2547 neighborMidpointP024Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP024Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP024Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP024DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP024Factor2557 * embedPair2542 neighborMidpointP024Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP024Factor2557 : ℝ) * neighborMidpointP024Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP024Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP024Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP024BaseError2557
    (embedPair_magnitude2542 neighborMidpointP024Factor2557)

def neighborMidpointP025Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((48479765632462230989059221 : ℚ) /
        7378697629483820646400000000))

def neighborMidpointP025Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP025Factor2557 : RatPair2542 := (((((((((((4 * 10^40
        + 425369234972862047273843940010656910901) * 10^40
        + 7669072895367285453859333328326089817374) * 10^40
        + 3962023963050748795412398096183885581562) * 10^40
        + 2299568745405271705024192655034227676194) * 10^40
        + 6605811360195841589315462040754652778303) * 10^40
        + 7488921545209641811300050583359818861308) * 10^40
        + 5547850232904092247682612845283909191128) * 10^40
        + 2667727482413349738622517888079611892263) : ℚ) /
        (((((((254459648836976145557012547 * 10^40
        + 4303760061134446089385118106684487876230) * 10^40
        + 5362375262303603213757301941454285052305) * 10^40
        + 101360108649218564616486347522841403141) * 10^40
        + 4295712673152182701843001412132176359410) * 10^40
        + 6749163473081698362041163556832999576000) * 10^40
        + 5915357529590295393263581962812815572044) * 10^40
        + 8048673325226258131184890959219073744896)),
    (((-((((93 * 10^40
        + 2241322928666036444055891767758285079831) * 10^40
        + 6461588555084280578726211288548527870716) * 10^40
        + 4801454767822463040997177973446240582051) * 10^40
        + 4670895729783139523034045999344101367177)) : ℚ) /
        (((531726379966421937994163474545681 * 10^40
        + 2078683824189866451503704252561668603123) * 10^40
        + 6078756084545639536262533069049779949476) * 10^40
        + 6482290694746490919582111836204735397888)))

noncomputable def neighborMidpointP025Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP025BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP025Center2557‖ ≤ neighborMidpointP025Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP025Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP025Input2557]
  have hs : compactExp2547 neighborMidpointP025Input2557 15 =
      (neighborMidpointP025Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP025Input2557 15).2 : ℝ) =
      neighborMidpointP025Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP025Error2557]
  have h := compactExp_error2547 neighborMidpointP025Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP025Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP025Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP025DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP025Factor2557 * embedPair2542 neighborMidpointP025Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP025Factor2557 : ℝ) * neighborMidpointP025Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP025Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP025Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP025BaseError2557
    (embedPair_magnitude2542 neighborMidpointP025Factor2557)

def neighborMidpointP026Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((100473894490366930888172769 : ℚ) /
        14757395258967641292800000000))

def neighborMidpointP026Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP026Factor2557 : RatPair2542 := (((((((((((16 * 10^40
        + 1701476939528107063890280270689433033437) * 10^40
        + 7306564916453778042056065972101490971558) * 10^40
        + 3010528403728213845468593280484070454852) * 10^40
        + 7865397619267267518963371341204763859672) * 10^40
        + 4736225098662957084888050840003768681798) * 10^40
        + 2502410733542779736966428336892736827518) * 10^40
        + 4173299286108544774949239289690659790910) * 10^40
        + 9800817675813764123497000939313712874015) : ℚ) /
        (((((((1017838595347904582228050189 * 10^40
        + 7215040244537784357540472426737951504922) * 10^40
        + 1449501049214412855029207765817140209220) * 10^40
        + 405440434596874258465945390091365612565) * 10^40
        + 7182850692608730807372005648528705437642) * 10^40
        + 6996653892326793448164654227331998304002) * 10^40
        + 3661430118361181573054327851251262288179) * 10^40
        + 2194693300905032524739563836876294979584)),
    (((-((((193 * 10^40
        + 2062069557032513613884841751938505638873) * 10^40
        + 3341982249394008767589721852259907029582) * 10^40
        + 1151129049167089014800128162170092417255) * 10^40
        + 8485530190417671646954041602430409656453)) : ℚ) /
        (((1063452759932843875988326949091362 * 10^40
        + 4157367648379732903007408505123337206247) * 10^40
        + 2157512169091279072525066138099559898953) * 10^40
        + 2964581389492981839164223672409470795776)))

noncomputable def neighborMidpointP026Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP026BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP026Center2557‖ ≤ neighborMidpointP026Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP026Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP026Input2557]
  have hs : compactExp2547 neighborMidpointP026Input2557 15 =
      (neighborMidpointP026Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP026Input2557 15).2 : ℝ) =
      neighborMidpointP026Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP026Error2557]
  have h := compactExp_error2547 neighborMidpointP026Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP026Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP026Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP026DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP026Factor2557 * embedPair2542 neighborMidpointP026Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP026Factor2557 : ℝ) * neighborMidpointP026Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP026Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP026Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP026BaseError2557
    (embedPair_magnitude2542 neighborMidpointP026Factor2557)

def neighborMidpointP027Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((211090470366057865778518799 : ℚ) /
        29514790517935282585600000000))

def neighborMidpointP027Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP027Factor2557 : RatPair2542 := (((((((((((64 * 10^40
        + 6805907755923973578971736441683432860303) * 10^40
        + 6537759187167949851852721781875898251792) * 10^40
        + 5778698783449447117631996753447194333611) * 10^40
        + 3732258943812172915133346574406225862459) * 10^40
        + 5019888611717493923789257209588567513173) * 10^40
        + 7802265419120626689112826052313758584066) * 10^40
        + 2273267811144790612698973632987373378074) * 10^40
        + 9038623830438408455312479308313698500863) : ℚ) /
        (((((((4071354381391618328912200758 * 10^40
        + 8860160978151137430161889706951806019688) * 10^40
        + 5798004196857651420116831063268560836880) * 10^40
        + 1621761738387497033863781560365462450262) * 10^40
        + 8731402770434923229488022594114821750570) * 10^40
        + 7986615569307173792658616909327993216009) * 10^40
        + 4645720473444726292217311405005049152716) * 10^40
        + 8778773203620130098958255347505179918336)),
    (((-((((1217 * 10^40
        + 7488285128095584791339429405847333471097) * 10^40
        + 4284859841436551918171937835328710060953) * 10^40
        + 1798391370514563367671800506404614343032) * 10^40
        + 7854976656309839198155297925880432418689)) : ℚ) /
        (((6380716559597063255929961694548174 * 10^40
        + 4944205890278397418044451030740023237483) * 10^40
        + 2945073014547674435150396828597359393719) * 10^40
        + 7787488336957891034985342034456824774656)))

noncomputable def neighborMidpointP027Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP027BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP027Center2557‖ ≤ neighborMidpointP027Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP027Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP027Input2557]
  have hs : compactExp2547 neighborMidpointP027Input2557 15 =
      (neighborMidpointP027Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP027Input2557 15).2 : ℝ) =
      neighborMidpointP027Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP027Error2557]
  have h := compactExp_error2547 neighborMidpointP027Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP027Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP027Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP027DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP027Factor2557 * embedPair2542 neighborMidpointP027Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP027Factor2557 : ℝ) * neighborMidpointP027Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP027Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP027Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP027BaseError2557
    (embedPair_magnitude2542 neighborMidpointP027Factor2557)

def neighborMidpointP028Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((860424389879986254866272499 : ℚ) /
        118059162071741130342400000000))

def neighborMidpointP028Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP028Factor2557 : RatPair2542 := (((((((((((1034 * 10^40
        + 8894524080444191867059769888357347672611) * 10^40
        + 7810389649567059122223715653927853354255) * 10^40
        + 7735908466736603312956531382685064638253) * 10^40
        + 5192856329880188125908588767409680191968) * 10^40
        + 7926609250640195673047015583704593416215) * 10^40
        + 2110124175485288818157114067603919116646) * 10^40
        + 3639841170631938748606370260437776548148) * 10^40
        + 311589331663942578131156946205378260023) : ℚ) /
        (((((((65141670102265893262595212142 * 10^40
        + 1762575650418198882590235311228896315017) * 10^40
        + 2768067149722422721869297012296973390082) * 10^40
        + 5948187814199952541820504965847399204205) * 10^40
        + 9702444326958771671808361505837148009132) * 10^40
        + 7785849108914780682537870549247891456151) * 10^40
        + 4331527575115620675476982480080786443470) * 10^40
        + 460371257922081583332085560082878693376)),
    (((-((((4963 * 10^40
        + 6574828944968920416557532658093358421357) * 10^40
        + 9893800852543834678947537773766922109287) * 10^40
        + 3630893075448794933477522664876760407780) * 10^40
        + 2453507540778559837118269461568974679389)) : ℚ) /
        (((25522866238388253023719846778192697 * 10^40
        + 9776823561113589672177804122960092949933) * 10^40
        + 1780292058190697740601587314389437574879) * 10^40
        + 1149953347831564139941368137827299098624)))

noncomputable def neighborMidpointP028Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP028BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP028Center2557‖ ≤ neighborMidpointP028Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP028Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP028Input2557]
  have hs : compactExp2547 neighborMidpointP028Input2557 15 =
      (neighborMidpointP028Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP028Input2557 15).2 : ℝ) =
      neighborMidpointP028Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP028Error2557]
  have h := compactExp_error2547 neighborMidpointP028Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP028Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP028Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP028DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP028Factor2557 * embedPair2542 neighborMidpointP028Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP028Factor2557 : ℝ) * neighborMidpointP028Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP028Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP028Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP028BaseError2557
    (embedPair_magnitude2542 neighborMidpointP028Factor2557)

def neighborMidpointP029Input2557 : RatPair2542 := ((((-((770987 * 10^40
        + 9241558908623557918814552242112228396500) * 10^40
        + 9922662915450605926490899412567961088519)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((884878527656961808081806583 : ℚ) /
        118059162071741130342400000000))

def neighborMidpointP029Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborMidpointP029Factor2557 : RatPair2542 := (((((((((((1034 * 10^40
        + 8894524058094558705159568104158363614929) * 10^40
        + 5449241056264822973120433742390176103873) * 10^40
        + 2458418067634047662739233670915770931967) * 10^40
        + 1591840097084779784607025510319874864176) * 10^40
        + 3653852044331410699548332319081273735379) * 10^40
        + 1148737417304078774679104091023605966477) * 10^40
        + 9599627909244550301593940577246433781638) * 10^40
        + 1824426086653930620786090526519150040975) : ℚ) /
        (((((((65141670102265893262595212142 * 10^40
        + 1762575650418198882590235311228896315017) * 10^40
        + 2768067149722422721869297012296973390082) * 10^40
        + 5948187814199952541820504965847399204205) * 10^40
        + 9702444326958771671808361505837148009132) * 10^40
        + 7785849108914780682537870549247891456151) * 10^40
        + 4331527575115620675476982480080786443470) * 10^40
        + 460371257922081583332085560082878693376)),
    (((-((((5104 * 10^40
        + 7296856261608627393360550182129436828149) * 10^40
        + 3113992465546273683457227673646354240581) * 10^40
        + 7714749138483041336212350376126147285393) * 10^40
        + 5042986729303159599075578784035982674713)) : ℚ) /
        (((25522866238388253023719846778192697 * 10^40
        + 9776823561113589672177804122960092949933) * 10^40
        + 1780292058190697740601587314389437574879) * 10^40
        + 1149953347831564139941368137827299098624)))

noncomputable def neighborMidpointP029Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborMidpointP029BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP029Center2557‖ ≤ neighborMidpointP029Error2557 := by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborMidpointP029Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborMidpointP029Input2557]
  have hs : compactExp2547 neighborMidpointP029Input2557 15 =
      (neighborMidpointP029Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborMidpointP029Input2557 15).2 : ℝ) =
      neighborMidpointP029Error2557 :=
      by
    rw [hs]
    norm_num [neighborMidpointP029Error2557]
  have h := compactExp_error2547 neighborMidpointP029Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      neighborMidpointPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborMidpointP029Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborMidpointPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborMidpointP029Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborMidpointP029DerivativeError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP029Factor2557 * embedPair2542 neighborMidpointP029Center2557‖
          ≤
        (pairMagnitude2542 neighborMidpointP029Factor2557 : ℝ) * neighborMidpointP029Error2557 :=
            by
  have hx : |neighborMidpointPosition2557| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [neighborMidpointPosition2557, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) neighborMidpointPosition2557 = embedPair2542
          neighborMidpointP029Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborMidpointPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborMidpointP029Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborMidpointP029BaseError2557
    (embedPair_magnitude2542 neighborMidpointP029Factor2557)

theorem neighborMidpointGrid2557 :
    -stripRadius2303 + ((5403 : ℝ) /
        2) * (2 * stripRadius2303 / 10240) =
      neighborMidpointPosition2557 := by
  norm_num [stripRadius2303, neighborMidpointPosition2557]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.neighborMidpointP000DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP001DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP002DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP003DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP004DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP005DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP006DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP007DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP008DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP009DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP010DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP011DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP012DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP013DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP014DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP015DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP016DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP017DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP018DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP019DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP020DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP021DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP022DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP023DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP024DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP025DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP026DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP027DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP028DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointP029DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborMidpointGrid2557
