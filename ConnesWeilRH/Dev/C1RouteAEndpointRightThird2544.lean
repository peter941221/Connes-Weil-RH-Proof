import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def endpointRightPosition2544 : ℝ := ((21037056321 : ℝ) /
        51200000000)

def endpointRightP000Input2544 : RatPair2542 :=
  ((((-((784572 * 10^40
        + 6811905081266710236408700291277958317180) * 10^40
        + 9730042723390700240474632798007040790639)) : ℚ) /
        ((1641590 * 10^40
        + 7299889921227587901041435668166425430412) * 10^40
        + 5748789340774106302562410437017600000000)),
    (((-116214821441625035538111309) : ℚ) /
        461168601842738790400000000))

def endpointRightP000Center2544 : RatPair2542 :=
  ((((-30085212616927361) : ℚ) /
        633825300114114700748351602688),
    ((13438227082181753 : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointRightP000Error2544 : ℝ := ((40167273250971 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP000Factor2544 : RatPair2542 :=
  ((((((((((((((1572407543773952213923824481342439 * 10^40
        + 5444075535408437681039989817798672467725) * 10^40
        + 5043260027961402402237611989139602016729) * 10^40
        + 3221955651894096248696942711264995589935) * 10^40
        + 5472102906399787115066582941998946669482) * 10^40
        + 4388700990751164501750516810643259115856) * 10^40
        + 9433540062590857385778427777776451750715) * 10^40
        + 6443451007560640463349172824647398037160) * 10^40
        + 3466231718508133790866641298490037760561) * 10^40
        + 4496847067506404013266881305197578875642) * 10^40
        + 1995837652516698523744695025833925088959) * 10^40
        + 4815661498908787195187708059819213499493) : ℚ) /
        (((((((((((97849666610260431086186438705 * 10^40
        + 3152351900434273351861729737784210913822) * 10^40
        + 2735628484770647946704590654917824422913) * 10^40
        + 6648911915454763378680985026687447833196) * 10^40
        + 1364335162905765751087626605484332447783) * 10^40
        + 6190585868498746400614533975873308687122) * 10^40
        + 5336675912315991087538102920637923740128) * 10^40
        + 7787221457693062770742990959722968380332) * 10^40
        + 165262878969057966087738654534175122151) * 10^40
        + 4394588098550318674350561037736511834423) * 10^40
        + 6940095466727065616374738654879653699710) * 10^40
        + 6021046149792871325546342864291090137088)),
    ((((((((((661979939262700196014 * 10^40
        + 7369061168622537827388776511528985461534) * 10^40
        + 9183856166622745421753834253678568806027) * 10^40
        + 7199423398842952904659587453361189260953) * 10^40
        + 935123553664293031518664603168423136525) * 10^40
        + 2820473562836840310649828832310528669773) * 10^40
        + 7463367684783200495455105659437676322751) * 10^40
        + 157220416867250022054389665439937187385) * 10^40
        + 7930717642330261700462550482731857011157) : ℚ) /
        ((((((((10974108004261534 * 10^40
        + 26343976501527727601616216202337224151) * 10^40
        + 7708329751480295757865838016755866395358) * 10^40
        + 4626247846672210190930205538533422196364) * 10^40
        + 7725306252061502181106360184033446181442) * 10^40
        + 7294744109536704405669910819317681135468) * 10^40
        + 1797886727174386711515417900162977561552) * 10^40
        + 1595316987362340492020297611572505794254) * 10^40
        + 5594119328822331609388727333296560668672)))

theorem endpointRightP000BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP000Center2544‖ ≤ endpointRightP000Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP000Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP000Input2544]
  have hc : (compactExp2542 endpointRightP000Input2544 6).1 = endpointRightP000Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP000Input2544 6).2 : ℝ) = endpointRightP000Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP000Input2544 6).2 =
        ((40167273250971 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP000Error2544]
  have h := compactExp_error2542 endpointRightP000Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP000Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP000Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP000DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP000Factor2544 * embedPair2542 endpointRightP000Center2544‖ ≤
      (pairMagnitude2542 endpointRightP000Factor2544 : ℝ) * endpointRightP000Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨0, by omega⟩)
      (storedWidth ⟨0, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP000Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP000Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨0, by omega⟩) (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP000BaseError2544
    (embedPair_magnitude2542 endpointRightP000Factor2544)

def endpointRightP001Input2544 : RatPair2542 :=
  ((((-((37 * 10^40
        + 2210872843279052800156387807736435194328) * 10^40
        + 6585212332736148238238202828482993853351)) : ℚ) /
        ((78 * 10^40
        + 7669206969983457920426651219472560969960) * 10^40
        + 6359156146779929224210681488998400000000)),
    (((-116214821441625035538111309) : ℚ) /
        461168601842738790400000000))

def endpointRightP001Center2544 : RatPair2542 :=
  ((((-42470726113974161) : ℚ) /
        633825300114114700748351602688),
    ((37940982444219857 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointRightP001Error2544 : ℝ := ((55510111139349 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP001Factor2544 : RatPair2542 :=
  ((((((((((((((9494961 * 10^40
        + 5260022851028025650924202901866859067706) * 10^40
        + 902657235537888874060275018444831957173) * 10^40
        + 2026973315811116600927489755971652118313) * 10^40
        + 1677279768690014020474580199732614443803) * 10^40
        + 3788406412240276463058392424527448559323) * 10^40
        + 9885633747953660445889980822335551329353) * 10^40
        + 4005914440852291003909599651016250833151) * 10^40
        + 1902397221687162715809663260406426109371) * 10^40
        + 800624018588147605576408283236202639659) * 10^40
        + 3147869955916153253265139292800305830565) * 10^40
        + 6339129532412994045381229393901651832213) : ℚ) /
        (((((((((((1194 * 10^40
        + 794099078955839090616851117144212553915) * 10^40
        + 6675648029225547193870308200583374650245) * 10^40
        + 2655544178785359927189201393889918161227) * 10^40
        + 8669872800993615784157118507997661949075) * 10^40
        + 9768546377773645358061208587245975576249) * 10^40
        + 190861922885626916751679719276985148881) * 10^40
        + 9950097213465206264051234459431063275895) * 10^40
        + 5989649647388764836115656125987622554259) * 10^40
        + 3387537332906178827816991243686583972195) * 10^40
        + 288294810346684875225055350456079509990) * 10^40
        + 9054008727322606449936721584801718468608)),
    ((((((((((3536 * 10^40
        + 8995507536895204428295534004181166360618) * 10^40
        + 3523318339779143207673543183944985666386) * 10^40
        + 5990280242257790276492119435991223478309) * 10^40
        + 7526779669565203126175468387009424149719) * 10^40
        + 3519044689059641203022080104215272787555) * 10^40
        + 1078102022244186534225725372631670505314) * 10^40
        + 5455206383260854174209647241367849413161) * 10^40
        + 9648886013278693921452242571316063301877) : ℚ) /
        (((((((581681345669742492879640478931820560304 * 10^40
        + 4329575226030047772295022831247707185743) * 10^40
        + 2606925378650348604679474123144773482765) * 10^40
        + 1166386758508370067736426631888846870960) * 10^40
        + 5165845726585722890303067449014875581986) * 10^40
        + 6394844811552813771885964089893950296831) * 10^40
        + 5380512753006325179859484884374797382294) * 10^40
        + 4839092947471049597855255886516602273792)))

theorem endpointRightP001BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP001Center2544‖ ≤ endpointRightP001Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP001Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP001Input2544]
  have hc : (compactExp2542 endpointRightP001Input2544 6).1 = endpointRightP001Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP001Input2544 6).2 : ℝ) = endpointRightP001Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP001Input2544 6).2 =
        ((55510111139349 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP001Error2544]
  have h := compactExp_error2542 endpointRightP001Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP001Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP001Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP001DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP001Factor2544 * embedPair2542 endpointRightP001Center2544‖ ≤
      (pairMagnitude2542 endpointRightP001Factor2544 : ℝ) * endpointRightP001Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP001Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP001Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP001BaseError2544
    (embedPair_magnitude2542 endpointRightP001Factor2544)

def endpointRightP002Input2544 : RatPair2542 :=
  ((((-((972 * 10^40
        + 4650254589744882533607086103630523782057) * 10^40
        + 449145224629076769356490527792110637991)) : ℚ) /
        ((2069 * 10^40
        + 9275360438959695706130539090735253425699) * 10^40
        + 327048463036252587370903823974400000000)),
    ((116214821441625035538111309 : ℚ) /
        461168601842738790400000000))

def endpointRightP002Center2544 : RatPair2542 :=
  ((((-101228313912808433) : ℚ) /
        1267650600228229401496703205376),
    (((-11303967557315125) : ℚ) /
        316912650057057350374175801344))

noncomputable def endpointRightP002Error2544 : ℝ := ((65558198693657 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP002Factor2544 : RatPair2542 :=
  ((((((((((((((1531881288416013 * 10^40
        + 2650332644564511186136464076018063515672) * 10^40
        + 9565052894625375163362870356711892714307) * 10^40
        + 8698898986432649397219735849460425526321) * 10^40
        + 9630684056180419847319840620186275251133) * 10^40
        + 4940726008328513844032882490783462496656) * 10^40
        + 4607378785633002590943868669952080286146) * 10^40
        + 8382980152913591828586269211923586432148) * 10^40
        + 9418670194162930561480634559604725849212) * 10^40
        + 822057799865925284071462394456479503368) * 10^40
        + 3092912158574157154443707445888354249009) * 10^40
        + 5226774964075396369365784081172053962133) : ℚ) /
        (((((((((((393279089790 * 10^40
        + 3287298295456763240306771988103225754277) * 10^40
        + 7230692381857067307839796462601979473446) * 10^40
        + 3677968324503920890452459895552425897020) * 10^40
        + 649384554069846973317663145061915949249) * 10^40
        + 9856550241763586501475832544306072467466) * 10^40
        + 747293183950310614202875675924188539472) * 10^40
        + 2465472083411441922613882797440754834450) * 10^40
        + 3071682827575333598604025481191814405830) * 10^40
        + 3303780088880931047974324080260177936731) * 10^40
        + 6778016713921759544504117020628408932633) * 10^40
        + 9723182026546714766587280747919025635328)),
    (((-((((((((1686502465 * 10^40
        + 9086253329432695306204139326833065287937) * 10^40
        + 3833150787608267952121611475187679092226) * 10^40
        + 2806707414920224892152405375176446275793) * 10^40
        + 1442781822738695379859918755895183978183) * 10^40
        + 1520931140592623871799502067890553064103) * 10^40
        + 2705151600563125586952237393120657214060) * 10^40
        + 4318749802610301181159538434582960230563) * 10^40
        + 4656763949008318950157996824486710014197)) : ℚ) /
        ((((((((27741 * 10^40
        + 5187803846634727757153581577659390123966) * 10^40
        + 8606281502304333286478669748142171009759) * 10^40
        + 4852847221619422280643663776163555061525) * 10^40
        + 7782024989414931882099245033797744558718) * 10^40
        + 3996186011277045880817673473743437429111) * 10^40
        + 3626748104782402149645744199039448426807) * 10^40
        + 443482139793926239060276372858008332293) * 10^40
        + 2461643237659073737908978752046615232512)))

theorem endpointRightP002BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP002Center2544‖ ≤ endpointRightP002Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP002Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP002Input2544]
  have hc : (compactExp2542 endpointRightP002Input2544 6).1 = endpointRightP002Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP002Input2544 6).2 : ℝ) = endpointRightP002Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP002Input2544 6).2 =
        ((65558198693657 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP002Error2544]
  have h := compactExp_error2542 endpointRightP002Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP002Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP002Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP002DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP002Factor2544 * embedPair2542 endpointRightP002Center2544‖ ≤
      (pairMagnitude2542 endpointRightP002Factor2544 : ℝ) * endpointRightP002Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP002Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP002Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP002BaseError2544
    (embedPair_magnitude2542 endpointRightP002Factor2544)

def endpointRightP003Input2544 : RatPair2542 :=
  ((((-((3467731 * 10^40
        + 8511828977644856382439885982238229303076) * 10^40
        + 4074901543573001235591471814120322040639)) : ℚ) /
        ((7405132 * 10^40
        + 3596549542648098448253759473411694208953) * 10^40
        + 3511265881635850302562410437017600000000)),
    ((116214821441625035538111309 : ℚ) /
        461168601842738790400000000))

def endpointRightP003Center2544 : RatPair2542 :=
  ((((-55780667598372603) : ℚ) /
        633825300114114700748351602688),
    (((-24915671613398283) : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointRightP003Error2544 : ℝ := ((17979927593879 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

def endpointRightP003Factor2544 : RatPair2542 :=
  ((((((((((((((1377199672241953390273095166381860091 * 10^40
        + 5996205432328777664784262224156710363492) * 10^40
        + 568398477179001635285506020483273181663) * 10^40
        + 9594401311630815644818494930055638400028) * 10^40
        + 3232779280031795193114448644500640625631) * 10^40
        + 2364774221455117264115762236207705437755) * 10^40
        + 8862719442727229963499461626928869859754) * 10^40
        + 7402884396253331676445970343274414646610) * 10^40
        + 9901718432035328492777100474179606864072) * 10^40
        + 2073786809146256567705995063902290023799) * 10^40
        + 1699524482341467923534385142718964518806) * 10^40
        + 4227553518970356139364214021733275999493) : ℚ) /
        (((((((((((824455002481478851790382456410224 * 10^40
        + 2531398280574424636514418657544355746409) * 10^40
        + 5173263792764250039082084933088317096968) * 10^40
        + 8077392698975058865296346816044362069208) * 10^40
        + 500150320135161369865742546786344720736) * 10^40
        + 7014025690486949092186856667327842658323) * 10^40
        + 4283387907653213634064096814145229137898) * 10^40
        + 3815184446205928315555373753326391890539) * 10^40
        + 2017723363176002390274385190578992275144) * 10^40
        + 9545910887587871712206805092042581765157) * 10^40
        + 6535125395568425203610980092341300502161) * 10^40
        + 6219209698194949062178662864291090137088)),
    (((-((((((((275893323873136928388214 * 10^40
        + 8741474407503557039378678103006168348439) * 10^40
        + 8666858698204782928873620456638599111183) * 10^40
        + 2026940865925806052840329112388519035158) * 10^40
        + 1845374794440057918708283980885264418100) * 10^40
        + 2005555437044838365072602196304536843569) * 10^40
        + 428690570110607008830922218073638893333) * 10^40
        + 3940609438253461975995279155049411473453) * 10^40
        + 2073548886932224772983756957341232011157)) : ℚ) /
        ((((((((4544027680051917677 * 10^40
        + 3945286293761104618266696297352473207838) * 10^40
        + 198730604686282202077827891474051747837) * 10^40
        + 9578775343606333413796428507437582960085) * 10^40
        + 120989190156972420164202936886635750393) * 10^40
        + 766492388082869085744927777978152349987) * 10^40
        + 9773689882467230872051365657006940035272) * 10^40
        + 1678638491811066657703257457405954673192) * 10^40
        + 4908644106538619639371447333296560668672)))

theorem endpointRightP003BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP003Center2544‖ ≤ endpointRightP003Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP003Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP003Input2544]
  have hc : (compactExp2542 endpointRightP003Input2544 6).1 = endpointRightP003Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP003Input2544 6).2 : ℝ) = endpointRightP003Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP003Input2544 6).2 =
        ((17979927593879 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [endpointRightP003Error2544]
  have h := compactExp_error2542 endpointRightP003Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP003Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP003Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP003DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP003Factor2544 * embedPair2542 endpointRightP003Center2544‖ ≤
      (pairMagnitude2542 endpointRightP003Factor2544 : ℝ) * endpointRightP003Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP003Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP003Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP003BaseError2544
    (embedPair_magnitude2542 endpointRightP003Factor2544)

def endpointRightP004Input2544 : RatPair2542 :=
  ((((-((2231 * 10^40
        + 3375535476931673290534537883071344715547) * 10^40
        + 6383006085386817160530046997518673137991)) : ℚ) /
        ((4774 * 10^40
        + 400252417480049124655959709246057629116) * 10^40
        + 4311969699402172587370903823974400000000)),
    (((-116214821441625035538111309) : ℚ) /
        461168601842738790400000000))

def endpointRightP004Center2544 : RatPair2542 :=
  ((((-118159590386044049) : ℚ) /
        1267650600228229401496703205376),
    ((26389300081792299 : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointRightP004Error2544 : ℝ := ((75977044915021 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP004Factor2544 : RatPair2542 :=
  ((((((((((((((21497793578730620 * 10^40
        + 7388495363832642212525553596018261680788) * 10^40
        + 6816999894081561056432379453055723544317) * 10^40
        + 4454510976270793143771151440491592910463) * 10^40
        + 8326319036511197388419912128921073076677) * 10^40
        + 7816137805895327567950400870046781153834) * 10^40
        + 6455726329027652696867558830145947595006) * 10^40
        + 7483368576602088360320894021089086016827) * 10^40
        + 2513814350437707165837329058026658566604) * 10^40
        + 7496481963495554766392899203730238583565) * 10^40
        + 7090843885090372429223792237927030663354) * 10^40
        + 5757646334632053684164382567500178962133) : ℚ) /
        (((((((((((59195179118994 * 10^40
        + 5487762931252617626511088023350538880701) * 10^40
        + 535743121574925174057788522883383361957) * 10^40
        + 630923578932538940596267344179041871591) * 10^40
        + 6156732236118171064788005788090601765877) * 10^40
        + 1393229984863927075161598743650883468230) * 10^40
        + 7622342238716221746799085972602178629312) * 10^40
        + 7482149584578034420579006985125241027052) * 10^40
        + 9749497040973161694469778299185058219426) * 10^40
        + 2444360803183981047277112178322199094630) * 10^40
        + 9901181092807130449986790388117613593362) * 10^40
        + 9466283803793243132769680747919025635328)),
    ((((((((((47605454163 * 10^40
        + 6879058741317587818889743806302447227803) * 10^40
        + 3666541698745596593063322892434969025869) * 10^40
        + 5120669953697242958230558576863935539754) * 10^40
        + 3739556964493717357085626633233582395146) * 10^40
        + 8502215253477815751334118528660014362909) * 10^40
        + 8605433989948726968612092217526442546007) * 10^40
        + 5142113938767937772728687500741689737111) * 10^40
        + 8709535649194896534756716648705460014197) : ℚ) /
        ((((((((784971 * 10^40
        + 5003213888598965320215483199582724431500) * 10^40
        + 8314857906455864655287792970613733636317) * 10^40
        + 4076736412063803489909937603871190373234) * 10^40
        + 6830236321983158153039493131278152435032) * 10^40
        + 4865044819442076836845584141238646271716) * 10^40
        + 8741485852367249530410192656053151823138) * 10^40
        + 2636104614135820526767660801487835342979) * 10^40
        + 9038677325144477195035378752046615232512)))

theorem endpointRightP004BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP004Center2544‖ ≤ endpointRightP004Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP004Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP004Input2544]
  have hc : (compactExp2542 endpointRightP004Input2544 6).1 = endpointRightP004Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP004Input2544 6).2 : ℝ) = endpointRightP004Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP004Input2544 6).2 =
        ((75977044915021 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP004Error2544]
  have h := compactExp_error2542 endpointRightP004Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP004Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP004Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP004DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP004Factor2544 * embedPair2542 endpointRightP004Center2544‖ ≤
      (pairMagnitude2542 endpointRightP004Factor2544 : ℝ) * endpointRightP004Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP004Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP004Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP004BaseError2544
    (embedPair_magnitude2542 endpointRightP004Factor2544)

def endpointRightP005Input2544 : RatPair2542 :=
  ((((-((105958 * 10^40
        + 1078245870052624652491804785029218162688) * 10^40
        + 7127909769652323698197879090457813560071)) : ℚ) /
        ((111373 * 10^40
        + 2246050746979823078836670277118175355916) * 10^40
        + 7617028968325063683475689468723200000000)),
    ((0 : ℚ) /
        1))

def endpointRightP005Center2544 : RatPair2542 :=
  (((76083006255940955 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def endpointRightP005Error2544 : ℝ := ((9130344602477 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP005Factor2544 : RatPair2542 :=
  (((((((((((((54798763452387582379717337709282184993 * 10^40
        + 6189234747538367963588551130220476340384) * 10^40
        + 7516487421148097699448620801834277341817) * 10^40
        + 9854964536314746025680378376592987678124) * 10^40
        + 6340076848493355243999998147822091848956) * 10^40
        + 6857035550128181094416446128908353754072) * 10^40
        + 1456438839546531976157760970030418105178) * 10^40
        + 867361963066895549181446822747103604512) * 10^40
        + 1771669858605012595792571822359779119236) * 10^40
        + 928996887769204121855076925369134858454) * 10^40
        + 135975986546595312959695928659628010001) : ℚ) /
        ((((((((((1233318202932009413819544578186947062 * 10^40
        + 135079955945156617695938875786987868630) * 10^40
        + 9551150461876522178435890386753241720447) * 10^40
        + 6055623617580392767570247134554211619847) * 10^40
        + 5475644471909323174000404337653496601882) * 10^40
        + 9232170844433117355214552377555806436575) * 10^40
        + 3195665097983068917858842241167527786965) * 10^40
        + 3879863574434158630371675185091630538810) * 10^40
        + 1637560903822224773511091745352635711892) * 10^40
        + 8935232904262250855034614398645610196628) * 10^40
        + 443015476690202503677567429277024080008)),
    ((0 : ℚ) /
        1))

theorem endpointRightP005BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP005Center2544‖ ≤ endpointRightP005Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP005Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP005Input2544]
  have hc : (compactExp2542 endpointRightP005Input2544 5).1 = endpointRightP005Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP005Input2544 5).2 : ℝ) = endpointRightP005Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP005Input2544 5).2 =
        ((9130344602477 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP005Error2544]
  have h := compactExp_error2542 endpointRightP005Input2544 hz 5
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          endpointRightP005Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP005Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP005DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP005Factor2544 * embedPair2542 endpointRightP005Center2544‖ ≤
      (pairMagnitude2542 endpointRightP005Factor2544 : ℝ) * endpointRightP005Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨5, by omega⟩)
      (storedWidth ⟨5, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP005Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP005Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨5, by omega⟩) (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP005BaseError2544
    (embedPair_magnitude2542 endpointRightP005Factor2544)

def endpointRightP006Input2544 : RatPair2542 :=
  ((((-127975970897319380164091345862964161) : ℚ) /
        135988780273982091902841651200000000),
    ((0 : ℚ) /
        1))

def endpointRightP006Center2544 : RatPair2542 :=
  (((6611928741841539 : ℚ) /
        79228162514264337593543950336),
    ((0 : ℚ) /
        1))

noncomputable def endpointRightP006Error2544 : ℝ := ((2934505226153 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

def endpointRightP006Factor2544 : RatPair2542 :=
  ((((((425435321062947856 * 10^40
        + 985226165840451896442367399916963706768) * 10^40
        + 9318043556375662676630099341554588000045) * 10^40
        + 6334511827623806897424317014907427434241) : ℚ) /
        (((40870396224478791 * 10^40
        + 9050435693890042605396440110849106695679) * 10^40
        + 6606150835142405604757367704392404329959) * 10^40
        + 9483020926843895179394536119259419473928)),
    ((0 : ℚ) /
        1))

theorem endpointRightP006BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP006Center2544‖ ≤ endpointRightP006Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP006Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP006Input2544]
  have hc : (compactExp2542 endpointRightP006Input2544 5).1 = endpointRightP006Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP006Input2544 5).2 : ℝ) = endpointRightP006Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP006Input2544 5).2 =
        ((2934505226153 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [endpointRightP006Error2544]
  have h := compactExp_error2542 endpointRightP006Input2544 hz 5
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          endpointRightP006Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP006Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP006DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP006Factor2544 * embedPair2542 endpointRightP006Center2544‖ ≤
      (pairMagnitude2542 endpointRightP006Factor2544 : ℝ) * endpointRightP006Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP006Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP006Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP006BaseError2544
    (embedPair_magnitude2542 endpointRightP006Factor2544)

def endpointRightP007Input2544 : RatPair2542 :=
  ((((-((3467731 * 10^40
        + 8511828977644856382439885982238229303076) * 10^40
        + 4074901543573001235591471814120322040639)) : ℚ) /
        ((3702566 * 10^40
        + 1798274771324049224126879736705847104476) * 10^40
        + 6755632940817925151281205218508800000000)),
    ((0 : ℚ) /
        1))

def endpointRightP007Center2544 : RatPair2542 :=
  (((122184672846750071 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def endpointRightP007Error2544 : ℝ := ((13166735637951 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP007Factor2544 : RatPair2542 :=
  ((((((((((((((318418 * 10^40
        + 545166010765831702757530821760931234188) * 10^40
        + 3517008809487728202592728344807875421237) * 10^40
        + 4787298318644103811495354185597731889539) * 10^40
        + 1383856840107647327696900973698599310370) * 10^40
        + 6934278921273906234204262210567805080008) * 10^40
        + 2424891691254391336617443625123066622472) * 10^40
        + 9179670464980015255540644562549223657191) * 10^40
        + 2336242145633053405812596159181969584616) * 10^40
        + 3113619218708397092289700301549910135028) * 10^40
        + 3236992887412405160205696823258154216321) * 10^40
        + 3048725552314438277799862801369262941441) : ℚ) /
        (((((((((((166497 * 10^40
        + 3618103119209832665011904838943561842291) * 10^40
        + 5277570746127744779650254318866446500507) * 10^40
        + 9189721528894732054070470171478608299617) * 10^40
        + 5996213938528317055126592813722604414405) * 10^40
        + 3567923151341927609639602050293202066450) * 10^40
        + 5862822706515316646454820129106144418025) * 10^40
        + 6488495192391804878676397306134450689250) * 10^40
        + 7422852304636821188585009106764856659264) * 10^40
        + 8164435240416746868311242905829635533402) * 10^40
        + 4169760532377763645842969338223248295188) * 10^40
        + 5413548418515506222398902410954103531528)),
    ((0 : ℚ) /
        1))

theorem endpointRightP007BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP007Center2544‖ ≤ endpointRightP007Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP007Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP007Input2544]
  have hc : (compactExp2542 endpointRightP007Input2544 5).1 = endpointRightP007Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP007Input2544 5).2 : ℝ) = endpointRightP007Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP007Input2544 5).2 =
        ((13166735637951 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP007Error2544]
  have h := compactExp_error2542 endpointRightP007Input2544 hz 5
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          endpointRightP007Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP007Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP007DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP007Factor2544 * embedPair2542 endpointRightP007Center2544‖ ≤
      (pairMagnitude2542 endpointRightP007Factor2544 : ℝ) * endpointRightP007Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP007Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP007Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP007BaseError2544
    (embedPair_magnitude2542 endpointRightP007Factor2544)

def endpointRightP008Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-83697431251741758597728337) : ℚ) /
        922337203685477580800000000))

def endpointRightP008Center2544 : RatPair2542 :=
  (((75678898124574477 : ℚ) /
        1267650600228229401496703205376),
    ((38968301667069885 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointRightP008Error2544 : ℝ := ((7984746117365 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

def endpointRightP008Factor2544 : RatPair2542 :=
  ((((((((((((((5379978964238155890168498602309340 * 10^40
        + 1325640100351039656097227919748362756598) * 10^40
        + 220177206890423378317290349002224074419) * 10^40
        + 4634055202833856564380743532323114046462) * 10^40
        + 8851126954027581295373475624262713611040) * 10^40
        + 5176984168125859067855777660852958344710) * 10^40
        + 7150609327721763809858619504050932741885) * 10^40
        + 4960888333251608091760085908738510494003) * 10^40
        + 531727144486164046173751493159867223117) * 10^40
        + 8776651358930220450151829322290821262) * 10^40
        + 6686171958691829898351366028427244322874) * 10^40
        + 9830374731523699984105709705244613039037) : ℚ) /
        (((((((((((4053154581804533747215819071326 * 10^40
        + 515903515321946232446946550867538452940) * 10^40
        + 2772542792314301176358637941146098631815) * 10^40
        + 4395757091334578647635821100694862806748) * 10^40
        + 2858379119514384773771945131142609437936) * 10^40
        + 1203598212520410372585152306343016639042) * 10^40
        + 1997115917148579356089354925153954776461) * 10^40
        + 3164464201758847079364228881045460473151) * 10^40
        + 3598199558609743560579145504695760674887) * 10^40
        + 7588036582801884201001540713092602103423) * 10^40
        + 892149086813588467137751321668453694961) * 10^40
        + 6841673447715482113858971457164360548352)),
    ((((((((((174001191976653044655 * 10^40
        + 3522166198673595700002539355820746930342) * 10^40
        + 8652652114251248052629362465567949340814) * 10^40
        + 8605071886311206357842840235369877603195) * 10^40
        + 4650112209664461694960440389904550657329) * 10^40
        + 5104937963607845603800696377538507416642) * 10^40
        + 6349511560601136938346993420520773027070) * 10^40
        + 3370592536954467707069700589625681713084) * 10^40
        + 7984406751448442832413546000339306282567) : ℚ) /
        ((((((((59585930762453093 * 10^40
        + 1126185733784068775279185241337362855749) * 10^40
        + 329392876194510945667687873683042212784) * 10^40
        + 9003357264940782383064909192708634288369) * 10^40
        + 7162194182653674329176132652029208035087) * 10^40
        + 2077442511016478162094657498653955161796) * 10^40
        + 8990223696421664010779578728122475831262) * 10^40
        + 4161251990707247252185181640311599320344) * 10^40
        + 8725440271758821535034431238053212192768)))

theorem endpointRightP008BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP008Center2544‖ ≤ endpointRightP008Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP008Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP008Input2544]
  have hc : (compactExp2542 endpointRightP008Input2544 6).1 = endpointRightP008Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP008Input2544 6).2 : ℝ) = endpointRightP008Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP008Input2544 6).2 =
        ((7984746117365 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [endpointRightP008Error2544]
  have h := compactExp_error2542 endpointRightP008Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP008Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP008Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP008DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP008Factor2544 * embedPair2542 endpointRightP008Center2544‖ ≤
      (pairMagnitude2542 endpointRightP008Factor2544 : ℝ) * endpointRightP008Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP008Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP008Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP008BaseError2544
    (embedPair_magnitude2542 endpointRightP008Factor2544)

def endpointRightP009Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-124480009324152847187337231) : ℚ) /
        922337203685477580800000000))

def endpointRightP009Center2544 : RatPair2542 :=
  ((((-30039768110131961) : ℚ) /
        633825300114114700748351602688),
    (((-60301521404716477) : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointRightP009Error2544 : ℝ := ((47043363468949 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP009Factor2544 : RatPair2542 :=
  ((((((((((((((11745896487217505853952598215205904 * 10^40
        + 7733029975924842994911445486640777133451) * 10^40
        + 1926751649622845936184461975288055832158) * 10^40
        + 9429058926306368663325462288293957752161) * 10^40
        + 2910352849869620535673570385089654727533) * 10^40
        + 9726018256647515945572788081104111301769) * 10^40
        + 7296365977478324913980589502321481246619) * 10^40
        + 8332070647253967318233036721080257816496) * 10^40
        + 7421441655779052336893511459821615171994) * 10^40
        + 9749709973608087232817075856290511824732) * 10^40
        + 5517064343601603291140312064089457025222) * 10^40
        + 775177601595866148043982219243652683261) : ℚ) /
        (((((((((((4053154581804533747215819071326 * 10^40
        + 515903515321946232446946550867538452940) * 10^40
        + 2772542792314301176358637941146098631815) * 10^40
        + 4395757091334578647635821100694862806748) * 10^40
        + 2858379119514384773771945131142609437936) * 10^40
        + 1203598212520410372585152306343016639042) * 10^40
        + 1997115917148579356089354925153954776461) * 10^40
        + 3164464201758847079364228881045460473151) * 10^40
        + 3598199558609743560579145504695760674887) * 10^40
        + 7588036582801884201001540713092602103423) * 10^40
        + 892149086813588467137751321668453694961) * 10^40
        + 6841673447715482113858971457164360548352)),
    ((((((((((3934621905013094510989 * 10^40
        + 506204621742900230801346902916100147514) * 10^40
        + 9217975607061227506464310614848821829378) * 10^40
        + 2281559563454251860571833241522445846701) * 10^40
        + 4494792844637266253921877781351127592484) * 10^40
        + 4508076630712340630899069784438093665985) * 10^40
        + 4338422708742945243667746135193032674092) * 10^40
        + 565316171913638932212958968327442203130) * 10^40
        + 2322702322849568916851953877103265770799) : ℚ) /
        ((((((((417101515337171651 * 10^40
        + 7883300136488481426954296689361539990243) * 10^40
        + 2305750133361576619673815115781295489494) * 10^40
        + 3023500854585476681454364348960440018588) * 10^40
        + 135359278575720304232928564204456245610) * 10^40
        + 4542097577115347134662602490577686132578) * 10^40
        + 2931565874951648075457051096857330818836) * 10^40
        + 9128763934950730765296271482181195242414) * 10^40
        + 1078081902311750745241018666372485349376)))

theorem endpointRightP009BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP009Center2544‖ ≤ endpointRightP009Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP009Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP009Input2544]
  have hc : (compactExp2542 endpointRightP009Input2544 6).1 = endpointRightP009Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP009Input2544 6).2 : ℝ) = endpointRightP009Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP009Input2544 6).2 =
        ((47043363468949 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP009Error2544]
  have h := compactExp_error2542 endpointRightP009Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP009Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP009Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP009DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP009Factor2544 * embedPair2542 endpointRightP009Center2544‖ ≤
      (pairMagnitude2542 endpointRightP009Factor2544 : ℝ) * endpointRightP009Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP009Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP009Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP009BaseError2544
    (embedPair_magnitude2542 endpointRightP009Factor2544)

def endpointRightP010Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-74049707789522705117225241) : ℚ) /
        461168601842738790400000000))

def endpointRightP010Center2544 : RatPair2542 :=
  ((((-14017905555603873) : ℚ) /
        316912650057057350374175801344),
    ((64045275684567125 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointRightP010Error2544 : ℝ := ((2911352684741 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

def endpointRightP010Factor2544 : RatPair2542 :=
  ((((((((((((((4143328088465305274889028954502289 * 10^40
        + 3814425678344811939892406089241473767353) * 10^40
        + 4368120968219062291582827274727830107448) * 10^40
        + 2137893797355407734089172508034499748878) * 10^40
        + 7904808679069610665974419097689819769920) * 10^40
        + 3989207714433666162631161630210766340173) * 10^40
        + 1195198055623437376255233370411687625685) * 10^40
        + 5644713286470601176942394892492923199218) * 10^40
        + 5434874159528317723921935339117643882692) * 10^40
        + 2254594819640886093593857780233416605729) * 10^40
        + 1046459581787944468376075044354485433186) * 10^40
        + 787495862757560414684367477915083535693) : ℚ) /
        (((((((((((1013288645451133436803954767831 * 10^40
        + 5128975878830486558111736637716884613235) * 10^40
        + 693135698078575294089659485286524657953) * 10^40
        + 8598939272833644661908955275173715701687) * 10^40
        + 714594779878596193442986282785652359484) * 10^40
        + 300899553130102593146288076585754159760) * 10^40
        + 5499278979287144839022338731288488694115) * 10^40
        + 3291116050439711769841057220261365118287) * 10^40
        + 8399549889652435890144786376173940168721) * 10^40
        + 9397009145700471050250385178273150525855) * 10^40
        + 7723037271703397116784437830417113423740) * 10^40
        + 4210418361928870528464742864291090137088)),
    ((((((((((824587278572636980183 * 10^40
        + 6039721356111456886382593179691137912975) * 10^40
        + 8735765580408905167009616714676732811570) * 10^40
        + 4089416776668062158689065346973914340230) * 10^40
        + 2179346065197377999305074568711083105089) * 10^40
        + 8073440428273540056032048289199549965646) * 10^40
        + 6985757044580503754195732197565699758380) * 10^40
        + 3390717950833907425464764054028674446153) * 10^40
        + 6002586247065242924535489935839373635593) : ℚ) /
        ((((((((52137689417146456 * 10^40
        + 4735412517061060178369287086170192498780) * 10^40
        + 4038218766670197077459226889472661936186) * 10^40
        + 7877937606823184585181795543620055002323) * 10^40
        + 5016919909821965038029116070525557030701) * 10^40
        + 3067762197139418391832825311322210766572) * 10^40
        + 2866445734368956009432131387107166352354) * 10^40
        + 6141095491868841345662033935272649405301) * 10^40
        + 7634760237788968843155127333296560668672)))

theorem endpointRightP010BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP010Center2544‖ ≤ endpointRightP010Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP010Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP010Input2544]
  have hc : (compactExp2542 endpointRightP010Input2544 6).1 = endpointRightP010Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP010Input2544 6).2 : ℝ) = endpointRightP010Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP010Input2544 6).2 =
        ((2911352684741 : ℚ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736)) := by cbv
    rw [hq]
    norm_num [endpointRightP010Error2544]
  have h := compactExp_error2542 endpointRightP010Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP010Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP010Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP010DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP010Factor2544 * embedPair2542 endpointRightP010Center2544‖ ≤
      (pairMagnitude2542 endpointRightP010Factor2544 : ℝ) * endpointRightP010Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP010Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP010Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP010BaseError2544
    (embedPair_magnitude2542 endpointRightP010Factor2544)

def endpointRightP011Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-81923590457429860456094121) : ℚ) /
        461168601842738790400000000))

def endpointRightP011Center2544 : RatPair2542 :=
  (((31067693906795939 : ℚ) /
        1267650600228229401496703205376),
    ((79250378872779645 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointRightP011Error2544 : ℝ := ((21117980314573 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def endpointRightP011Factor2544 : RatPair2542 :=
  ((((((((((((((5064184383564645994779819510803178 * 10^40
        + 5588636881804881331516349408844939000135) * 10^40
        + 4026859073652587904690300921209073682229) * 10^40
        + 2744105084439020151065463905721344816176) * 10^40
        + 8982164778305077653249338067342324998206) * 10^40
        + 6760098362103519433969091883703924713624) * 10^40
        + 6472088879453025860674448813018246495946) * 10^40
        + 713603054062133451270884643680507574532) * 10^40
        + 2732296623167968419208906429485573876913) * 10^40
        + 3451069708123354208052484615889391425626) * 10^40
        + 8753962486065604637626264727755305867876) * 10^40
        + 8019091726474875770948322767783710700013) : ℚ) /
        (((((((((((1013288645451133436803954767831 * 10^40
        + 5128975878830486558111736637716884613235) * 10^40
        + 693135698078575294089659485286524657953) * 10^40
        + 8598939272833644661908955275173715701687) * 10^40
        + 714594779878596193442986282785652359484) * 10^40
        + 300899553130102593146288076585754159760) * 10^40
        + 5499278979287144839022338731288488694115) * 10^40
        + 3291116050439711769841057220261365118287) * 10^40
        + 8399549889652435890144786376173940168721) * 10^40
        + 9397009145700471050250385178273150525855) * 10^40
        + 7723037271703397116784437830417113423740) * 10^40
        + 4210418361928870528464742864291090137088)),
    ((((((((((1114390580387940291608 * 10^40
        + 819080718634294755736939957389671593264) * 10^40
        + 9776781732256019603351136858499996171384) * 10^40
        + 6251071082825688996494747952812656653063) * 10^40
        + 3756182324717270081880040942480775386837) * 10^40
        + 8861218731403876734547420482311167054354) * 10^40
        + 1417473096972136781871662443750495219129) * 10^40
        + 7873795175219674600981818403656409583495) * 10^40
        + 6567422753737665364388306696288353329593) : ℚ) /
        ((((((((52137689417146456 * 10^40
        + 4735412517061060178369287086170192498780) * 10^40
        + 4038218766670197077459226889472661936186) * 10^40
        + 7877937606823184585181795543620055002323) * 10^40
        + 5016919909821965038029116070525557030701) * 10^40
        + 3067762197139418391832825311322210766572) * 10^40
        + 2866445734368956009432131387107166352354) * 10^40
        + 6141095491868841345662033935272649405301) * 10^40
        + 7634760237788968843155127333296560668672)))

theorem endpointRightP011BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP011Center2544‖ ≤ endpointRightP011Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP011Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP011Input2544]
  have hc : (compactExp2542 endpointRightP011Input2544 6).1 = endpointRightP011Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP011Input2544 6).2 : ℝ) = endpointRightP011Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP011Input2544 6).2 =
        ((21117980314573 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [endpointRightP011Error2544]
  have h := compactExp_error2542 endpointRightP011Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP011Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP011Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP011DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP011Factor2544 * embedPair2542 endpointRightP011Center2544‖ ≤
      (pairMagnitude2542 endpointRightP011Factor2544 : ℝ) * endpointRightP011Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP011Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP011Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP011BaseError2544
    (embedPair_magnitude2542 endpointRightP011Factor2544)

def endpointRightP012Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-1801580117301358815136389) : ℚ) /
        9223372036854775808000000))

def endpointRightP012Center2544 : RatPair2542 :=
  (((21235111400005671 : ℚ) /
        316912650057057350374175801344),
    ((1390702552558213 : ℚ) /
        316912650057057350374175801344))

noncomputable def endpointRightP012Error2544 : ℝ := ((1516939706649 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

def endpointRightP012Factor2544 : RatPair2542 :=
  ((((((((((((((1528996453032894227141854909138836 * 10^40
        + 2704435856903674742554668601917248401715) * 10^40
        + 5028236282101475522363629115461154210391) * 10^40
        + 8359184520048205193027521351450446847194) * 10^40
        + 2933524035268066091594299462021551371533) * 10^40
        + 9869991600209006706600993631221074871533) * 10^40
        + 1255700433893676760218616771640194703584) * 10^40
        + 4298884159178948088070003322448509871362) * 10^40
        + 1181831460450899373663996425580292537632) * 10^40
        + 5564917988477684189273496107014974943493) * 10^40
        + 7309064034800916377805988291404904362735) * 10^40
        + 9071643664711179568329709042897863339909) : ℚ) /
        (((((((((((253322161362783359200988691957 * 10^40
        + 8782243969707621639527934159429221153308) * 10^40
        + 7673283924519643823522414871321631164488) * 10^40
        + 4649734818208411165477238818793428925421) * 10^40
        + 7678648694969649048360746570696413089871) * 10^40
        + 75224888282525648286572019146438539940) * 10^40
        + 1374819744821786209755584682822122173528) * 10^40
        + 8322779012609927942460264305065341279571) * 10^40
        + 9599887472413108972536196594043485042180) * 10^40
        + 4849252286425117762562596294568287631463) * 10^40
        + 9430759317925849279196109457604278355935) * 10^40
        + 1052604590482217632116185716072772534272)),
    ((((((((((184896771598569785150 * 10^40
        + 7218758715991575217441538008450292991646) * 10^40
        + 3477904924551326985741754542146194279180) * 10^40
        + 4433598540752096731719122409087298533120) * 10^40
        + 4762967993299476825282795491332735727345) * 10^40
        + 7635142590639667104602088383566683877834) * 10^40
        + 2828774221473712307179705907161776005841) * 10^40
        + 527189993877489859921760378549481201642) * 10^40
        + 9169135593275438203734646542163897629925) : ℚ) /
        ((((((((6517211177143307 * 10^40
        + 591926564632632522296160885771274062347) * 10^40
        + 5504777345833774634682403361184082742023) * 10^40
        + 3484742200852898073147724442952506875290) * 10^40
        + 4377114988727745629753639508815694628837) * 10^40
        + 6633470274642427298979103163915276345821) * 10^40
        + 5358305716796119501179016423388395794044) * 10^40
        + 3267636936483605168207754241909081175662) * 10^40
        + 7204345029723621105394390916662070083584)))

theorem endpointRightP012BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP012Center2544‖ ≤ endpointRightP012Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP012Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP012Input2544]
  have hc : (compactExp2542 endpointRightP012Input2544 6).1 = endpointRightP012Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP012Input2544 6).2 : ℝ) = endpointRightP012Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP012Input2544 6).2 =
        ((1516939706649 : ℚ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736)) := by cbv
    rw [hq]
    norm_num [endpointRightP012Error2544]
  have h := compactExp_error2542 endpointRightP012Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP012Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP012Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP012DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP012Factor2544 * embedPair2542 endpointRightP012Center2544‖ ≤
      (pairMagnitude2542 endpointRightP012Factor2544 : ℝ) * endpointRightP012Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP012Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP012Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP012BaseError2544
    (embedPair_magnitude2542 endpointRightP012Factor2544)

def endpointRightP013Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-19502183631944175412566411) : ℚ) /
        92233720368547758080000000))

def endpointRightP013Center2544 : RatPair2542 :=
  (((24200498752788563 : ℚ) /
        633825300114114700748351602688),
    (((-70022622034815297) : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointRightP013Error2544 : ℝ := ((40989034846297 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP013Factor2544 : RatPair2542 :=
  ((((((((((((((7161338282368115797304827438509482 * 10^40
        + 3972411382874696062215231262674880503886) * 10^40
        + 2018523304746360017258827002609501590253) * 10^40
        + 1422312947386497557329318468092094940205) * 10^40
        + 9513104717438747541248372151641509426825) * 10^40
        + 3589820390440598864244194800831314534942) * 10^40
        + 1691260288326217504946452049925511230857) * 10^40
        + 8360776426664287509683528927079872693497) * 10^40
        + 3373106874267671438662538680175778684081) * 10^40
        + 7840883268855264255613280642946782942446) * 10^40
        + 6408996991358064587639786520595293138532) * 10^40
        + 4654520895948609194938474784243679318061) : ℚ) /
        (((((((((((1013288645451133436803954767831 * 10^40
        + 5128975878830486558111736637716884613235) * 10^40
        + 693135698078575294089659485286524657953) * 10^40
        + 8598939272833644661908955275173715701687) * 10^40
        + 714594779878596193442986282785652359484) * 10^40
        + 300899553130102593146288076585754159760) * 10^40
        + 5499278979287144839022338731288488694115) * 10^40
        + 3291116050439711769841057220261365118287) * 10^40
        + 8399549889652435890144786376173940168721) * 10^40
        + 9397009145700471050250385178273150525855) * 10^40
        + 7723037271703397116784437830417113423740) * 10^40
        + 4210418361928870528464742864291090137088)),
    ((((((((((1874318246992982564936 * 10^40
        + 2716033022415505488425162239921144897371) * 10^40
        + 9996193167562198186578884458764511608484) * 10^40
        + 343888850260088790917411874732350905653) * 10^40
        + 7553524789493854772778198565696458651170) * 10^40
        + 3491481256648043205592288248836637305637) * 10^40
        + 2321476931410013834967690535715512065595) * 10^40
        + 7130996553261093964702710073133302304971) * 10^40
        + 3628284593406865051237844132603265912935) : ℚ) /
        ((((((((52137689417146456 * 10^40
        + 4735412517061060178369287086170192498780) * 10^40
        + 4038218766670197077459226889472661936186) * 10^40
        + 7877937606823184585181795543620055002323) * 10^40
        + 5016919909821965038029116070525557030701) * 10^40
        + 3067762197139418391832825311322210766572) * 10^40
        + 2866445734368956009432131387107166352354) * 10^40
        + 6141095491868841345662033935272649405301) * 10^40
        + 7634760237788968843155127333296560668672)))

theorem endpointRightP013BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP013Center2544‖ ≤ endpointRightP013Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP013Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP013Input2544]
  have hc : (compactExp2542 endpointRightP013Input2544 6).1 = endpointRightP013Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP013Input2544 6).2 : ℝ) = endpointRightP013Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP013Input2544 6).2 =
        ((40989034846297 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP013Error2544]
  have h := compactExp_error2542 endpointRightP013Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP013Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP013Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP013DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP013Factor2544 * embedPair2542 endpointRightP013Center2544‖ ≤
      (pairMagnitude2542 endpointRightP013Factor2544 : ℝ) * endpointRightP013Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP013Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP013Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP013BaseError2544
    (embedPair_magnitude2542 endpointRightP013Factor2544)

def endpointRightP014Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-111281490475376521366248531) : ℚ) /
        461168601842738790400000000))

def endpointRightP014Center2544 : RatPair2542 :=
  ((((-82160928314915089) : ℚ) /
        1267650600228229401496703205376),
    (((-11128859045257829) : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointRightP014Error2544 : ℝ := ((46835536846957 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP014Factor2544 : RatPair2542 :=
  ((((((((((((((9317192357513612091611852522303952 * 10^40
        + 1423400632185489121458097905644807287142) * 10^40
        + 675604935101497759019562240534393909924) * 10^40
        + 5575369325277089435783856221416716734109) * 10^40
        + 8680632011670183506663315210277776054479) * 10^40
        + 3963202783225866836823746807846660645488) * 10^40
        + 4297129624688108028883418172660948199511) * 10^40
        + 6384834029058963058061118278933129493266) * 10^40
        + 5016376243291895237929673905903277811421) * 10^40
        + 4386667407489732794247769215485054950867) * 10^40
        + 6222102529333328932942433519572295147981) * 10^40
        + 9178503792617163030679552286520052430053) : ℚ) /
        (((((((((((1013288645451133436803954767831 * 10^40
        + 5128975878830486558111736637716884613235) * 10^40
        + 693135698078575294089659485286524657953) * 10^40
        + 8598939272833644661908955275173715701687) * 10^40
        + 714594779878596193442986282785652359484) * 10^40
        + 300899553130102593146288076585754159760) * 10^40
        + 5499278979287144839022338731288488694115) * 10^40
        + 3291116050439711769841057220261365118287) * 10^40
        + 8399549889652435890144786376173940168721) * 10^40
        + 9397009145700471050250385178273150525855) * 10^40
        + 7723037271703397116784437830417113423740) * 10^40
        + 4210418361928870528464742864291090137088)),
    ((((((((((2781783255234853399856 * 10^40
        + 3686811852814689748002824182578190334971) * 10^40
        + 5887817172659659259557342889566681574501) * 10^40
        + 5507545980108073802124490876160012295842) * 10^40
        + 6613943222545924860214913771958892189480) * 10^40
        + 5427805362157792216483441014022989431009) * 10^40
        + 9327706712531363947657173051217243601991) * 10^40
        + 6730587858759173119298887780597399636955) * 10^40
        + 2858279368533382374093483192437907484043) : ℚ) /
        ((((((((52137689417146456 * 10^40
        + 4735412517061060178369287086170192498780) * 10^40
        + 4038218766670197077459226889472661936186) * 10^40
        + 7877937606823184585181795543620055002323) * 10^40
        + 5016919909821965038029116070525557030701) * 10^40
        + 3067762197139418391832825311322210766572) * 10^40
        + 2866445734368956009432131387107166352354) * 10^40
        + 6141095491868841345662033935272649405301) * 10^40
        + 7634760237788968843155127333296560668672)))

theorem endpointRightP014BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP014Center2544‖ ≤ endpointRightP014Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP014Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP014Input2544]
  have hc : (compactExp2542 endpointRightP014Input2544 6).1 = endpointRightP014Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP014Input2544 6).2 : ℝ) = endpointRightP014Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP014Input2544 6).2 =
        ((46835536846957 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP014Error2544]
  have h := compactExp_error2542 endpointRightP014Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP014Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP014Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP014DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP014Factor2544 * embedPair2542 endpointRightP014Center2544‖ ≤
      (pairMagnitude2542 endpointRightP014Factor2544 : ℝ) * endpointRightP014Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP014Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP014Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP014BaseError2544
    (embedPair_magnitude2542 endpointRightP014Factor2544)

def endpointRightP015Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-121148152407873549709974087) : ℚ) /
        461168601842738790400000000))

def endpointRightP015Center2544 : RatPair2542 :=
  ((((-38252678060581621) : ℚ) /
        1267650600228229401496703205376),
    ((76043124458158487 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointRightP015Error2544 : ℝ := ((14636194061413 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

def endpointRightP015Factor2544 : RatPair2542 :=
  ((((((((((((((11036740856579181830755487359244973 * 10^40
        + 242649862859101474624608058444361588042) * 10^40
        + 1430740605690581386809645594181118818203) * 10^40
        + 6472087504918714694981984455976945953008) * 10^40
        + 2324133675211113418012528096222490364617) * 10^40
        + 1676098063283133356329930926584582359218) * 10^40
        + 1226912853209152403985225260607271774904) * 10^40
        + 6153581361080095911260454611397959952887) * 10^40
        + 9047056760125231693832095087017394404216) * 10^40
        + 1023398055782127973575967161031460063099) * 10^40
        + 3716882135946864782572582836321712192017) * 10^40
        + 9305236932425963334056343448375360543629) : ℚ) /
        (((((((((((1013288645451133436803954767831 * 10^40
        + 5128975878830486558111736637716884613235) * 10^40
        + 693135698078575294089659485286524657953) * 10^40
        + 8598939272833644661908955275173715701687) * 10^40
        + 714594779878596193442986282785652359484) * 10^40
        + 300899553130102593146288076585754159760) * 10^40
        + 5499278979287144839022338731288488694115) * 10^40
        + 3291116050439711769841057220261365118287) * 10^40
        + 8399549889652435890144786376173940168721) * 10^40
        + 9397009145700471050250385178273150525855) * 10^40
        + 7723037271703397116784437830417113423740) * 10^40
        + 4210418361928870528464742864291090137088)),
    ((((((((((3586571000500018965486 * 10^40
        + 5650349500266553933845408246890078401503) * 10^40
        + 2248343728744512642086332403798202263241) * 10^40
        + 9079041951782324081167623439997662126412) * 10^40
        + 2948215474238191873690480255378348705795) * 10^40
        + 9109645535239880241730590382439415552972) * 10^40
        + 7248650504314902055679804193729976915431) * 10^40
        + 8672365495711636240116622678580924705616) * 10^40
        + 6130542006434682506181863170025689949207) : ℚ) /
        ((((((((52137689417146456 * 10^40
        + 4735412517061060178369287086170192498780) * 10^40
        + 4038218766670197077459226889472661936186) * 10^40
        + 7877937606823184585181795543620055002323) * 10^40
        + 5016919909821965038029116070525557030701) * 10^40
        + 3067762197139418391832825311322210766572) * 10^40
        + 2866445734368956009432131387107166352354) * 10^40
        + 6141095491868841345662033935272649405301) * 10^40
        + 7634760237788968843155127333296560668672)))

theorem endpointRightP015BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP015Center2544‖ ≤ endpointRightP015Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP015Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP015Input2544]
  have hc : (compactExp2542 endpointRightP015Input2544 6).1 = endpointRightP015Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP015Input2544 6).2 : ℝ) = endpointRightP015Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP015Input2544 6).2 =
        ((14636194061413 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [endpointRightP015Error2544]
  have h := compactExp_error2542 endpointRightP015Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP015Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP015Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP015DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP015Factor2544 * embedPair2542 endpointRightP015Center2544‖ ≤
      (pairMagnitude2542 endpointRightP015Factor2544 : ℝ) * endpointRightP015Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP015Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP015Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP015BaseError2544
    (embedPair_magnitude2542 endpointRightP015Factor2544)

def endpointRightP016Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-64139286418828663293690489) : ℚ) /
        230584300921369395200000000))

def endpointRightP016Center2544 : RatPair2542 :=
  (((5318950355279571 : ℚ) /
        158456325028528675187087900672),
    ((73723708884741065 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointRightP016Error2544 : ℝ := ((53659945627381 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP016Factor2544 : RatPair2542 :=
  ((((((((((((((3092573854469459346397074363196305 * 10^40
        + 1995780037645603502175273368038436196733) * 10^40
        + 883601926202962360525433413762243030906) * 10^40
        + 4435152939900399926756442375264446650065) * 10^40
        + 7162472449119328356458427138667897896696) * 10^40
        + 9067057804409878160973656821638439528975) * 10^40
        + 898561752313484194446150534521644007998) * 10^40
        + 13628029540702298041709401553933047748) * 10^40
        + 8398115251685155574657189360661759896763) * 10^40
        + 7372646560906733110891258294125193280179) * 10^40
        + 1820500213823948826152486561817806364984) * 10^40
        + 4267421116927541069513399040129769534221) : ℚ) /
        (((((((((((253322161362783359200988691957 * 10^40
        + 8782243969707621639527934159429221153308) * 10^40
        + 7673283924519643823522414871321631164488) * 10^40
        + 4649734818208411165477238818793428925421) * 10^40
        + 7678648694969649048360746570696413089871) * 10^40
        + 75224888282525648286572019146438539940) * 10^40
        + 1374819744821786209755584682822122173528) * 10^40
        + 8322779012609927942460264305065341279571) * 10^40
        + 9599887472413108972536196594043485042180) * 10^40
        + 4849252286425117762562596294568287631463) * 10^40
        + 9430759317925849279196109457604278355935) * 10^40
        + 1052604590482217632116185716072772534272)),
    ((((((((((531999679654652253841 * 10^40
        + 420466843162889045742022645036364515198) * 10^40
        + 3635637328910095671726341220560956330307) * 10^40
        + 1066708940883541119703540157669376189871) * 10^40
        + 6989090073164924917423071799619431112826) * 10^40
        + 6696629489930247533802165518855050498977) * 10^40
        + 9350155589145474798499187349530231370141) * 10^40
        + 8057206454692428136725927303823832775017) * 10^40
        + 9413795275946740040580755778624070233641) : ℚ) /
        ((((((((6517211177143307 * 10^40
        + 591926564632632522296160885771274062347) * 10^40
        + 5504777345833774634682403361184082742023) * 10^40
        + 3484742200852898073147724442952506875290) * 10^40
        + 4377114988727745629753639508815694628837) * 10^40
        + 6633470274642427298979103163915276345821) * 10^40
        + 5358305716796119501179016423388395794044) * 10^40
        + 3267636936483605168207754241909081175662) * 10^40
        + 7204345029723621105394390916662070083584)))

theorem endpointRightP016BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP016Center2544‖ ≤ endpointRightP016Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP016Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP016Input2544]
  have hc : (compactExp2542 endpointRightP016Input2544 6).1 = endpointRightP016Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP016Input2544 6).2 : ℝ) = endpointRightP016Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP016Input2544 6).2 =
        ((53659945627381 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP016Error2544]
  have h := compactExp_error2542 endpointRightP016Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP016Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP016Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP016DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP016Factor2544 * embedPair2542 endpointRightP016Center2544‖ ≤
      (pairMagnitude2542 endpointRightP016Factor2544 : ℝ) * endpointRightP016Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP016Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP016Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP016BaseError2544
    (embedPair_magnitude2542 endpointRightP016Factor2544)

def endpointRightP017Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-142128968738930782070534667) : ℚ) /
        461168601842738790400000000))

def endpointRightP017Center2544 : RatPair2542 :=
  (((3411013174531863 : ℚ) /
        79228162514264337593543950336),
    (((-4082767411106281) : ℚ) /
        79228162514264337593543950336))

noncomputable def endpointRightP017Error2544 : ℝ := ((25052858391699 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def endpointRightP017Factor2544 : RatPair2542 :=
  ((((((((((((((15178531749707734422644626524268059 * 10^40
        + 772051666481556538527402037077914051234) * 10^40
        + 8623215789238745065611552553449119600240) * 10^40
        + 6339843052077671756870230613326504017791) * 10^40
        + 914637423038185942730825854109269291225) * 10^40
        + 7111635127283035786880525907061252274336) * 10^40
        + 4960953649908631731778636498966825826717) * 10^40
        + 7493565713344535273171074362393381731387) * 10^40
        + 7830669316353712103969384968348500631065) * 10^40
        + 417862930571096277108632129185986442061) * 10^40
        + 4931890388677940734478919823264354099916) * 10^40
        + 5274761560590469549473689368632610607669) : ℚ) /
        (((((((((((1013288645451133436803954767831 * 10^40
        + 5128975878830486558111736637716884613235) * 10^40
        + 693135698078575294089659485286524657953) * 10^40
        + 8598939272833644661908955275173715701687) * 10^40
        + 714594779878596193442986282785652359484) * 10^40
        + 300899553130102593146288076585754159760) * 10^40
        + 5499278979287144839022338731288488694115) * 10^40
        + 3291116050439711769841057220261365118287) * 10^40
        + 8399549889652435890144786376173940168721) * 10^40
        + 9397009145700471050250385178273150525855) * 10^40
        + 7723037271703397116784437830417113423740) * 10^40
        + 4210418361928870528464742864291090137088)),
    ((((((((((826414330998464228339 * 10^40
        + 8509729577860850574396758932198601300535) * 10^40
        + 1081577359477780411399641238266360008174) * 10^40
        + 3569642346146116215603897040328851941707) * 10^40
        + 8971364521045862148839219616246937899768) * 10^40
        + 3355335596316571250141460650971055891341) * 10^40
        + 1276489556744197180464606519436105784245) * 10^40
        + 6902403681090692349523089244592535014893) * 10^40
        + 7644590854342443431382078581193212319861) : ℚ) /
        ((((((((7448241345306636 * 10^40
        + 6390773216723008596909898155167170356968) * 10^40
        + 6291174109524313868208460984210380276598) * 10^40
        + 1125419658117597797883113649088579286046) * 10^40
        + 2145274272831709291147016581503651004385) * 10^40
        + 9009680313877059770261832187331744395224) * 10^40
        + 6123777962052708001347447341015309478907) * 10^40
        + 8020156498838405906523147705038949915043) * 10^40
        + 1090680033969852691879303904756651524096)))

theorem endpointRightP017BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP017Center2544‖ ≤ endpointRightP017Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP017Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP017Input2544]
  have hc : (compactExp2542 endpointRightP017Input2544 6).1 = endpointRightP017Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP017Input2544 6).2 : ℝ) = endpointRightP017Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP017Input2544 6).2 =
        ((25052858391699 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [endpointRightP017Error2544]
  have h := compactExp_error2542 endpointRightP017Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP017Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP017Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP017DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP017Factor2544 * embedPair2542 endpointRightP017Center2544‖ ≤
      (pairMagnitude2542 endpointRightP017Factor2544 : ℝ) * endpointRightP017Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP017Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP017Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP017BaseError2544
    (embedPair_magnitude2542 endpointRightP017Factor2544)

def endpointRightP018Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-36841377177147749391625773) : ℚ) /
        115292150460684697600000000))

def endpointRightP018Center2544 : RatPair2542 :=
  ((((-1307289511708849) : ℚ) /
        633825300114114700748351602688),
    (((-85082243345458329) : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointRightP018Error2544 : ℝ := ((56636079998407 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP018Factor2544 : RatPair2542 :=
  ((((((((((((((1019700595965358773078211314330467 * 10^40
        + 9201411286611692549973579493456979070725) * 10^40
        + 7306422278499685211491994686887699929675) * 10^40
        + 5486646662384438275705815889065056056611) * 10^40
        + 2379893570075932945312438072525139805437) * 10^40
        + 9158205900570556093366452957729483412566) * 10^40
        + 7286375502697293064311894986131995519694) * 10^40
        + 2428015809376156734085369868106623037017) * 10^40
        + 4450525056357629306472638150617431384138) * 10^40
        + 8057204247834298906347803084821616351233) * 10^40
        + 3488634444640525162226945190761280864273) * 10^40
        + 7066352328034461599572986145467920974309) : ℚ) /
        (((((((((((63330540340695839800247172989 * 10^40
        + 4695560992426905409881983539857305288327) * 10^40
        + 1918320981129910955880603717830407791122) * 10^40
        + 1162433704552102791369309704698357231355) * 10^40
        + 4419662173742412262090186642674103272467) * 10^40
        + 7518806222070631412071643004786609634985) * 10^40
        + 343704936205446552438896170705530543382) * 10^40
        + 2080694753152481985615066076266335319892) * 10^40
        + 9899971868103277243134049148510871260545) * 10^40
        + 1212313071606279440640649073642071907865) * 10^40
        + 9857689829481462319799027364401069588983) * 10^40
        + 7763151147620554408029046429018193133568)),
    ((((((((((100731746562775606324 * 10^40
        + 2353290323604162789221488508664027833942) * 10^40
        + 7363640200655920365930648751749261219794) * 10^40
        + 7048741635953041574842024819087134200333) * 10^40
        + 3590832423891042635443727184801097852697) * 10^40
        + 7719168007512856675898320663682880770822) * 10^40
        + 2174548505307879454078284356854397049120) * 10^40
        + 3392213371169597985483307916535596144349) * 10^40
        + 9183747675017375272550167220997980552693) : ℚ) /
        ((((((((814651397142913 * 10^40
        + 3823990820579079065287020110721409257793) * 10^40
        + 4438097168229221829335300420148010342752) * 10^40
        + 9185592775106612259143465555369063359411) * 10^40
        + 3047139373590968203719204938601961828604) * 10^40
        + 7079183784330303412372387895489409543227) * 10^40
        + 6919788214599514937647377052923549474255) * 10^40
        + 5408454617060450646025969280238635146957) * 10^40
        + 8400543128715452638174298864582758760448)))

theorem endpointRightP018BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP018Center2544‖ ≤ endpointRightP018Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP018Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP018Input2544]
  have hc : (compactExp2542 endpointRightP018Input2544 6).1 = endpointRightP018Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP018Input2544 6).2 : ℝ) = endpointRightP018Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP018Input2544 6).2 =
        ((56636079998407 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP018Error2544]
  have h := compactExp_error2542 endpointRightP018Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP018Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP018Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP018DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP018Factor2544 * embedPair2542 endpointRightP018Center2544‖ ≤
      (pairMagnitude2542 endpointRightP018Factor2544 : ℝ) * endpointRightP018Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP018Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP018Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP018BaseError2544
    (embedPair_magnitude2542 endpointRightP018Factor2544)

def endpointRightP019Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-7841468079158496015368511) : ℚ) /
        23058430092136939520000000))

def endpointRightP019Center2544 : RatPair2542 :=
  ((((-41472183286353791) : ℚ) /
        633825300114114700748351602688),
    (((-19132595485657273) : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointRightP019Error2544 : ℝ := ((44522606514041 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP019Factor2544 : RatPair2542 :=
  ((((((((((((((1154613207819343336968844584825128 * 10^40
        + 1907881277874755132087251106099709618102) * 10^40
        + 2136340060869954554039721581686743384930) * 10^40
        + 3972010344440303463805360701376969582618) * 10^40
        + 8308910811706184535350457162158754977647) * 10^40
        + 6933107171037913009551556413679356773815) * 10^40
        + 9580920889118786240401243472806034731477) * 10^40
        + 8379600694156470442159723130210928297664) * 10^40
        + 8834598762759047192091228323695307039140) * 10^40
        + 558759220626934539157654144480400355527) * 10^40
        + 8219495289880452748958957474409208460690) * 10^40
        + 5300380573636201407129292907280560977621) : ℚ) /
        (((((((((((63330540340695839800247172989 * 10^40
        + 4695560992426905409881983539857305288327) * 10^40
        + 1918320981129910955880603717830407791122) * 10^40
        + 1162433704552102791369309704698357231355) * 10^40
        + 4419662173742412262090186642674103272467) * 10^40
        + 7518806222070631412071643004786609634985) * 10^40
        + 343704936205446552438896170705530543382) * 10^40
        + 2080694753152481985615066076266335319892) * 10^40
        + 9899971868103277243134049148510871260545) * 10^40
        + 1212313071606279440640649073642071907865) * 10^40
        + 9857689829481462319799027364401069588983) * 10^40
        + 7763151147620554408029046429018193133568)),
    ((((((((((121372884284956742334 * 10^40
        + 8275326896124572151035107841930003074753) * 10^40
        + 2524441830612990095462198577764954352797) * 10^40
        + 5800798012793259087167905623162642208142) * 10^40
        + 2683265375763688759914473959165020566991) * 10^40
        + 4632894752237566854675634763684864346277) * 10^40
        + 3614356759425812004327195519039690123810) * 10^40
        + 5115584870749625817595292942103109916620) * 10^40
        + 7333263291834843829830498637447735764035) : ℚ) /
        ((((((((814651397142913 * 10^40
        + 3823990820579079065287020110721409257793) * 10^40
        + 4438097168229221829335300420148010342752) * 10^40
        + 9185592775106612259143465555369063359411) * 10^40
        + 3047139373590968203719204938601961828604) * 10^40
        + 7079183784330303412372387895489409543227) * 10^40
        + 6919788214599514937647377052923549474255) * 10^40
        + 5408454617060450646025969280238635146957) * 10^40
        + 8400543128715452638174298864582758760448)))

theorem endpointRightP019BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP019Center2544‖ ≤ endpointRightP019Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP019Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP019Input2544]
  have hc : (compactExp2542 endpointRightP019Input2544 6).1 = endpointRightP019Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP019Input2544 6).2 : ℝ) = endpointRightP019Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP019Input2544 6).2 =
        ((44522606514041 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP019Error2544]
  have h := compactExp_error2542 endpointRightP019Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP019Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP019Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP019DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP019Factor2544 * embedPair2542 endpointRightP019Center2544‖ ≤
      (pairMagnitude2542 endpointRightP019Factor2544 : ℝ) * endpointRightP019Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP019Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP019Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP019BaseError2544
    (embedPair_magnitude2542 endpointRightP019Factor2544)

def endpointRightP020Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-167120544922882863756005499) : ℚ) /
        461168601842738790400000000))

def endpointRightP020Center2544 : RatPair2542 :=
  ((((-30726832232824155) : ℚ) /
        1267650600228229401496703205376),
    ((79383159026970969 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointRightP020Error2544 : ℝ := ((11638332541593 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

def endpointRightP020Factor2544 : RatPair2542 :=
  ((((((((((((((20973557087160194868824260538392058 * 10^40
        + 8569192273374692030302711746827435462459) * 10^40
        + 95985723686794335738128106538422114422) * 10^40
        + 4482623210055068483531935537864470854870) * 10^40
        + 1149711071093195801045295454789850117655) * 10^40
        + 570761495986175378702176549702404413007) * 10^40
        + 7119474216302388868528531069219836537830) * 10^40
        + 4862931357708129556015589235728995155074) * 10^40
        + 3757132733065206635308361906417468466104) * 10^40
        + 3746450562176737581104275252668737228847) * 10^40
        + 4052590862813568926346789879872058689933) * 10^40
        + 7505517426912752232191319922902721038933) : ℚ) /
        (((((((((((1013288645451133436803954767831 * 10^40
        + 5128975878830486558111736637716884613235) * 10^40
        + 693135698078575294089659485286524657953) * 10^40
        + 8598939272833644661908955275173715701687) * 10^40
        + 714594779878596193442986282785652359484) * 10^40
        + 300899553130102593146288076585754159760) * 10^40
        + 5499278979287144839022338731288488694115) * 10^40
        + 3291116050439711769841057220261365118287) * 10^40
        + 8399549889652435890144786376173940168721) * 10^40
        + 9397009145700471050250385178273150525855) * 10^40
        + 7723037271703397116784437830417113423740) * 10^40
        + 4210418361928870528464742864291090137088)),
    ((((((((((1342411201314016427417 * 10^40
        + 5232296283454072840338056192185411092693) * 10^40
        + 9662468865815890912651682055958913850561) * 10^40
        + 4685695980085791416994215918491106731058) * 10^40
        + 990664485890165993532403688573099372553) * 10^40
        + 4663528697399577471939227194371955333331) * 10^40
        + 6038037957640222204678006914409300853920) * 10^40
        + 3637358820545485974793704336746659572461) * 10^40
        + 6361413218523394645261723965444032318501) : ℚ) /
        ((((((((7448241345306636 * 10^40
        + 6390773216723008596909898155167170356968) * 10^40
        + 6291174109524313868208460984210380276598) * 10^40
        + 1125419658117597797883113649088579286046) * 10^40
        + 2145274272831709291147016581503651004385) * 10^40
        + 9009680313877059770261832187331744395224) * 10^40
        + 6123777962052708001347447341015309478907) * 10^40
        + 8020156498838405906523147705038949915043) * 10^40
        + 1090680033969852691879303904756651524096)))

theorem endpointRightP020BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP020Center2544‖ ≤ endpointRightP020Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP020Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP020Input2544]
  have hc : (compactExp2542 endpointRightP020Input2544 6).1 = endpointRightP020Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP020Input2544 6).2 : ℝ) = endpointRightP020Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP020Input2544 6).2 =
        ((11638332541593 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [endpointRightP020Error2544]
  have h := compactExp_error2542 endpointRightP020Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP020Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP020Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP020DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP020Factor2544 * embedPair2542 endpointRightP020Center2544‖ ≤
      (pairMagnitude2542 endpointRightP020Factor2544 : ℝ) * endpointRightP020Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP020Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP020Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP020BaseError2544
    (embedPair_magnitude2542 endpointRightP020Factor2544)

def endpointRightP021Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-175708939706778788195515227) : ℚ) /
        461168601842738790400000000))

def endpointRightP021Center2544 : RatPair2542 :=
  (((15596467458466339 : ℚ) /
        316912650057057350374175801344),
    ((57912238786266003 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointRightP021Error2544 : ℝ := ((32706087005659 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP021Factor2544 : RatPair2542 :=
  ((((((((((((((23181271189516625625062460501371065 * 10^40
        + 8892877034123037651314899638306007485287) * 10^40
        + 8697377030063780840508463250325809086722) * 10^40
        + 123755547048356771679109304078553970773) * 10^40
        + 6725319129990575555603283963981694282162) * 10^40
        + 1263126442490957855627428511704316573901) * 10^40
        + 2965728942972332226235426232959833797312) * 10^40
        + 4582883813422142565502418802662137325746) * 10^40
        + 3671798352177077449976690390817730386563) * 10^40
        + 1426073559759287377215507391860163142085) * 10^40
        + 9389055672433873420438413183864679555785) * 10^40
        + 677696251472156297537151113734143257749) : ℚ) /
        (((((((((((1013288645451133436803954767831 * 10^40
        + 5128975878830486558111736637716884613235) * 10^40
        + 693135698078575294089659485286524657953) * 10^40
        + 8598939272833644661908955275173715701687) * 10^40
        + 714594779878596193442986282785652359484) * 10^40
        + 300899553130102593146288076585754159760) * 10^40
        + 5499278979287144839022338731288488694115) * 10^40
        + 3291116050439711769841057220261365118287) * 10^40
        + 8399549889652435890144786376173940168721) * 10^40
        + 9397009145700471050250385178273150525855) * 10^40
        + 7723037271703397116784437830417113423740) * 10^40
        + 4210418361928870528464742864291090137088)),
    ((((((((((10919113242562194811346 * 10^40
        + 8570254675406971384356714134019696699739) * 10^40
        + 2595628720363313452586347307457603019069) * 10^40
        + 1231747859859903107142257412677278896157) * 10^40
        + 1952267330048249674123896410922843401667) * 10^40
        + 81636344598355578123655832576371962444) * 10^40
        + 8190789642652083482357590350934418601781) * 10^40
        + 7327919347488888127471427671264342659483) * 10^40
        + 3201888010687705712733707468699123861667) : ℚ) /
        ((((((((52137689417146456 * 10^40
        + 4735412517061060178369287086170192498780) * 10^40
        + 4038218766670197077459226889472661936186) * 10^40
        + 7877937606823184585181795543620055002323) * 10^40
        + 5016919909821965038029116070525557030701) * 10^40
        + 3067762197139418391832825311322210766572) * 10^40
        + 2866445734368956009432131387107166352354) * 10^40
        + 6141095491868841345662033935272649405301) * 10^40
        + 7634760237788968843155127333296560668672)))

theorem endpointRightP021BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP021Center2544‖ ≤ endpointRightP021Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP021Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP021Input2544]
  have hc : (compactExp2542 endpointRightP021Input2544 6).1 = endpointRightP021Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP021Input2544 6).2 : ℝ) = endpointRightP021Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP021Input2544 6).2 =
        ((32706087005659 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP021Error2544]
  have h := compactExp_error2542 endpointRightP021Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP021Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP021Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP021DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP021Factor2544 * embedPair2542 endpointRightP021Center2544‖ ≤
      (pairMagnitude2542 endpointRightP021Factor2544 : ℝ) * endpointRightP021Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP021Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP021Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP021BaseError2544
    (embedPair_magnitude2542 endpointRightP021Factor2544)

def endpointRightP022Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-36020959374381273657830793) : ℚ) /
        92233720368547758080000000))

def endpointRightP022Center2544 : RatPair2542 :=
  (((84311051410122179 : ℚ) /
        1267650600228229401496703205376),
    ((11724792803509099 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointRightP022Error2544 : ℝ := ((22295137333103 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP022Factor2544 : RatPair2542 :=
  ((((((((((((((24354057665949033052013013980904990 * 10^40
        + 4509792339263308319797862251526992369983) * 10^40
        + 1421321928377507483746298226036131898282) * 10^40
        + 685367383764311882056910029420041522038) * 10^40
        + 1515396100132263161237111577669036831468) * 10^40
        + 5057879735935524342553507063018741526481) * 10^40
        + 4683637547107604243200242940389384290475) * 10^40
        + 1266568774999820005846723689143288444903) * 10^40
        + 2783430088684549524631292069492886098385) * 10^40
        + 7520148254513308440848112865479829182065) * 10^40
        + 3236516224992205366468630821748379018392) * 10^40
        + 2097060641119509102382721350354700383461) : ℚ) /
        (((((((((((1013288645451133436803954767831 * 10^40
        + 5128975878830486558111736637716884613235) * 10^40
        + 693135698078575294089659485286524657953) * 10^40
        + 8598939272833644661908955275173715701687) * 10^40
        + 714594779878596193442986282785652359484) * 10^40
        + 300899553130102593146288076585754159760) * 10^40
        + 5499278979287144839022338731288488694115) * 10^40
        + 3291116050439711769841057220261365118287) * 10^40
        + 8399549889652435890144786376173940168721) * 10^40
        + 9397009145700471050250385178273150525855) * 10^40
        + 7723037271703397116784437830417113423740) * 10^40
        + 4210418361928870528464742864291090137088)),
    ((((((((((11758211026764048006223 * 10^40
        + 1772166309603821702714048943271648329688) * 10^40
        + 4577544240626563729449641993969529417290) * 10^40
        + 9445613145285479589713846319044929372333) * 10^40
        + 4726320994295418861497585043977375451889) * 10^40
        + 3830306075113336482266577918041780504509) * 10^40
        + 3468582450226830577312670378337477535954) * 10^40
        + 3501671197891498462925400603224947465661) * 10^40
        + 8105307785123253847163563126071314764405) : ℚ) /
        ((((((((52137689417146456 * 10^40
        + 4735412517061060178369287086170192498780) * 10^40
        + 4038218766670197077459226889472661936186) * 10^40
        + 7877937606823184585181795543620055002323) * 10^40
        + 5016919909821965038029116070525557030701) * 10^40
        + 3067762197139418391832825311322210766572) * 10^40
        + 2866445734368956009432131387107166352354) * 10^40
        + 6141095491868841345662033935272649405301) * 10^40
        + 7634760237788968843155127333296560668672)))

theorem endpointRightP022BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP022Center2544‖ ≤ endpointRightP022Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP022Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP022Input2544]
  have hc : (compactExp2542 endpointRightP022Input2544 6).1 = endpointRightP022Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP022Input2544 6).2 : ℝ) = endpointRightP022Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP022Input2544 6).2 =
        ((22295137333103 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP022Error2544]
  have h := compactExp_error2542 endpointRightP022Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP022Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP022Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP022DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP022Factor2544 * embedPair2542 endpointRightP022Center2544‖ ≤
      (pairMagnitude2542 endpointRightP022Factor2544 : ℝ) * endpointRightP022Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP022Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP022Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP022BaseError2544
    (embedPair_magnitude2542 endpointRightP022Factor2544)

def endpointRightP023Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-96389434963244923910950893) : ℚ) /
        230584300921369395200000000))

def endpointRightP023Center2544 : RatPair2542 :=
  ((((-1061566622896829) : ℚ) /
        316912650057057350374175801344),
    (((-42508215020887159) : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointRightP023Error2544 : ℝ := ((1415403270485 : ℝ) /
        (4 * 10^40
        + 3556142965880123323311949751266331066368))

def endpointRightP023Factor2544 : RatPair2542 :=
  ((((((((((((((6974409398937863670955403897443443 * 10^40
        + 8776141645856577033297665812505045457435) * 10^40
        + 2787797495895234563347363555780644897094) * 10^40
        + 174655207334633096386378199308139416835) * 10^40
        + 3483692724327720035349037626014874447174) * 10^40
        + 2576322550504321365560051408136436547820) * 10^40
        + 9374414148495834272767125474504608285882) * 10^40
        + 7950072836424496886802544212665160678392) * 10^40
        + 2792820624689760118699809499339673189663) * 10^40
        + 9124914483372446538515514301360807803392) * 10^40
        + 9802439453892240574424887935725697036457) * 10^40
        + 7726933651887156632438032879333221345637) : ℚ) /
        (((((((((((253322161362783359200988691957 * 10^40
        + 8782243969707621639527934159429221153308) * 10^40
        + 7673283924519643823522414871321631164488) * 10^40
        + 4649734818208411165477238818793428925421) * 10^40
        + 7678648694969649048360746570696413089871) * 10^40
        + 75224888282525648286572019146438539940) * 10^40
        + 1374819744821786209755584682822122173528) * 10^40
        + 8322779012609927942460264305065341279571) * 10^40
        + 9599887472413108972536196594043485042180) * 10^40
        + 4849252286425117762562596294568287631463) * 10^40
        + 9430759317925849279196109457604278355935) * 10^40
        + 1052604590482217632116185716072772534272)),
    ((((((((((1801989790577379023277 * 10^40
        + 4566678855678928528078027411012768394661) * 10^40
        + 9395247323204753920276026284236200661528) * 10^40
        + 3597315518875842356541765058119039286191) * 10^40
        + 5117762362737691529515604721499827444645) * 10^40
        + 314715639922812416268149838598393857360) * 10^40
        + 8072410044638261384831202524375264098331) * 10^40
        + 9207085307688052765732286896112297620634) * 10^40
        + 8260132283105204535645841571783332058421) : ℚ) /
        ((((((((6517211177143307 * 10^40
        + 591926564632632522296160885771274062347) * 10^40
        + 5504777345833774634682403361184082742023) * 10^40
        + 3484742200852898073147724442952506875290) * 10^40
        + 4377114988727745629753639508815694628837) * 10^40
        + 6633470274642427298979103163915276345821) * 10^40
        + 5358305716796119501179016423388395794044) * 10^40
        + 3267636936483605168207754241909081175662) * 10^40
        + 7204345029723621105394390916662070083584)))

theorem endpointRightP023BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP023Center2544‖ ≤ endpointRightP023Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP023Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP023Input2544]
  have hc : (compactExp2542 endpointRightP023Input2544 6).1 = endpointRightP023Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP023Input2544 6).2 : ℝ) = endpointRightP023Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP023Input2544 6).2 =
        ((1415403270485 : ℚ) /
        (4 * 10^40
        + 3556142965880123323311949751266331066368)) := by cbv
    rw [hq]
    norm_num [endpointRightP023Error2544]
  have h := compactExp_error2542 endpointRightP023Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP023Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP023Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP023DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP023Factor2544 * embedPair2542 endpointRightP023Center2544‖ ≤
      (pairMagnitude2542 endpointRightP023Factor2544 : ℝ) * endpointRightP023Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP023Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP023Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP023BaseError2544
    (embedPair_magnitude2542 endpointRightP023Factor2544)

def endpointRightP024Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-99301680327601486613435187) : ℚ) /
        230584300921369395200000000))

def endpointRightP024Center2544 : RatPair2542 :=
  ((((-64410169773694499) : ℚ) /
        1267650600228229401496703205376),
    (((-13913020398823667) : ℚ) /
        316912650057057350374175801344))

noncomputable def endpointRightP024Error2544 : ℝ := ((48200538787461 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP024Factor2544 : RatPair2542 :=
  ((((((((((((((7401727940565333713193279620500537 * 10^40
        + 4977239155266387733090734364739816397405) * 10^40
        + 4250881450402546820229590888221128457341) * 10^40
        + 8121670285201372585180562184322877714734) * 10^40
        + 6028866421907050581603314615981271707281) * 10^40
        + 3447913093883735825445939323881779792018) * 10^40
        + 9929973342804588020526245864089032775155) * 10^40
        + 915045371076786841718593151582852079001) * 10^40
        + 6088699164529327693994597576302688374987) * 10^40
        + 9883644952510077528811566814949580611514) * 10^40
        + 411842370225221563135546167550223953024) * 10^40
        + 1290259720159306354106860786217272439077) : ℚ) /
        (((((((((((253322161362783359200988691957 * 10^40
        + 8782243969707621639527934159429221153308) * 10^40
        + 7673283924519643823522414871321631164488) * 10^40
        + 4649734818208411165477238818793428925421) * 10^40
        + 7678648694969649048360746570696413089871) * 10^40
        + 75224888282525648286572019146438539940) * 10^40
        + 1374819744821786209755584682822122173528) * 10^40
        + 8322779012609927942460264305065341279571) * 10^40
        + 9599887472413108972536196594043485042180) * 10^40
        + 4849252286425117762562596294568287631463) * 10^40
        + 9430759317925849279196109457604278355935) * 10^40
        + 1052604590482217632116185716072772534272)),
    ((((((((((1970124126194684458687 * 10^40
        + 6323706833000656766980456960797232400643) * 10^40
        + 3186066801847069937407162373363561529314) * 10^40
        + 6737772810479747428277630226780698320694) * 10^40
        + 6448820420365059109660064120621678083773) * 10^40
        + 9812686394312495466458299767444396460163) * 10^40
        + 3746768428995040519196046568414953967818) * 10^40
        + 2245913577705058648251692478127418261258) * 10^40
        + 605131458097555127031369992245030561579) : ℚ) /
        ((((((((6517211177143307 * 10^40
        + 591926564632632522296160885771274062347) * 10^40
        + 5504777345833774634682403361184082742023) * 10^40
        + 3484742200852898073147724442952506875290) * 10^40
        + 4377114988727745629753639508815694628837) * 10^40
        + 6633470274642427298979103163915276345821) * 10^40
        + 5358305716796119501179016423388395794044) * 10^40
        + 3267636936483605168207754241909081175662) * 10^40
        + 7204345029723621105394390916662070083584)))

theorem endpointRightP024BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP024Center2544‖ ≤ endpointRightP024Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP024Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP024Input2544]
  have hc : (compactExp2542 endpointRightP024Input2544 6).1 = endpointRightP024Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP024Input2544 6).2 : ℝ) = endpointRightP024Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP024Input2544 6).2 =
        ((48200538787461 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP024Error2544]
  have h := compactExp_error2542 endpointRightP024Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP024Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP024Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP024DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP024Factor2544 * embedPair2542 endpointRightP024Center2544‖ ≤
      (pairMagnitude2542 endpointRightP024Factor2544 : ℝ) * endpointRightP024Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP024Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP024Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP024BaseError2544
    (embedPair_magnitude2542 endpointRightP024Factor2544)

def endpointRightP025Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-3217284425888024839257393) : ℚ) /
        7205759403792793600000000))

def endpointRightP025Center2544 : RatPair2542 :=
  ((((-40649034076960087) : ℚ) /
        633825300114114700748351602688),
    ((12613963201607519 : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointRightP025Error2544 : ℝ := ((23965893802661 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def endpointRightP025Factor2544 : RatPair2542 :=
  ((((((((((((((7769021016077651452367145080931 * 10^40
        + 2922929974381874345848123547445399979931) * 10^40
        + 8283256757269067270799791848020474667191) * 10^40
        + 6869540140816563875806254788047839142216) * 10^40
        + 9686755544215475852306998036689111486371) * 10^40
        + 6324581813026977167686755174751958161610) * 10^40
        + 2679860231445485138477475666458074437386) * 10^40
        + 329301220186850401505260312202518673599) * 10^40
        + 9425303999300922853755717369270969373130) * 10^40
        + 9077449862950530252063595176455056661714) * 10^40
        + 5841598435992790382974847184866307529682) * 10^40
        + 988748497970304968961794579183970041469) : ℚ) /
        (((((((((((247384923205843124219715519 * 10^40
        + 4901154535126667599257351498202567598782) * 10^40
        + 5280930941332538714671408608272775030434) * 10^40
        + 707665756658406651528786366033977957934) * 10^40
        + 9821951805366181297898789791572945715908) * 10^40
        + 771557836804963403953404855487447693886) * 10^40
        + 6602905097407052525595464438166818478685) * 10^40
        + 867502713879501882756308851860415372343) * 10^40
        + 3319921765109778426730992379486370590861) * 10^40
        + 5043798097935962029065002535443914343390) * 10^40
        + 1015069100896411962186714950642191678081) * 10^40
        + 9678762309170392790656363462613352316928)),
    ((((((((((1367257738026452 * 10^40
        + 7095576007631870323377636494431908274506) * 10^40
        + 5575003818108830880161969090104833140968) * 10^40
        + 5791611439897139293982476280836274094827) * 10^40
        + 9447116629137920870067699864991409680841) * 10^40
        + 7437517671032446307035937350072899147727) * 10^40
        + 3230671734251063873103769833666040456193) * 10^40
        + 403961244049796083778002780365365665163) * 10^40
        + 8382451128582985791137272703418262261857) : ℚ) /
        ((((((((4058969413 * 10^40
        + 3794711734648141437535202522222331001919) * 10^40
        + 5322138263797274739027768929868961993833) * 10^40
        + 4201257501558390000260379182605007219902) * 10^40
        + 7394137870393084298111665533347310476930) * 10^40
        + 3481978830435787678887378290357419331002) * 10^40
        + 5870321068778971019585746409523741049253) * 10^40
        + 9972075337086540679062928621100128740010) * 10^40
        + 8964337534593873143797025342289464000512)))

theorem endpointRightP025BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP025Center2544‖ ≤ endpointRightP025Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP025Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP025Input2544]
  have hc : (compactExp2542 endpointRightP025Input2544 6).1 = endpointRightP025Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP025Input2544 6).2 : ℝ) = endpointRightP025Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP025Input2544 6).2 =
        ((23965893802661 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [endpointRightP025Error2544]
  have h := compactExp_error2542 endpointRightP025Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP025Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP025Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP025DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP025Factor2544 * embedPair2542 endpointRightP025Center2544‖ ≤
      (pairMagnitude2542 endpointRightP025Factor2544 : ℝ) * endpointRightP025Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP025Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP025Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP025BaseError2544
    (embedPair_magnitude2542 endpointRightP025Factor2544)

def endpointRightP026Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-6667794114411367544987277) : ℚ) /
        14411518807585587200000000))

def endpointRightP026Center2544 : RatPair2542 :=
  ((((-19751936632082831) : ℚ) /
        1267650600228229401496703205376),
    ((82799064943075705 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointRightP026Error2544 : ℝ := ((15008208047897 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

def endpointRightP026Factor2544 : RatPair2542 :=
  ((((((((((((((33367362583253764682757442913114 * 10^40
        + 4315869700564404413654043237121656068015) * 10^40
        + 2851013403636944854779302722460016299440) * 10^40
        + 7489194381437661618009910357393533544660) * 10^40
        + 6818510858849144899690243377099325046019) * 10^40
        + 9402971576148321798248975417714994111802) * 10^40
        + 9124606697871071365458252634463911801526) * 10^40
        + 8408207955650493451232104280082836228178) * 10^40
        + 3972283091287650264631114601451716064125) * 10^40
        + 3359586210296870232086095661412485543259) * 10^40
        + 2445764565929673444933294412603883225901) * 10^40
        + 7760639854175860329036826604623536269477) : ℚ) /
        (((((((((((989539692823372496878862077 * 10^40
        + 9604618140506670397029405992810270395130) * 10^40
        + 1123723765330154858685634433091100121736) * 10^40
        + 2830663026633626606115145464135911831739) * 10^40
        + 9287807221464725191595159166291782863632) * 10^40
        + 3086231347219853615813619421949790775546) * 10^40
        + 6411620389628210102381857752667273914740) * 10^40
        + 3470010855518007531025235407441661489373) * 10^40
        + 3279687060439113706923969517945482363446) * 10^40
        + 175192391743848116260010141775657373560) * 10^40
        + 4060276403585647848746859802568766712327) * 10^40
        + 8715049236681571162625453850453409267712)),
    ((((((((((596324568417407217 * 10^40
        + 4257149143922547078600603681625891352005) * 10^40
        + 2934087657307929867921946801328682229670) * 10^40
        + 2077154779189796657538915892006256402892) * 10^40
        + 751294256294364404894449767368745287250) * 10^40
        + 2600653825092800673708550559946655860722) * 10^40
        + 6289838024526274456641242619268214598975) * 10^40
        + 6430809875265233147401487111378587534806) * 10^40
        + 6401399938240563079925754434947907350549) : ℚ) /
        ((((((((1591116010044 * 10^40
        + 7526999982071443513799388711153752752456) * 10^40
        + 6278199408531697698885420508633101582700) * 10^40
        + 6892940610888880102068639581162830201873) * 10^40
        + 8502045194089044859772889072145706956696) * 10^40
        + 4935701530828770123852289820108377753014) * 10^40
        + 1165858961356639677612592533306491307566) * 10^40
        + 9053532137923946192668019471250466084271) * 10^40
        + 4020313560798272368433934177469888200704)))

theorem endpointRightP026BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP026Center2544‖ ≤ endpointRightP026Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP026Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP026Input2544]
  have hc : (compactExp2542 endpointRightP026Input2544 6).1 = endpointRightP026Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP026Input2544 6).2 : ℝ) = endpointRightP026Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP026Input2544 6).2 =
        ((15008208047897 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [endpointRightP026Error2544]
  have h := compactExp_error2542 endpointRightP026Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP026Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP026Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP026DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP026Factor2544 * embedPair2542 endpointRightP026Center2544‖ ≤
      (pairMagnitude2542 endpointRightP026Factor2544 : ℝ) * endpointRightP026Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP026Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP026Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP026BaseError2544
    (embedPair_magnitude2542 endpointRightP026Factor2544)

def endpointRightP027Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-14008691541762368185839267) : ℚ) /
        28823037615171174400000000))

def endpointRightP027Center2544 : RatPair2542 :=
  (((10131872598729435 : ℚ) /
        158456325028528675187087900672),
    ((6499587704832155 : ℚ) /
        316912650057057350374175801344))

noncomputable def endpointRightP027Error2544 : ℝ := ((2676132222099 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

def endpointRightP027Factor2544 : RatPair2542 :=
  ((((((((((((((147270142966747326645431481384080 * 10^40
        + 8491147652659765470273982514593479670057) * 10^40
        + 9468335130617223479948215175637467443944) * 10^40
        + 6365844776163954663795039692803511433960) * 10^40
        + 2864869838931353740676058505959023385990) * 10^40
        + 3863958975041492059043582937118636448277) * 10^40
        + 1191711036900540584062080064983386643281) * 10^40
        + 5440242736529694356315469290370104662942) * 10^40
        + 2122070365527480223700805407427243500541) * 10^40
        + 1216194700709205744516134743503465137688) * 10^40
        + 5202940324726210594873216567058140228264) * 10^40
        + 6997355451443915817609343051185198405189) : ℚ) /
        (((((((((((3958158771293489987515448311 * 10^40
        + 8418472562026681588117623971241081580520) * 10^40
        + 4494895061320619434742537732364400486945) * 10^40
        + 1322652106534506424460581856543647326959) * 10^40
        + 7151228885858900766380636665167131454529) * 10^40
        + 2344925388879414463254477687799163102186) * 10^40
        + 5646481558512840409527431010669095658961) * 10^40
        + 3880043422072030124100941629766645957493) * 10^40
        + 3118748241756454827695878071781929453784) * 10^40
        + 700769566975392465040040567102629494241) * 10^40
        + 6241105614342591394987439210275066849311) * 10^40
        + 4860196946726284650501815401813637070848)),
    ((((((((((5529368986398606227 * 10^40
        + 8515200232837881538902765433692158181297) * 10^40
        + 2077995736004421377989291299622253542902) * 10^40
        + 2199321500320561273229747450652914180422) * 10^40
        + 6188389146152846086619434054314644759335) * 10^40
        + 4110713512695011684826354249107193475765) * 10^40
        + 9622252109337854953156130384670059026721) * 10^40
        + 7903799755698065245517480687774497121439) * 10^40
        + 6505221173706197690363641899661017427707) : ℚ) /
        ((((((((12728928080358 * 10^40
        + 215999856571548110395109689230022019653) * 10^40
        + 225595268253581591083364069064812661605) * 10^40
        + 5143524887111040816549116649302641614990) * 10^40
        + 8016361552712358878183112577165655653571) * 10^40
        + 9485612246630160990818318560867022024112) * 10^40
        + 9326871690853117420900740266451930460535) * 10^40
        + 2428257103391569541344155770003728674171) * 10^40
        + 2162508486386178947471473419759105605632)))

theorem endpointRightP027BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP027Center2544‖ ≤ endpointRightP027Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP027Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP027Input2544]
  have hc : (compactExp2542 endpointRightP027Input2544 6).1 = endpointRightP027Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP027Input2544 6).2 : ℝ) = endpointRightP027Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP027Input2544 6).2 =
        ((2676132222099 : ℚ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736)) := by cbv
    rw [hq]
    norm_num [endpointRightP027Error2544]
  have h := compactExp_error2542 endpointRightP027Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP027Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP027Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP027DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP027Factor2544 * embedPair2542 endpointRightP027Center2544‖ ≤
      (pairMagnitude2542 endpointRightP027Factor2544 : ℝ) * endpointRightP027Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP027Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP027Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP027BaseError2544
    (embedPair_magnitude2542 endpointRightP027Factor2544)

def endpointRightP028Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-57100729615769193262781367) : ℚ) /
        115292150460684697600000000))

def endpointRightP028Center2544 : RatPair2542 :=
  (((81775618486861615 : ℚ) /
        1267650600228229401496703205376),
    (((-11817067923735785) : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointRightP028Error2544 : ℝ := ((42721615969753 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP028Factor2544 : RatPair2542 :=
  ((((((((((((((2446748400711466966295912399223699 * 10^40
        + 7046350702172029791813431949484148132937) * 10^40
        + 7834222741485874993945899404804322582893) * 10^40
        + 2918125678675887460525068689910950262875) * 10^40
        + 3057657980729740246661928488687564288106) * 10^40
        + 2798319051084033884866577202135188887574) * 10^40
        + 316271274016389374527572057333956250960) * 10^40
        + 1082381635574873883856832187797656737460) * 10^40
        + 5215213791833449187828623548295680281620) * 10^40
        + 6321866891602032060329724444314951195737) * 10^40
        + 9354810510637310715721407127214521213952) * 10^40
        + 9043380673532175190018763132221674358829) : ℚ) /
        (((((((((((63330540340695839800247172989 * 10^40
        + 4695560992426905409881983539857305288327) * 10^40
        + 1918320981129910955880603717830407791122) * 10^40
        + 1162433704552102791369309704698357231355) * 10^40
        + 4419662173742412262090186642674103272467) * 10^40
        + 7518806222070631412071643004786609634985) * 10^40
        + 343704936205446552438896170705530543382) * 10^40
        + 2080694753152481985615066076266335319892) * 10^40
        + 9899971868103277243134049148510871260545) * 10^40
        + 1212313071606279440640649073642071907865) * 10^40
        + 9857689829481462319799027364401069588983) * 10^40
        + 7763151147620554408029046429018193133568)),
    ((((((((((374445637809384072435 * 10^40
        + 9653238878593578572181403979091714260695) * 10^40
        + 8121768133584832811089490982362063371556) * 10^40
        + 1600260127618106771173166311186634947518) * 10^40
        + 4092459127958171184417669452397075750957) * 10^40
        + 2006898948985067565996319926363469666005) * 10^40
        + 5642578859367979966784872850825270172123) * 10^40
        + 2729008512716492625741632694794303645291) * 10^40
        + 3609469357409827456170134308928043633767) : ℚ) /
        ((((((((814651397142913 * 10^40
        + 3823990820579079065287020110721409257793) * 10^40
        + 4438097168229221829335300420148010342752) * 10^40
        + 9185592775106612259143465555369063359411) * 10^40
        + 3047139373590968203719204938601961828604) * 10^40
        + 7079183784330303412372387895489409543227) * 10^40
        + 6919788214599514937647377052923549474255) * 10^40
        + 5408454617060450646025969280238635146957) * 10^40
        + 8400543128715452638174298864582758760448)))

theorem endpointRightP028BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP028Center2544‖ ≤ endpointRightP028Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP028Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP028Input2544]
  have hc : (compactExp2542 endpointRightP028Input2544 6).1 = endpointRightP028Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP028Input2544 6).2 : ℝ) = endpointRightP028Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP028Input2544 6).2 =
        ((42721615969753 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP028Error2544]
  have h := compactExp_error2542 endpointRightP028Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP028Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP028Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP028DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP028Factor2544 * embedPair2542 endpointRightP028Center2544‖ ≤
      (pairMagnitude2542 endpointRightP028Factor2544 : ℝ) * endpointRightP028Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP028Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP028Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP028BaseError2544
    (embedPair_magnitude2542 endpointRightP028Factor2544)

def endpointRightP029Input2544 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-58723590526748964315538539) : ℚ) /
        115292150460684697600000000))

def endpointRightP029Center2544 : RatPair2542 :=
  (((8062714586698767 : ℚ) /
        316912650057057350374175801344),
    (((-39388152698687339) : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointRightP029Error2544 : ℝ := ((60793450727817 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointRightP029Factor2544 : RatPair2542 :=
  ((((((((((((((2587688225074083449614153543769041 * 10^40
        + 649503461969240349848165947489885270410) * 10^40
        + 9636890909881584303045686501950081331356) * 10^40
        + 117752428682619133864463024802220411366) * 10^40
        + 1610683035828561240434355210532389571460) * 10^40
        + 9279290604335373250098416427243637761018) * 10^40
        + 4118101430147417796939758998464041269442) * 10^40
        + 3916440928152264826735009622842141418126) * 10^40
        + 9053627522115053627539715010886085774985) * 10^40
        + 4499341042693423247773591176639336625286) * 10^40
        + 5003999457677686881984377225001048410686) * 10^40
        + 3970174748822299660911892524359983042933) : ℚ) /
        (((((((((((63330540340695839800247172989 * 10^40
        + 4695560992426905409881983539857305288327) * 10^40
        + 1918320981129910955880603717830407791122) * 10^40
        + 1162433704552102791369309704698357231355) * 10^40
        + 4419662173742412262090186642674103272467) * 10^40
        + 7518806222070631412071643004786609634985) * 10^40
        + 343704936205446552438896170705530543382) * 10^40
        + 2080694753152481985615066076266335319892) * 10^40
        + 9899971868103277243134049148510871260545) * 10^40
        + 1212313071606279440640649073642071907865) * 10^40
        + 9857689829481462319799027364401069588983) * 10^40
        + 7763151147620554408029046429018193133568)),
    ((((((((((407262637481785616654 * 10^40
        + 803572410559186975397923365921673398096) * 10^40
        + 5496219743297368986070179782380718042609) * 10^40
        + 9850750928490774536276305747193573271592) * 10^40
        + 8847644935438380540282268609600822192789) * 10^40
        + 2650526367738385153855850742352951245297) * 10^40
        + 5155884364227387372000421795140928453171) * 10^40
        + 682168448892984602228456590592061825588) * 10^40
        + 1503366923379228503661489338936011291987) : ℚ) /
        ((((((((814651397142913 * 10^40
        + 3823990820579079065287020110721409257793) * 10^40
        + 4438097168229221829335300420148010342752) * 10^40
        + 9185592775106612259143465555369063359411) * 10^40
        + 3047139373590968203719204938601961828604) * 10^40
        + 7079183784330303412372387895489409543227) * 10^40
        + 6919788214599514937647377052923549474255) * 10^40
        + 5408454617060450646025969280238635146957) * 10^40
        + 8400543128715452638174298864582758760448)))

theorem endpointRightP029BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP029Center2544‖ ≤ endpointRightP029Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointRightP029Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointRightP029Input2544]
  have hc : (compactExp2542 endpointRightP029Input2544 6).1 = endpointRightP029Center2544 := by
      cbv
  have he : ((compactExp2542 endpointRightP029Input2544 6).2 : ℝ) = endpointRightP029Error2544 :=
      by
    have hq : (compactExp2542 endpointRightP029Input2544 6).2 =
        ((60793450727817 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointRightP029Error2544]
  have h := compactExp_error2542 endpointRightP029Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      endpointRightPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          endpointRightP029Input2544) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointRightPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointRightP029Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointRightP029DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ endpointRightPosition2544 -
      embedPair2542 endpointRightP029Factor2544 * embedPair2542 endpointRightP029Center2544‖ ≤
      (pairMagnitude2542 endpointRightP029Factor2544 : ℝ) * endpointRightP029Error2544 := by
  have hx : |endpointRightPosition2544| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [endpointRightPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) endpointRightPosition2544 = embedPair2542
          endpointRightP029Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointRightPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointRightP029Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointRightP029BaseError2544
    (embedPair_magnitude2542 endpointRightP029Factor2544)

theorem endpointRight_grid2544 :
    -stripRadius2303 + (5441 : ℝ)*(2*stripRadius2303/10240) = endpointRightPosition2544 := by
  norm_num [stripRadius2303, endpointRightPosition2544]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.endpointRightP000DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP001DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP002DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP003DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP004DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP005DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP006DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP007DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP008DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP009DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP010DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP011DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP012DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP013DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP014DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP015DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP016DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP017DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP018DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP019DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP020DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP021DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP022DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP023DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP024DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP025DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP026DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP027DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP028DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointRightP029DerivativeError2544
