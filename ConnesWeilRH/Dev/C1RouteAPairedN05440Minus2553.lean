import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def pairedN05440MinusPosition2553 : ℝ := ((65536001 : ℝ) /
        160000000)

theorem pairedN05440MinusZero2553 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def pairedN05440MinusP000Input2553 : RatPair2542 := ((((-((33 * 10^40
        + 1290059165262451568566309402597100238574) * 10^40
        + 58407946859350584659335737862549108307)) : ℚ) /
        ((68 * 10^40
        + 4108646130446117391380318820003814069094) * 10^40
        + 5827290179342624543465749633167360000000)),
    (((-362039942185747774262029) : ℚ) /
        1441151880758558720000000))

def pairedN05440MinusP000Center2553 : RatPair2542 := ((((-47240625468716384282800085644730723) :
    ℚ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((18314198851726989519620350327925883 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN05440MinusP000Factor2553 : RatPair2542 := ((((((((((((((306295305258473372642551 *
    10^40
        + 5864965863056604601143881013329900641267) * 10^40
        + 3638708552596540269309049322712627316573) * 10^40
        + 81256348055299971110645095409241973891) * 10^40
        + 829711657811043310375945475222360651669) * 10^40
        + 4691707501259150943489084811864319225831) * 10^40
        + 1914858324360390001667955975392773375677) * 10^40
        + 9337900435489880887390360098192208286952) * 10^40
        + 1338674696086928004908192796905471788080) * 10^40
        + 2583514468868361212123693324029937165397) * 10^40
        + 3986934343698380368367975660235669396989) * 10^40
        + 8227799793751239275391138047145703254321) : ℚ) /
        (((((((((((14858812902724391177 * 10^40
        + 3914644235504745007909735001169384381007) * 10^40
        + 1844881240089933603887962341860643523460) * 10^40
        + 5480977614990707061369432804462859026007) * 10^40
        + 8822666597448527724237166447268410396721) * 10^40
        + 9946908985667864059233175685416859448789) * 10^40
        + 1772526151343142426262489548722775448399) * 10^40
        + 9151926082066865041545700436063354319065) * 10^40
        + 5494842377964677056256491283406448055962) * 10^40
        + 2599856225108555368746340549975694519596) * 10^40
        + 1687676960230766039095737209285420201601) * 10^40
        + 374417720559226663405210625814208446464)),
    ((((((((((20616211940963 * 10^40
        + 3820592566541507216316089821956033512235) * 10^40
        + 3971051123462927834952014849410735176405) * 10^40
        + 8761144747677447162929624294790347701962) * 10^40
        + 9091914154155358078155008955462390549228) * 10^40
        + 4552644576094315074388099601568193115334) * 10^40
        + 5335519149120184911239944464737278537472) * 10^40
        + 1737190214010175595793693268137162485252) * 10^40
        + 3570029976468945139801961853403903646437) : ℚ) /
        ((((((((347064262 * 10^40
        + 7567007173867870115569880478991789728245) * 10^40
        + 6760705912975754929199920984881470359745) * 10^40
        + 8467471475072895805471424614794166971503) * 10^40
        + 5061188735027225722550733722517957416696) * 10^40
        + 1560718208491165579514798473885035339480) * 10^40
        + 5092715512281319322962596680044233098605) * 10^40
        + 7399419053698630897699024853701654451303) * 10^40
        + 1296852544043064379504336483176836759552)))

noncomputable def pairedN05440MinusP000Error2553 : ℝ := ((28853873385704556118854613093727 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN05440MinusP000BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP000Center2553‖ ≤ pairedN05440MinusP000Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP000Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP000Input2553]
  have hs : compactExp2547 pairedN05440MinusP000Input2553 6 =
      (pairedN05440MinusP000Center2553, ((28853873385704556118854613093727 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP000Input2553 6).2 : ℝ) =
      pairedN05440MinusP000Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP000Error2553]
  have h := compactExp_error2547 pairedN05440MinusP000Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP000Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP000Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP000DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP000Factor2553 * embedPair2542
          pairedN05440MinusP000Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP000Factor2553 : ℝ) * pairedN05440MinusP000Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
      (storedWidth ⟨0, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP000Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP000Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨0, by omega⟩) (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP000BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP000Factor2553)

def pairedN05440MinusP001Input2553 : RatPair2542 := ((((-(424417575296239745199154000011321411027
    *
    10^40
        + 7930567342231968039510139851389362216201)) : ℚ) /
        (886210261626655755083735189233369746668 * 10^40
        + 3797746372915947800471746154516480000000)),
    (((-362039942185747774262029) : ℚ) /
        1441151880758558720000000))

def pairedN05440MinusP001Center2553 : RatPair2542 := ((((-8317493327841034999117566362833513) : ℚ)
    /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((12898070272576534656216409493599237 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def pairedN05440MinusP001Factor2553 : RatPair2542 := ((((((((((((((32618 * 10^40
        + 9098985434438195502106254595705247247580) * 10^40
        + 305007555312133159809652257417641124645) * 10^40
        + 8655948805817173502610147657376655835830) * 10^40
        + 9255221622332696287551675849790681899612) * 10^40
        + 7863580881725770916458367309400701258027) * 10^40
        + 2194785642848380823005131859245789063956) * 10^40
        + 4170095306843312742589326402935545600382) * 10^40
        + 1313345418819061171179796103289975385201) * 10^40
        + 4246434076830877665977307697415061015332) * 10^40
        + 4238386072248157126371390644884195514443) * 10^40
        + 3266275224855604617953429213442655550027) : ℚ) /
        (((((((((((2 * 10^40
        + 6007015790623434321211705357225853298659) * 10^40
        + 5244309791880134632661648372165206209940) * 10^40
        + 7301828850428918255361284108459092636093) * 10^40
        + 1226300862384552218948950305665763280773) * 10^40
        + 9072833017840401717311748030006024115559) * 10^40
        + 3726506219630336917114704808339177444525) * 10^40
        + 2790550058477535009026062837619231103736) * 10^40
        + 231996267424212097760827186486221515959) * 10^40
        + 9749885156354439786172341898442861436722) * 10^40
        + 4243267759735663233166921871258977872267) * 10^40
        + 6097643426167772543569762558233718816768)),
    ((((((((((58 * 10^40
        + 9226542299209009552002194153053804971322) * 10^40
        + 9580249598575101652981540994130364205753) * 10^40
        + 6542135702970205463573117960516302494299) * 10^40
        + 8177961058683912030980226038399839720681) * 10^40
        + 475816770819982703556238108377069728585) * 10^40
        + 5161012851668207753346704415675416568180) * 10^40
        + 9888457375478795470238692217090163261280) * 10^40
        + 8582772823676356686982296522309448794037) : ℚ) /
        (((((((9773647633404747718875879981514886715 * 10^40
        + 8603685856436692169309093239966098853839) * 10^40
        + 7656999226396869036009767818903745503705) * 10^40
        + 3313684529912668061111093298939113317831) * 10^40
        + 5706621653075060341119322492496743759866) * 10^40
        + 5852330712503776286664116254491248412679) * 10^40
        + 2012987523270991628535820178817129352001) * 10^40
        + 4667580454374216993044141776915138609152)))

noncomputable def pairedN05440MinusP001Error2553 : ℝ := ((20212333422939156095014085369811 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem pairedN05440MinusP001BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP001Center2553‖ ≤ pairedN05440MinusP001Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP001Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP001Input2553]
  have hs : compactExp2547 pairedN05440MinusP001Input2553 6 =
      (pairedN05440MinusP001Center2553, ((20212333422939156095014085369811 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP001Input2553 6).2 : ℝ) =
      pairedN05440MinusP001Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP001Error2553]
  have h := compactExp_error2547 pairedN05440MinusP001Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP001Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP001Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP001DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP001Factor2553 * embedPair2542
          pairedN05440MinusP001Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP001Factor2553 : ℝ) * pairedN05440MinusP001Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP001Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP001Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP001BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP001Factor2553)

def pairedN05440MinusP002Input2553 : RatPair2542 := ((((-((1 * 10^40
        + 1089503407207950123102807654511471321419) * 10^40
        + 1225280447109717097189589041083555224841)) : ℚ) /
        ((2 * 10^40
        + 3288003241060619496441480162260487009338) * 10^40
        + 6963595085534041865672938472263680000000)),
    ((362039942185747774262029 : ℚ) /
        1441151880758558720000000))

def pairedN05440MinusP002Center2553 : RatPair2542 := ((((-19802477832083935096949159204845913) :
    ℚ)
    /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-30708019902392295161306432703451507) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN05440MinusP002Factor2553 : RatPair2542 := ((((((((((((((7280806700328 * 10^40
        + 7169886171648797800447546252192712791730) * 10^40
        + 9165197242138216615751117063804581573752) * 10^40
        + 1732566575677378357518701827187259258828) * 10^40
        + 555462991866968129173196896412145304015) * 10^40
        + 9846613401392893007297048794458709761181) * 10^40
        + 4008574733599032235009637014535038872356) * 10^40
        + 1003534593688196259299260069438087397054) * 10^40
        + 3020871322835218362134880252617312809240) * 10^40
        + 9617161284620361257518465517589827834668) * 10^40
        + 1592664720079930889426169326522763426629) * 10^40
        + 1500530690301615442742378795267368581707) : ℚ) /
        (((((((((((856373838 * 10^40
        + 4964061878500512131921927310261459410850) * 10^40
        + 7880038319419246801415039542686552870440) * 10^40
        + 6166988295024833079611818876229334477434) * 10^40
        + 1032829693233327754337821052831761073407) * 10^40
        + 6013867349890824980527782137141008866341) * 10^40
        + 7951471640712445827607600295271571035906) * 10^40
        + 397479283341777690037191932947659736225) * 10^40
        + 2798293147941026468108278800282449776036) * 10^40
        + 3136308126061542363303203066070890506333) * 10^40
        + 7594521031323413805143049307394962069195) * 10^40
        + 3540126501310824037935207679072181157888)),
    (((-((((((((28186782 * 10^40
        + 4269555650915053017011085014421716775133) * 10^40
        + 4997858940009915056513648608358032132226) * 10^40
        + 8529441784196340218914786491604015717998) * 10^40
        + 1551138351740737552270879834689894653812) * 10^40
        + 6915078594934181107684901851264574148066) * 10^40
        + 6393063564334281854614781323939061528019) * 10^40
        + 3151833494680500823512966605062502817204) * 10^40
        + 1490709028078445053207549578170199211957)) : ℚ) /
        ((((((((466 * 10^40
        + 565230973624133558526167779360043636572) * 10^40
        + 4109669601874930549670219492506828262102) * 10^40
        + 3941139014796456452997852262342750741367) * 10^40
        + 735739778948538230406697993137601521364) * 10^40
        + 5672678517938210646571290218421409642190) * 10^40
        + 6831995526851481057226898214491419635051) * 10^40
        + 3938883756142930537586701324526589209838) * 10^40
        + 9811867037956618140370659910523889385472)))

noncomputable def pairedN05440MinusP002Error2553 : ℝ := ((47991106304641732704040200024805 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN05440MinusP002BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP002Center2553‖ ≤ pairedN05440MinusP002Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP002Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP002Input2553]
  have hs : compactExp2547 pairedN05440MinusP002Input2553 6 =
      (pairedN05440MinusP002Center2553, ((47991106304641732704040200024805 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP002Input2553 6).2 : ℝ) =
      pairedN05440MinusP002Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP002Error2553]
  have h := compactExp_error2547 pairedN05440MinusP002Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP002Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP002Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP002DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP002Factor2553 * embedPair2542
          pairedN05440MinusP002Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP002Factor2553 : ℝ) * pairedN05440MinusP002Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP002Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP002Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP002BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP002Factor2553)

def pairedN05440MinusP003Input2553 : RatPair2542 := ((((-((146 * 10^40
        + 4666505999543186600661552487163202263838) * 10^40
        + 5198120859216655713919987686397705358307)) : ℚ) /
        ((308 * 10^40
        + 5584325157930343245986452666829032621960) * 10^40
        + 3552613615865160449465749633167360000000)),
    ((362039942185747774262029 : ℚ) /
        1441151880758558720000000))

def pairedN05440MinusP003Center2553 : RatPair2542 := ((((-87241822855911911563400556314471745) :
    ℚ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-33821823401309118702122571323232333) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN05440MinusP003Factor2553 : RatPair2542 := ((((((((((((((786126223474925572189844865 *
    10^40
        + 3354702884629290213083650451553762400131) * 10^40
        + 9579098336394399572453744469045537209732) * 10^40
        + 1149731253292735480472918307218239487755) * 10^40
        + 7983864110422513431841172532356179336830) * 10^40
        + 1970222961664504550099325544781741764813) * 10^40
        + 7874373854601003984781734957896967101297) * 10^40
        + 2060586718789332043368964666466328091422) * 10^40
        + 7601901274937169290077702201634769619687) * 10^40
        + 6956678327584129034724669089661152554179) * 10^40
        + 3948691721048805371808250302434405221363) * 10^40
        + 8311463240950190756350912730153515754321) : ℚ) /
        (((((((((((125100243850258391234703 * 10^40
        + 4995695706726846002466186870263003335743) * 10^40
        + 4847637812652791158573231600937903752756) * 10^40
        + 7645733307912107572621105872524026047331) * 10^40
        + 5835171778052844612767578809234048284799) * 10^40
        + 6701121350062580819634235406927043742880) * 10^40
        + 4165395130683772529195154254614843952950) * 10^40
        + 1999633169006865505995753934608830929327) * 10^40
        + 2222997205390046433714500207573319555632) * 10^40
        + 7486387284660247605720823702103101882819) * 10^40
        + 5965801828423411882820003073630736240952) * 10^40
        + 5068012967054672365972737025814208446464)),
    (((-((((((((26075569794012486 * 10^40
        + 89922221897054709510382490377680222012) * 10^40
        + 1495157771104920944211368447785106301706) * 10^40
        + 9112210580615222691168193928412163916631) * 10^40
        + 5902739196553675225940800962381920394213) * 10^40
        + 4373286147725651565637631352255332661242) * 10^40
        + 5239309373194264091216206776240402969071) * 10^40
        + 2692560767305387248449424453916979179211) * 10^40
        + 486424562542561717332197540289835939311)) : ℚ) /
        ((((((((430903987195 * 10^40
        + 3036787996556007758858814067267494701812) * 10^40
        + 6891598905072457433128610262366956806589) * 10^40
        + 8914893803172754733750964915752643487035) * 10^40
        + 8993085148896280809115752769810975610103) * 10^40
        + 8483110465154781377284322090760779172148) * 10^40
        + 7037556954431239915791614970073949997245) * 10^40
        + 7692066781036377233723245227017918329579) * 10^40
        + 8436973621523872836176599849530510278656)))

noncomputable def pairedN05440MinusP003Error2553 : ℝ := ((52777713574168061994876877403937 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN05440MinusP003BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP003Center2553‖ ≤ pairedN05440MinusP003Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP003Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP003Input2553]
  have hs : compactExp2547 pairedN05440MinusP003Input2553 6 =
      (pairedN05440MinusP003Center2553, ((52777713574168061994876877403937 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP003Input2553 6).2 : ℝ) =
      pairedN05440MinusP003Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP003Error2553]
  have h := compactExp_error2547 pairedN05440MinusP003Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP003Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP003Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP003DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP003Factor2553 * embedPair2542
          pairedN05440MinusP003Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP003Factor2553 : ℝ) * pairedN05440MinusP003Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP003Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP003Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP003BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP003Factor2553)

def pairedN05440MinusP004Input2553 : RatPair2542 := ((((-((2 * 10^40
        + 5446819663058783993660070886078225195841) * 10^40
        + 2437251345453047163544114024481992724841)) : ℚ) /
        ((5 * 10^40
        + 3709268744536454894037321260456311664067) * 10^40
        + 5409328121924953525672938472263680000000)),
    (((-362039942185747774262029) : ℚ) /
        1441151880758558720000000))

def pairedN05440MinusP004Center2553 : RatPair2542 := ((((-92368363498077763200615907375097755) :
    ℚ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((35809275595485935311450143559984851 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN05440MinusP004Factor2553 : RatPair2542 := ((((((((((((((641793258009364 * 10^40
        + 6903373912391810363416163099634002091073) * 10^40
        + 3922039352381531140890238619213203618002) * 10^40
        + 3956822025394232048131007858299161819396) * 10^40
        + 7531571533125465054199825826417007961126) * 10^40
        + 5798615067455775945618353209660123148780) * 10^40
        + 9228165940025192632936575819837733510301) * 10^40
        + 3346373360785383545263735720875680754043) * 10^40
        + 1181338608707655677184878984385953377833) * 10^40
        + 2017767019761556461339225008821665819538) * 10^40
        + 7344411386898649040647524713923496614223) * 10^40
        + 1778989825484929975198138996439243581707) : ℚ) /
        (((((((((((128874000789 * 10^40
        + 8248012963730326716521146103321161279583) * 10^40
        + 4886240587390790871116373794511445611230) * 10^40
        + 1670546816688098377831740478228607328380) * 10^40
        + 7125481938769742023255524874840988775162) * 10^40
        + 4896635531149656032840074064026549648945) * 10^40
        + 1625509497499456537297243199617844116088) * 10^40
        + 5608796233975148897165699326618370687211) * 10^40
        + 6096869851129745719737456756781640715077) * 10^40
        + 1209785451726493365593131583336719327270) * 10^40
        + 9374787842709647703757931197695327833452) * 10^40
        + 8492484984328098776279143679072181157888)),
    ((((((((((797876543 * 10^40
        + 838685590218536890943941496604732349956) * 10^40
        + 1506728319397426783981450264159906006113) * 10^40
        + 2731934749665286981592733394043553032986) * 10^40
        + 709225527205385732737189971959750453826) * 10^40
        + 6518306603275471020298535845301888184307) * 10^40
        + 160475136622762889358120724882168803792) * 10^40
        + 3727999040661857223425550772246000657685) * 10^40
        + 5618538863503222492079836652388949211957) : ℚ) /
        ((((((((13185 * 10^40
        + 8016127353611814584171637125180201618495) * 10^40
        + 4959964127337556780442070131620983631468) * 10^40
        + 6661489113779641054622051588439612160968) * 10^40
        + 2770548086944166362669149970776464771112) * 10^40
        + 4591050674598677700135077169087520748449) * 10^40
        + 3519428327567097900729427518176852050843) * 10^40
        + 6521141887531967185265903260493976329157) * 10^40
        + 3227727773227200841369315910523889385472)))

noncomputable def pairedN05440MinusP004Error2553 : ℝ := ((1744663336729100491513849203247 : ℝ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))

theorem pairedN05440MinusP004BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP004Center2553‖ ≤ pairedN05440MinusP004Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP004Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP004Input2553]
  have hs : compactExp2547 pairedN05440MinusP004Input2553 6 =
      (pairedN05440MinusP004Center2553, ((1744663336729100491513849203247 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP004Input2553 6).2 : ℝ) =
      pairedN05440MinusP004Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP004Error2553]
  have h := compactExp_error2547 pairedN05440MinusP004Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP004Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP004Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP004DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP004Factor2553 * embedPair2542
          pairedN05440MinusP004Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP004Factor2553 : ℝ) * pairedN05440MinusP004Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP004Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP004Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP004BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP004Factor2553)

def pairedN05440MinusP005Input2553 : RatPair2542 := ((((-((120 * 10^40
        + 8092596673282430104202541543593795555768) * 10^40
        + 1336442834775297158451777459193116074921)) : ℚ) /
        ((125 * 10^40
        + 3117539759639451663790354394338218649327) * 10^40
        + 8796645127269504130198624449751040000000)),
    ((0 : ℚ) /
        1))

def pairedN05440MinusP005Center2553 : RatPair2542 := (((58440655205264784253542505258651371 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def pairedN05440MinusP005Factor2553 : RatPair2542 :=
    (((((((((((((103784507219687500321379263214930129 * 10^40
        + 1313279505962138994786694228472217306101) * 10^40
        + 3959836327688165926323743812403039026392) * 10^40
        + 6550645001696878958035849488808789945196) * 10^40
        + 4895828769341038268233323569598814096530) * 10^40
        + 6653588552831196209026579421010387426830) * 10^40
        + 733179704230452538780801517518820408643) * 10^40
        + 6539909348041653067044043681594786240607) * 10^40
        + 1588296571905112673712682732119573498566) * 10^40
        + 4996040641081536151345330564518080392294) * 10^40
        + 9894335761549241411417475800647430630479) : ℚ) /
        ((((((((((2686835637112402805739744976330506 * 10^40
        + 1124009443244004160027297680297912514717) * 10^40
        + 5413674461977368642529677336085192307921) * 10^40
        + 4382524253702604196172944501586100130983) * 10^40
        + 5710525529179307744818949481730494249355) * 10^40
        + 4149905100267191094486974442960496461846) * 10^40
        + 2569112915754520733815673849655529145608) * 10^40
        + 5628547956068344295721006963747374445367) * 10^40
        + 1833432105511100958028544996089653318082) * 10^40
        + 9576391290142279461471492332992499327869) * 10^40
        + 912811822879776228660193594820554956168)),
    ((0 : ℚ) /
        1))

noncomputable def pairedN05440MinusP005Error2553 : ℝ := ((5392063690868360224307101704391 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN05440MinusP005BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP005Center2553‖ ≤ pairedN05440MinusP005Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP005Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP005Input2553]
  have hs : compactExp2547 pairedN05440MinusP005Input2553 5 =
      (pairedN05440MinusP005Center2553, ((5392063690868360224307101704391 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP005Input2553 5).2 : ℝ) =
      pairedN05440MinusP005Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP005Error2553]
  have h := compactExp_error2547 pairedN05440MinusP005Input2553 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          pairedN05440MinusP005Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP005Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP005DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP005Factor2553 * embedPair2542
          pairedN05440MinusP005Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP005Factor2553 : ℝ) * pairedN05440MinusP005Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
      (storedWidth ⟨5, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP005Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP005Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨5, by omega⟩) (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP005BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP005Factor2553)

def pairedN05440MinusP006Input2553 : RatPair2542 := ((((-1319574023673334813971797333) : ℚ) /
        1383441177848927569920000000),
    ((0 : ℚ) /
        1))

def pairedN05440MinusP006Center2553 : RatPair2542 := (((81087962221925884035765162278375503 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def pairedN05440MinusP006Factor2553 : RatPair2542 := (((((193196752246660628126633274 * 10^40
        + 2031296524019920960861020020932280028856) * 10^40
        + 3652747557082522887565179846956951021037) : ℚ) /
        ((13134640807505800999788842 * 10^40
        + 4136026660720274558531709965293476242922) * 10^40
        + 7195280675955333059478561224344391831704)),
    ((0 : ℚ) /
        1))

noncomputable def pairedN05440MinusP006Error2553 : ℝ := ((3702723538938007690129329773821 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem pairedN05440MinusP006BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP006Center2553‖ ≤ pairedN05440MinusP006Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP006Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP006Input2553]
  have hs : compactExp2547 pairedN05440MinusP006Input2553 5 =
      (pairedN05440MinusP006Center2553, ((3702723538938007690129329773821 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP006Input2553 5).2 : ℝ) =
      pairedN05440MinusP006Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP006Error2553]
  have h := compactExp_error2547 pairedN05440MinusP006Input2553 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          pairedN05440MinusP006Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP006Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP006DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP006Factor2553 * embedPair2542
          pairedN05440MinusP006Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP006Factor2553 : ℝ) * pairedN05440MinusP006Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP006Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP006Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP006BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP006Factor2553)

def pairedN05440MinusP007Input2553 : RatPair2542 := ((((-((146 * 10^40
        + 4666505999543186600661552487163202263838) * 10^40
        + 5198120859216655713919987686397705358307)) : ℚ) /
        ((154 * 10^40
        + 2792162578965171622993226333414516310980) * 10^40
        + 1776306807932580224732874816583680000000)),
    ((0 : ℚ) /
        1))

def pairedN05440MinusP007Center2553 : RatPair2542 := (((23392107901773803867593395997467051 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1))

def pairedN05440MinusP007Factor2553 : RatPair2542 :=
    (((((((((((((1482783365809988760536987611610595940 * 10^40
        + 6309979698035902611404147831607745730968) * 10^40
        + 3199900325470831030543633644765139514359) * 10^40
        + 9984216166532204631137303704392626466767) * 10^40
        + 4158428006992135467384201730517386747678) * 10^40
        + 2668676941008951044832071835719984663522) * 10^40
        + 1501810466966241603901013919751580499206) * 10^40
        + 8713154576922705141146447356863563336267) * 10^40
        + 3094072371615439514864242150837427373649) * 10^40
        + 6631965499946434632054502851044225742574) * 10^40
        + 4267087894116710334454555637061015949277) : ℚ) /
        ((((((((((252637930514135423344756149138662960 * 10^40
        + 6067364299795357974235598125215550058033) * 10^40
        + 5487860496380372884064534921958904779435) * 10^40
        + 4917886559006727948701347241122710020866) * 10^40
        + 5740181988318056695202281654681716714565) * 10^40
        + 803934619824589439546891772881280380597) * 10^40
        + 2896486218621237612927237649237317100143) * 10^40
        + 385204635470894416448050769861046274070) * 10^40
        + 6852571909890207747846895582953106085916) * 10^40
        + 7243524696146052563149756450404473392067) * 10^40
        + 8376079183066317324363554903511872405784)),
    ((0 : ℚ) /
        1))

noncomputable def pairedN05440MinusP007Error2553 : ℝ := ((2126774035256946926737326396049 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem pairedN05440MinusP007BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP007Center2553‖ ≤ pairedN05440MinusP007Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP007Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP007Input2553]
  have hs : compactExp2547 pairedN05440MinusP007Input2553 5 =
      (pairedN05440MinusP007Center2553, ((2126774035256946926737326396049 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP007Input2553 5).2 : ℝ) =
      pairedN05440MinusP007Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP007Error2553]
  have h := compactExp_error2547 pairedN05440MinusP007Input2553 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          pairedN05440MinusP007Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP007Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP007DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP007Factor2553 * embedPair2542
          pairedN05440MinusP007Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP007Factor2553 : ℝ) * pairedN05440MinusP007Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP007Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP007Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP007BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP007Factor2553)

def pairedN05440MinusP008Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-260739661220379310273297) : ℚ) /
        2882303761517117440000000))

def pairedN05440MinusP008Center2553 : RatPair2542 := (((57537443603401921390633830479701233 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((15478251147924734515746882554607549 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def pairedN05440MinusP008Factor2553 : RatPair2542 := ((((((((((((((1181831257584397935692317 *
    10^40
        + 3142598344529169059185333847142264063947) * 10^40
        + 3949804768768407579606426622899548325196) * 10^40
        + 9067620483039503231296776470554753269339) * 10^40
        + 396459411454592911229449379953349036036) * 10^40
        + 8249574386372398312752065155147132764297) * 10^40
        + 1752177318141959186273640026012504857450) * 10^40
        + 1188385532578636638264883516180650263021) * 10^40
        + 1545396740595535718119785043387267847766) * 10^40
        + 9464041507991235716029974788658685698709) * 10^40
        + 2495593828275742170680927783800319936679) * 10^40
        + 239063530424861921102779540909097218089) : ℚ) /
        (((((((((((615289709700762130819 * 10^40
        + 2667369925511681703342192976575735905268) * 10^40
        + 4712110337195813426046525087490161349187) * 10^40
        + 2199025630085124060817057257331208478465) * 10^40
        + 765108591467221046079954119627757537065) * 10^40
        + 5136171490030332620748065972155513025576) * 10^40
        + 5420412172159710999947621946696328891093) * 10^40
        + 8115673089682555185428886907508899447392) * 10^40
        + 2487288857400932708493451356871747229039) * 10^40
        + 6568453865789071469954230234109021725778) * 10^40
        + 6753834925263062957660696391840787932008) * 10^40
        + 4604222616740656076036714503256833785856)),
    ((((((((((106690592422435 * 10^40
        + 2386859794369351490920485022283376364112) * 10^40
        + 7068938560201509666241044180815279494777) * 10^40
        + 8830538080270956905996173020835113465915) * 10^40
        + 7006607858670351390341223496940557187290) * 10^40
        + 1354157544647074552151798776103880179659) * 10^40
        + 8580164973318146922348050489638891611374) * 10^40
        + 7661085390628025588970154222045067620135) * 10^40
        + 9584303039455288367169652914106352229187) : ℚ) /
        ((((((((39565030288 * 10^40
        + 9116300174983236563756802637443229814807) * 10^40
        + 4031746182230799665665562575587711225433) * 10^40
        + 1681446925185722658165687198496468044983) * 10^40
        + 3404967696900733662351529618956548862365) * 10^40
        + 36611202581523272923670116609918720764) * 10^40
        + 2821979378199175952065784702342542672867) * 10^40
        + 1642881632148526095476342726337116339003) * 10^40
        + 2568591804903855026021259596244082229248)))

noncomputable def pairedN05440MinusP008Error2553 : ℝ := ((11575521723662052280025085548421 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem pairedN05440MinusP008BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP008Center2553‖ ≤ pairedN05440MinusP008Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP008Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP008Input2553]
  have hs : compactExp2547 pairedN05440MinusP008Input2553 6 =
      (pairedN05440MinusP008Center2553, ((11575521723662052280025085548421 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP008Input2553 6).2 : ℝ) =
      pairedN05440MinusP008Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP008Error2553]
  have h := compactExp_error2547 pairedN05440MinusP008Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP008Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP008Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP008DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP008Factor2553 * embedPair2542
          pairedN05440MinusP008Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP008Factor2553 : ℝ) * pairedN05440MinusP008Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP008Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP008Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP008BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP008Factor2553)

def pairedN05440MinusP009Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-387788191040974601829711) : ℚ) /
        2882303761517117440000000))

def pairedN05440MinusP009Center2553 : RatPair2542 := ((((-44852642557681038107682380285967765) :
    ℚ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-23754488556904829262836055396081811) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def pairedN05440MinusP009Factor2553 : RatPair2542 := ((((((((((((((2591190109035520969985956 *
    10^40
        + 1357376904669981804002028268816568708672) * 10^40
        + 4314517178476341268662817823704231633438) * 10^40
        + 3157977104464264718385792723886843694167) * 10^40
        + 7283371565092939865251648041529081781320) * 10^40
        + 9787095272374333141594669088162015475447) * 10^40
        + 7523270281052047028388957694254916937689) * 10^40
        + 1613325889727971996716563658552314362554) * 10^40
        + 2286402049072605968640490362060098630391) * 10^40
        + 3677884193031502632124733825678088237042) * 10^40
        + 8221470534877317767633704328918321359024) * 10^40
        + 2065658557722606333748673732642126995817) : ℚ) /
        (((((((((((615289709700762130819 * 10^40
        + 2667369925511681703342192976575735905268) * 10^40
        + 4712110337195813426046525087490161349187) * 10^40
        + 2199025630085124060817057257331208478465) * 10^40
        + 765108591467221046079954119627757537065) * 10^40
        + 5136171490030332620748065972155513025576) * 10^40
        + 5420412172159710999947621946696328891093) * 10^40
        + 8115673089682555185428886907508899447392) * 10^40
        + 2487288857400932708493451356871747229039) * 10^40
        + 6568453865789071469954230234109021725778) * 10^40
        + 6753834925263062957660696391840787932008) * 10^40
        + 4604222616740656076036714503256833785856)),
    ((((((((((120023411739442 * 10^40
        + 2416915793762800162037363842749374040982) * 10^40
        + 2553234986350089936499546301464123487046) * 10^40
        + 3094811149802774833544310271367649621708) * 10^40
        + 5499089360540131203495215874597993707813) * 10^40
        + 3639973986676899525542441054984841753100) * 10^40
        + 2841607988202606145583018323702238866303) * 10^40
        + 5688080041583452511043761021834307350157) * 10^40
        + 7954866379444542358947919460177407825759) : ℚ) /
        ((((((((13188343429 * 10^40
        + 6372100058327745521252267545814409938269) * 10^40
        + 1343915394076933221888520858529237075144) * 10^40
        + 3893815641728574219388562399498822681661) * 10^40
        + 1134989232300244554117176539652182954121) * 10^40
        + 6678870400860507757641223372203306240254) * 10^40
        + 7607326459399725317355261567447514224289) * 10^40
        + 547627210716175365158780908779038779667) * 10^40
        + 7522863934967951675340419865414694076416)))

noncomputable def pairedN05440MinusP009Error2553 : ℝ := ((34774923420691158720098641791685 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN05440MinusP009BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP009Center2553‖ ≤ pairedN05440MinusP009Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP009Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP009Input2553]
  have hs : compactExp2547 pairedN05440MinusP009Input2553 6 =
      (pairedN05440MinusP009Center2553, ((34774923420691158720098641791685 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP009Input2553 6).2 : ℝ) =
      pairedN05440MinusP009Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP009Error2553]
  have h := compactExp_error2547 pairedN05440MinusP009Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP009Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP009Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP009DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN05440MinusPosition2553 -
      embedPair2542 pairedN05440MinusP009Factor2553 * embedPair2542
          pairedN05440MinusP009Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP009Factor2553 : ℝ) * pairedN05440MinusP009Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP009Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP009Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP009BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP009Factor2553)

def pairedN05440MinusP010Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-230684447942438333698521) : ℚ) /
        1441151880758558720000000))

def pairedN05440MinusP010Center2553 : RatPair2542 := ((((-1393429861033247907131675594061061) : ℚ)
    /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    ((23877898517905602507702050279895391 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def pairedN05440MinusP010Factor2553 : RatPair2542 := ((((((((((((((914984513923833925492733 *
    10^40
        + 5190558810466230406373636623835112821736) * 10^40
        + 3198654916826590373142861736158781653281) * 10^40
        + 7184460418692735657610551598357343315123) * 10^40
        + 534343359443383272803743264330724423222) * 10^40
        + 6943045843834964092753656034792548430180) * 10^40
        + 5064679948490948897340384058787905278085) * 10^40
        + 1654751234554614245056710333600292445907) * 10^40
        + 7090967280637581460554115786048817914123) * 10^40
        + 4427609517244616709582504192680026594256) * 10^40
        + 9983088727108882625657967675161958130911) * 10^40
        + 4129720234497023563496139879074148665721) : ℚ) /
        (((((((((((153822427425190532704 * 10^40
        + 8166842481377920425835548244143933976317) * 10^40
        + 1178027584298953356511631271872540337296) * 10^40
        + 8049756407521281015204264314332802119616) * 10^40
        + 2691277147866805261519988529906939384266) * 10^40
        + 3784042872507583155187016493038878256394) * 10^40
        + 1355103043039927749986905486674082222773) * 10^40
        + 4528918272420638796357221726877224861848) * 10^40
        + 621822214350233177123362839217936807259) * 10^40
        + 9142113466447267867488557558527255431444) * 10^40
        + 6688458731315765739415174097960196983002) * 10^40
        + 1151055654185164019009178625814208446464)),
    ((((((((((2824493697830 * 10^40
        + 1996021308397087274143186866415942671128) * 10^40
        + 6462973687312484652215499380709066477686) * 10^40
        + 2105362745472614726124909613579600857432) * 10^40
        + 9641613818353236086962141326366509202994) * 10^40
        + 7211673743509220930614495605364387674920) * 10^40
        + 6564237126501276262822482647230222940708) * 10^40
        + 3204704994579033633397155848749529508740) * 10^40
        + 8810766662707728579231926409634486402257) : ℚ) /
        ((((((((183171436 * 10^40
        + 5227390278587885354461837049247422360253) * 10^40
        + 7379776602695512961415118345257350514932) * 10^40
        + 5609636328357341308602618922215261426134) * 10^40
        + 1821319294893058952140516340828502541029) * 10^40
        + 4676095422234173718856128102391712586670) * 10^40
        + 2050101756380551740518823077325659919781) * 10^40
        + 7924272600148835768960538623733042205273) * 10^40
        + 1632261999096777106601950275908537417728)))

noncomputable def pairedN05440MinusP010Error2553 : ℝ := ((2135345849964300921452249795461 : ℝ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))

theorem pairedN05440MinusP010BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP010Center2553‖ ≤ pairedN05440MinusP010Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP010Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP010Input2553]
  have hs : compactExp2547 pairedN05440MinusP010Input2553 6 =
      (pairedN05440MinusP010Center2553, ((2135345849964300921452249795461 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP010Input2553 6).2 : ℝ) =
      pairedN05440MinusP010Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP010Error2553]
  have h := compactExp_error2547 pairedN05440MinusP010Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP010Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP010Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP010DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP010Factor2553 * embedPair2542
          pairedN05440MinusP010Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP010Factor2553 : ℝ) * pairedN05440MinusP010Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP010Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP010Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP010BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP010Factor2553)

def pairedN05440MinusP011Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-255213677437476200797801) : ℚ) /
        1441151880758558720000000))

def pairedN05440MinusP011Center2553 : RatPair2542 := (((21677349661823418260054337967759011 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((15408915768246468071665926197435201 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def pairedN05440MinusP011Factor2553 : RatPair2542 := ((((((((((((((1118854100001245812843104 *
    10^40
        + 6581516974851987812301381616719850432489) * 10^40
        + 5908502985280152678849748342588077616014) * 10^40
        + 2861133030209246730638022929453553782530) * 10^40
        + 7333906746900465189174530952847301425519) * 10^40
        + 5443121230012361948570962162342041740224) * 10^40
        + 5621686820502655078826718606873922997841) * 10^40
        + 809123092216753140714007065230533153358) * 10^40
        + 7865194129845165926445470687223851061613) * 10^40
        + 397222630235835121402930132896927793256) * 10^40
        + 6492891795937777302109890430703788575238) * 10^40
        + 6037860252528325779252044579807953444761) : ℚ) /
        (((((((((((153822427425190532704 * 10^40
        + 8166842481377920425835548244143933976317) * 10^40
        + 1178027584298953356511631271872540337296) * 10^40
        + 8049756407521281015204264314332802119616) * 10^40
        + 2691277147866805261519988529906939384266) * 10^40
        + 3784042872507583155187016493038878256394) * 10^40
        + 1355103043039927749986905486674082222773) * 10^40
        + 4528918272420638796357221726877224861848) * 10^40
        + 621822214350233177123362839217936807259) * 10^40
        + 9142113466447267867488557558527255431444) * 10^40
        + 6688458731315765739415174097960196983002) * 10^40
        + 1151055654185164019009178625814208446464)),
    ((((((((((103543172894050 * 10^40
        + 5081804142129873472706596038300346003841) * 10^40
        + 4462570653409165506528841972927495371683) * 10^40
        + 3524971311951207227613410204535637513674) * 10^40
        + 2745843959135451624711171726680884538080) * 10^40
        + 6463382051375690597484480308515806777243) * 10^40
        + 7422753502122665786226260362038586321263) * 10^40
        + 9310022463640543633743107995085489972468) * 10^40
        + 8779550312087056972714332229949549222939) : ℚ) /
        ((((((((4945628786 * 10^40
        + 1139537521872904570469600329680403726850) * 10^40
        + 9253968272778849958208195321948463903179) * 10^40
        + 1460180865648215332270710899812058505622) * 10^40
        + 9175620962112591707793941202369568607795) * 10^40
        + 6254576400322690409115458764576239840095) * 10^40
        + 5352747422274896994008223087792817834108) * 10^40
        + 3955360204018565761934542840792139542375) * 10^40
        + 4071073975612981878252657449530510278656)))

noncomputable def pairedN05440MinusP011Error2553 : ℝ := ((976176441297065170493648203653 : ℝ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))

theorem pairedN05440MinusP011BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP011Center2553‖ ≤ pairedN05440MinusP011Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP011Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP011Input2553]
  have hs : compactExp2547 pairedN05440MinusP011Input2553 6 =
      (pairedN05440MinusP011Center2553, ((976176441297065170493648203653 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP011Input2553 6).2 : ℝ) =
      pairedN05440MinusP011Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP011Error2553]
  have h := compactExp_error2547 pairedN05440MinusP011Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP011Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP011Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP011DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP011Factor2553 * embedPair2542
          pairedN05440MinusP011Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP011Factor2553 : ℝ) * pairedN05440MinusP011Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP011Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP011Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP011BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP011Factor2553)

def pairedN05440MinusP012Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-5612399119318874813509) : ℚ) /
        28823037615171174400000))

def pairedN05440MinusP012Center2553 : RatPair2542 := (((64981192871236934929299603481569641 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((6804926438889422414819218834034259 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN05440MinusP012Factor2553 : RatPair2542 := ((((((((((((((337928450341740069393618 *
    10^40
        + 7442914892255251599208751730816810743863) * 10^40
        + 3758929292733408468364690464715375457298) * 10^40
        + 8467937320258441351746124661793665592931) * 10^40
        + 3539699342092401191082342425938019648133) * 10^40
        + 2088028319167671678624370340260749619208) * 10^40
        + 3228875658341036347299749014504693250087) * 10^40
        + 799285145837982936356398883746022667560) * 10^40
        + 5758549823035271887201986638386599648925) * 10^40
        + 3022828404714345006475962230164288952667) * 10^40
        + 5263895898458601761732621938110492671363) * 10^40
        + 6891862723413755604566245396321515166673) : ℚ) /
        (((((((((((38455606856297633176 * 10^40
        + 2041710620344480106458887061035983494079) * 10^40
        + 2794506896074738339127907817968135084324) * 10^40
        + 2012439101880320253801066078583200529904) * 10^40
        + 672819286966701315379997132476734846066) * 10^40
        + 5946010718126895788796754123259719564098) * 10^40
        + 5338775760759981937496726371668520555693) * 10^40
        + 3632229568105159699089305431719306215462) * 10^40
        + 155455553587558294280840709804484201814) * 10^40
        + 9785528366611816966872139389631813857861) * 10^40
        + 1672114682828941434853793524490049245750) * 10^40
        + 5287763913546291004752294656453552111616)),
    ((((((((((218243652187 * 10^40
        + 2791771974603644136468048873367506654100) * 10^40
        + 7666832181844425984135545181563125906558) * 10^40
        + 7912941842212153399836600348902699793607) * 10^40
        + 5378145301878058791556078911908825877800) * 10^40
        + 2871826745205942143500582474854540532519) * 10^40
        + 5695240675875089349050305288116703607480) * 10^40
        + 4592664143747299176857517030820299697824) * 10^40
        + 929266628334672914004827021702036122225) : ℚ) /
        ((((((((7825362 * 10^40
        + 33448635319419152801375949888734816023) * 10^40
        + 4982996785241738686642734486268905797315) * 10^40
        + 1568766108964633252108023276740208953331) * 10^40
        + 6818315855952709797006003071522736659189) * 10^40
        + 5500402810760004256976448510703443417468) * 10^40
        + 5055937891490941292712038327670558256066) * 10^40
        + 6272081266145598996458757188039228068896) * 10^40
        + 1636188408189261047275716230141662199808)))

noncomputable def pairedN05440MinusP012Error2553 : ℝ := ((4396854203489918989623838475413 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem pairedN05440MinusP012BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP012Center2553‖ ≤ pairedN05440MinusP012Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP012Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP012Input2553]
  have hs : compactExp2547 pairedN05440MinusP012Input2553 6 =
      (pairedN05440MinusP012Center2553, ((4396854203489918989623838475413 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP012Input2553 6).2 : ℝ) =
      pairedN05440MinusP012Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP012Error2553]
  have h := compactExp_error2547 pairedN05440MinusP012Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP012Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP012Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP012DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP012Factor2553 * embedPair2542
          pairedN05440MinusP012Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP012Factor2553 : ℝ) * pairedN05440MinusP012Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP012Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP012Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP012BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP012Factor2553)

def pairedN05440MinusP013Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-60754466143128272313291) : ℚ) /
        288230376151711744000000))

def pairedN05440MinusP013Center2553 : RatPair2542 := (((39382765271224552272061736665356415 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-26066550646370625254922894967874555) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def pairedN05440MinusP013Factor2553 : RatPair2542 := ((((((((((((((1583145759367673728388917 *
    10^40
        + 7013120409564294817813601846857645212902) * 10^40
        + 9029398422765238517399262770615831847682) * 10^40
        + 6687633290456604773743665772813063059851) * 10^40
        + 8533909477521491679668738740756943629602) * 10^40
        + 1013137402658928721140368501921673341147) * 10^40
        + 9734384634134241388130644265981948100424) * 10^40
        + 4671636841127468749027869063491915099403) * 10^40
        + 2323638975511519033803466930864765771299) * 10^40
        + 8212353613755729242163774653707028493920) * 10^40
        + 3832746676057629051350250435891729319926) * 10^40
        + 6100420439345585517325257919689173171417) : ℚ) /
        (((((((((((153822427425190532704 * 10^40
        + 8166842481377920425835548244143933976317) * 10^40
        + 1178027584298953356511631271872540337296) * 10^40
        + 8049756407521281015204264314332802119616) * 10^40
        + 2691277147866805261519988529906939384266) * 10^40
        + 3784042872507583155187016493038878256394) * 10^40
        + 1355103043039927749986905486674082222773) * 10^40
        + 4528918272420638796357221726877224861848) * 10^40
        + 621822214350233177123362839217936807259) * 10^40
        + 9142113466447267867488557558527255431444) * 10^40
        + 6688458731315765739415174097960196983002) * 10^40
        + 1151055654185164019009178625814208446464)),
    ((((((((((58405275689149 * 10^40
        + 2706570230250280575557327546244743474495) * 10^40
        + 2944369661050852325156766582842759491199) * 10^40
        + 7938504560850789999185018105448104659874) * 10^40
        + 1846127400543987418401734681481400289907) * 10^40
        + 5248107338077095110735229724424866077980) * 10^40
        + 9996341354740525953354781659757560574784) * 10^40
        + 3307685674779943757853031142288191708125) * 10^40
        + 8006699655556821851191613712477878925335) : ℚ) /
        ((((((((1648542928 * 10^40
        + 7046512507290968190156533443226801242283) * 10^40
        + 6417989424259616652736065107316154634393) * 10^40
        + 486726955216071777423570299937352835207) * 10^40
        + 6391873654037530569264647067456522869265) * 10^40
        + 2084858800107563469705152921525413280031) * 10^40
        + 8450915807424965664669407695930939278036) * 10^40
        + 1318453401339521920644847613597379847458) * 10^40
        + 4690357991870993959417552483176836759552)))

noncomputable def pairedN05440MinusP013Error2553 : ℝ := ((7355829096510237871649470901867 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem pairedN05440MinusP013BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP013Center2553‖ ≤ pairedN05440MinusP013Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP013Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP013Input2553]
  have hs : compactExp2547 pairedN05440MinusP013Input2553 6 =
      (pairedN05440MinusP013Center2553, ((7355829096510237871649470901867 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP013Input2553 6).2 : ℝ) =
      pairedN05440MinusP013Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP013Error2553]
  have h := compactExp_error2547 pairedN05440MinusP013Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP013Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP013Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP013DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP013Factor2553 * embedPair2542
          pairedN05440MinusP013Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP013Factor2553 : ℝ) * pairedN05440MinusP013Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP013Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP013Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP013BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP013Factor2553)

def pairedN05440MinusP014Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-346671309892138695845011) : ℚ) /
        1441151880758558720000000))

def pairedN05440MinusP014Center2553 : RatPair2542 := ((((-62168845630609279066093426989327931) :
    ℚ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-10048595471072856334951689568819431) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def pairedN05440MinusP014Factor2553 : RatPair2542 := ((((((((((((((2060433127963877853053973 *
    10^40
        + 1293682730704897289631819108695071236913) * 10^40
        + 2707861376995335026753016383678498769308) * 10^40
        + 3400159085965992322807334977304518113673) * 10^40
        + 2640088408306280067863263061815213641613) * 10^40
        + 1095499307257972747456106222914620871309) * 10^40
        + 927781465250162393640854463936798190627) * 10^40
        + 6482802840818517221843000183891346737583) * 10^40
        + 9955595991028861935968579743947672915114) * 10^40
        + 5350043631337055460033766476538974520226) * 10^40
        + 9254340794261080366808549033862330525734) * 10^40
        + 3652852682884295186980324610549630238641) : ℚ) /
        (((((((((((153822427425190532704 * 10^40
        + 8166842481377920425835548244143933976317) * 10^40
        + 1178027584298953356511631271872540337296) * 10^40
        + 8049756407521281015204264314332802119616) * 10^40
        + 2691277147866805261519988529906939384266) * 10^40
        + 3784042872507583155187016493038878256394) * 10^40
        + 1355103043039927749986905486674082222773) * 10^40
        + 4528918272420638796357221726877224861848) * 10^40
        + 621822214350233177123362839217936807259) * 10^40
        + 9142113466447267867488557558527255431444) * 10^40
        + 6688458731315765739415174097960196983002) * 10^40
        + 1151055654185164019009178625814208446464)),
    ((((((((((260931446082144 * 10^40
        + 7543473061566476620117893602758196596472) * 10^40
        + 6253716542306610135814478854318446245533) * 10^40
        + 2699124219292122255330919128645156516325) * 10^40
        + 2973863773356501232144586964194550653250) * 10^40
        + 1442917419452395311379127337860877554182) * 10^40
        + 8589814000945863242466973114436558576824) * 10^40
        + 2049318136940657623329669951891719286627) * 10^40
        + 327240242035458422652906257761393170289) : ℚ) /
        ((((((((4945628786 * 10^40
        + 1139537521872904570469600329680403726850) * 10^40
        + 9253968272778849958208195321948463903179) * 10^40
        + 1460180865648215332270710899812058505622) * 10^40
        + 9175620962112591707793941202369568607795) * 10^40
        + 6254576400322690409115458764576239840095) * 10^40
        + 5352747422274896994008223087792817834108) * 10^40
        + 3955360204018565761934542840792139542375) * 10^40
        + 4071073975612981878252657449530510278656)))

noncomputable def pairedN05440MinusP014Error2553 : ℝ := ((17482014299399900349848528141407 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem pairedN05440MinusP014BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP014Center2553‖ ≤ pairedN05440MinusP014Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP014Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP014Input2553]
  have hs : compactExp2547 pairedN05440MinusP014Input2553 6 =
      (pairedN05440MinusP014Center2553, ((17482014299399900349848528141407 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP014Input2553 6).2 : ℝ) =
      pairedN05440MinusP014Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP014Error2553]
  have h := compactExp_error2547 pairedN05440MinusP014Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP014Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP014Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP014DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP014Factor2553 * embedPair2542
          pairedN05440MinusP014Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP014Factor2553 : ℝ) * pairedN05440MinusP014Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP014Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP014Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP014BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP014Factor2553)

def pairedN05440MinusP015Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-377408574479356852679047) : ℚ) /
        1441151880758558720000000))

def pairedN05440MinusP015Center2553 : RatPair2542 := ((((-1011769251304330505760896803558561) : ℚ)
    /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    ((56750481799658991252986141589092645 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN05440MinusP015Factor2553 : RatPair2542 := ((((((((((((((2441126231339702913064765 *
    10^40
        + 4488277406468537133201094227233786886731) * 10^40
        + 418885639738623645625681897126279874891) * 10^40
        + 7606511550198512748282458851990945793082) * 10^40
        + 9351067632840871334084831369085796507280) * 10^40
        + 6239062840253666441606030531457180954653) * 10^40
        + 6225606143580492549611279880290480510822) * 10^40
        + 9997093807289123424746290356606701243556) * 10^40
        + 9263032871197765659912881102474350578411) * 10^40
        + 1347762745552247694299180464873714372905) * 10^40
        + 7791951400568855867747405367355597396469) * 10^40
        + 6489372102042545399431454226996284067513) : ℚ) /
        (((((((((((153822427425190532704 * 10^40
        + 8166842481377920425835548244143933976317) * 10^40
        + 1178027584298953356511631271872540337296) * 10^40
        + 8049756407521281015204264314332802119616) * 10^40
        + 2691277147866805261519988529906939384266) * 10^40
        + 3784042872507583155187016493038878256394) * 10^40
        + 1355103043039927749986905486674082222773) * 10^40
        + 4528918272420638796357221726877224861848) * 10^40
        + 621822214350233177123362839217936807259) * 10^40
        + 9142113466447267867488557558527255431444) * 10^40
        + 6688458731315765739415174097960196983002) * 10^40
        + 1151055654185164019009178625814208446464)),
    ((((((((((337010552786843 * 10^40
        + 7880178993912446791687793397100477805195) * 10^40
        + 7462266725108659263159851553244014875968) * 10^40
        + 4633457445582666853211802613111964360929) * 10^40
        + 3392309471548117761426378314501110799034) * 10^40
        + 8455448729295527500065138605560997193415) * 10^40
        + 8121759847189931753925954463314817952283) * 10^40
        + 6671043681403628464034361366927525026510) * 10^40
        + 7616231877814209904992146158938096869461) : ℚ) /
        ((((((((4945628786 * 10^40
        + 1139537521872904570469600329680403726850) * 10^40
        + 9253968272778849958208195321948463903179) * 10^40
        + 1460180865648215332270710899812058505622) * 10^40
        + 9175620962112591707793941202369568607795) * 10^40
        + 6254576400322690409115458764576239840095) * 10^40
        + 5352747422274896994008223087792817834108) * 10^40
        + 3955360204018565761934542840792139542375) * 10^40
        + 4071073975612981878252657449530510278656)))

noncomputable def pairedN05440MinusP015Error2553 : ℝ := ((43319910888660698020942386707399 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN05440MinusP015BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP015Center2553‖ ≤ pairedN05440MinusP015Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP015Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP015Input2553]
  have hs : compactExp2547 pairedN05440MinusP015Input2553 6 =
      (pairedN05440MinusP015Center2553, ((43319910888660698020942386707399 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP015Input2553 6).2 : ℝ) =
      pairedN05440MinusP015Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP015Error2553]
  have h := compactExp_error2547 pairedN05440MinusP015Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP015Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP015Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP015DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP015Factor2553 * embedPair2542
          pairedN05440MinusP015Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP015Factor2553 : ℝ) * pairedN05440MinusP015Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP015Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP015Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP015BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP015Factor2553)

def pairedN05440MinusP016Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-199810861117846303095609) : ℚ) /
        720575940379279360000000))

def pairedN05440MinusP016Center2553 : RatPair2542 := (((7368508287208723833617869710274807 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((58310752188159705405092269008552461 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN05440MinusP016Factor2553 : RatPair2542 := ((((((((((((((684090907314985592044151 *
    10^40
        + 9729558597162589367466687259440544241378) * 10^40
        + 2345759200487303957576286271546652497114) * 10^40
        + 2667965879657868073286767991117875535110) * 10^40
        + 4275891093136386758709841370203118467763) * 10^40
        + 8597123254400600521419337905284528076138) * 10^40
        + 7958374648758290760380955826256673277025) * 10^40
        + 4339256941279262854775909502897501112407) * 10^40
        + 5272009245965206101155537831997490276275) * 10^40
        + 2089924038969408504851181044418854639965) * 10^40
        + 9177594097353764214379641406340850100691) * 10^40
        + 7699793927815607756057591339609992058937) : ℚ) /
        (((((((((((38455606856297633176 * 10^40
        + 2041710620344480106458887061035983494079) * 10^40
        + 2794506896074738339127907817968135084324) * 10^40
        + 2012439101880320253801066078583200529904) * 10^40
        + 672819286966701315379997132476734846066) * 10^40
        + 5946010718126895788796754123259719564098) * 10^40
        + 5338775760759981937496726371668520555693) * 10^40
        + 3632229568105159699089305431719306215462) * 10^40
        + 155455553587558294280840709804484201814) * 10^40
        + 9785528366611816966872139389631813857861) * 10^40
        + 1672114682828941434853793524490049245750) * 10^40
        + 5287763913546291004752294656453552111616)),
    ((((((((((16680082540408 * 10^40
        + 8485448654690336150751197593180905315648) * 10^40
        + 4742036231889220243290763208676645940273) * 10^40
        + 1096377695957032285921759986963109476056) * 10^40
        + 3996075272589381672320729105188809645403) * 10^40
        + 5981880999725060257986022203904239715390) * 10^40
        + 4210876291926831213589945429650930676747) * 10^40
        + 6802482456457497613893478277476108333451) * 10^40
        + 8250752121261343349639025529712242236281) : ℚ) /
        ((((((((206067866 * 10^40
        + 880814063411371023769566680403350155285) * 10^40
        + 4552248678032452081592008138414519329299) * 10^40
        + 1310840869402008972177946287492169104400) * 10^40
        + 9548984206754691321158080883432065358658) * 10^40
        + 1510607350013445433713144115190676660003) * 10^40
        + 9806364475928120708083675961991367409754) * 10^40
        + 5164806675167440240080605951699672480932) * 10^40
        + 3086294748983874244927194060397104594944)))

noncomputable def pairedN05440MinusP016Error2553 : ℝ := ((20160656965579976439248333390805 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem pairedN05440MinusP016BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP016Center2553‖ ≤ pairedN05440MinusP016Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP016Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP016Input2553]
  have hs : compactExp2547 pairedN05440MinusP016Input2553 6 =
      (pairedN05440MinusP016Center2553, ((20160656965579976439248333390805 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP016Input2553 6).2 : ℝ) =
      pairedN05440MinusP016Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP016Error2553]
  have h := compactExp_error2547 pairedN05440MinusP016Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP016Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP016Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP016DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP016Factor2553 * embedPair2542
          pairedN05440MinusP016Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP016Factor2553 : ℝ) * pairedN05440MinusP016Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP016Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP016Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP016BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP016Factor2553)

def pairedN05440MinusP017Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-442769373018475956606027) : ℚ) /
        1441151880758558720000000))

def pairedN05440MinusP017Center2553 : RatPair2542 := (((5611306955666891588827560422351355 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    (((-11868312439964319863065903548417661) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def pairedN05440MinusP017Factor2553 : RatPair2542 := ((((((((((((((3358082763531537459538519 *
    10^40
        + 6768074832827224930948891574485383606427) * 10^40
        + 496415441452031876754905755866385950006) * 10^40
        + 901920193988557744755689591015874035312) * 10^40
        + 3881333884026449779484316012074976285129) * 10^40
        + 7958499373598557851771627593292327393353) * 10^40
        + 7012758173677588166118541643381080631562) * 10^40
        + 4939257520105594590758851564573392583360) * 10^40
        + 2851933023030246947021834099598043655214) * 10^40
        + 5337872830496309827535459126498586826369) * 10^40
        + 736230330048313488055812370899322824682) * 10^40
        + 525334122005427611903096088926802259393) : ℚ) /
        (((((((((((153822427425190532704 * 10^40
        + 8166842481377920425835548244143933976317) * 10^40
        + 1178027584298953356511631271872540337296) * 10^40
        + 8049756407521281015204264314332802119616) * 10^40
        + 2691277147866805261519988529906939384266) * 10^40
        + 3784042872507583155187016493038878256394) * 10^40
        + 1355103043039927749986905486674082222773) * 10^40
        + 4528918272420638796357221726877224861848) * 10^40
        + 621822214350233177123362839217936807259) * 10^40
        + 9142113466447267867488557558527255431444) * 10^40
        + 6688458731315765739415174097960196983002) * 10^40
        + 1151055654185164019009178625814208446464)),
    ((((((((((181661090147387 * 10^40
        + 8342583527681433269722790147327210288674) * 10^40
        + 3338241674182428893177307976612336304116) * 10^40
        + 5787653367656410439297395998227385952826) * 10^40
        + 1747629593277008343304711332397930112345) * 10^40
        + 2018013373439998738958865890707932628883) * 10^40
        + 1490957845789750208640640407187952503802) * 10^40
        + 6965463484191753851920022987032613446387) * 10^40
        + 9851723607009216242776685154218208979107) : ℚ) /
        ((((((((1648542928 * 10^40
        + 7046512507290968190156533443226801242283) * 10^40
        + 6417989424259616652736065107316154634393) * 10^40
        + 486726955216071777423570299937352835207) * 10^40
        + 6391873654037530569264647067456522869265) * 10^40
        + 2084858800107563469705152921525413280031) * 10^40
        + 8450915807424965664669407695930939278036) * 10^40
        + 1318453401339521920644847613597379847458) * 10^40
        + 4690357991870993959417552483176836759552)))

noncomputable def pairedN05440MinusP017Error2553 : ℝ := ((36280065101144762218000893027007 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN05440MinusP017BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP017Center2553‖ ≤ pairedN05440MinusP017Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP017Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP017Input2553]
  have hs : compactExp2547 pairedN05440MinusP017Input2553 6 =
      (pairedN05440MinusP017Center2553, ((36280065101144762218000893027007 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP017Input2553 6).2 : ℝ) =
      pairedN05440MinusP017Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP017Error2553]
  have h := compactExp_error2547 pairedN05440MinusP017Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP017Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP017Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP017DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP017Factor2553 * embedPair2542
          pairedN05440MinusP017Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP017Factor2553 : ℝ) * pairedN05440MinusP017Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP017Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP017Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP017BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP017Factor2553)

def pairedN05440MinusP018Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-114770645411675231749613) : ℚ) /
        360287970189639680000000))

def pairedN05440MinusP018Center2553 : RatPair2542 := (((1077535662890610878976762588306111 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-8162622623876380485045945234927505) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)))

def pairedN05440MinusP018Factor2553 : RatPair2542 := ((((((((((((((225608334576366357698560 *
    10^40
        + 556675884947453115648324565877131161572) * 10^40
        + 9029819412422318614148009453450603004053) * 10^40
        + 3426892890792442593121518037248925490322) * 10^40
        + 3550719803613368380687271256245174336432) * 10^40
        + 9836351806713686914325855439905821138759) * 10^40
        + 3265054255817237639643986756315519650547) * 10^40
        + 1756959914972536003698618187684787056167) * 10^40
        + 6565900865794211710701496305388722398216) * 10^40
        + 4693514226301876044381262361922097225315) * 10^40
        + 8321515159914039663061418059056106272704) * 10^40
        + 7868871487999265309480555929777128503473) : ℚ) /
        (((((((((((9613901714074408294 * 10^40
        + 510427655086120026614721765258995873519) * 10^40
        + 8198626724018684584781976954492033771081) * 10^40
        + 503109775470080063450266519645800132476) * 10^40
        + 168204821741675328844999283119183711516) * 10^40
        + 6486502679531723947199188530814929891024) * 10^40
        + 6334693940189995484374181592917130138923) * 10^40
        + 3408057392026289924772326357929826553865) * 10^40
        + 5038863888396889573570210177451121050453) * 10^40
        + 7446382091652954241718034847407953464465) * 10^40
        + 2918028670707235358713448381122512311437) * 10^40
        + 6321940978386572751188073664113388027904)),
    ((((((((((9494277955634 * 10^40
        + 6083332914062631293575529779557275369966) * 10^40
        + 6798670988874703767427130905043197691488) * 10^40
        + 1548861119542248872779318065322648104787) * 10^40
        + 7793044616706594709571954402688673321617) * 10^40
        + 5978367073150685461696269902717793629227) * 10^40
        + 2035951586646577033654669945140694471961) * 10^40
        + 8106847047224278958025471284898515528319) * 10^40
        + 8961877825668969713143258909967023764239) : ℚ) /
        ((((((((77275449 * 10^40
        + 7830305273779264133913587505151256308232) * 10^40
        + 457093254262169530597003051905444748487) * 10^40
        + 1741565326025753364566729857809563414150) * 10^40
        + 3580869077533009245434280331287024509496) * 10^40
        + 8066477756255042037642429043196503747501) * 10^40
        + 4927386678473045265531378485746762778657) * 10^40
        + 9436802503187790090030227231887377180349) * 10^40
        + 6157360530868952841847697772648914223104)))

noncomputable def pairedN05440MinusP018Error2553 : ℝ := ((20947289263051892501081730537617 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem pairedN05440MinusP018BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP018Center2553‖ ≤ pairedN05440MinusP018Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP018Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP018Input2553]
  have hs : compactExp2547 pairedN05440MinusP018Input2553 6 =
      (pairedN05440MinusP018Center2553, ((20947289263051892501081730537617 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP018Input2553 6).2 : ℝ) =
      pairedN05440MinusP018Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP018Error2553]
  have h := compactExp_error2547 pairedN05440MinusP018Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP018Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP018Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP018DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP018Factor2553 * embedPair2542
          pairedN05440MinusP018Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP018Factor2553 : ℝ) * pairedN05440MinusP018Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP018Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP018Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP018BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP018Factor2553)

def pairedN05440MinusP019Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-24428249467783476683391) : ℚ) /
        72057594037927936000000))

def pairedN05440MinusP019Center2553 : RatPair2542 := ((((-7815442200531936289270772578682233) : ℚ)
    /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    (((-9482479847814596727027007597998467) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def pairedN05440MinusP019Factor2553 : RatPair2542 := ((((((((((((((255476815121777853248290 *
    10^40
        + 4320746974880621438517971394300888556470) * 10^40
        + 5022963183232394849291536304749425672481) * 10^40
        + 2787507974654923371610704585896180979275) * 10^40
        + 304029535601693876920000103794906038737) * 10^40
        + 5850435142235371619216735726403267602407) * 10^40
        + 8411438051504645431974128729496178313012) * 10^40
        + 9921357528710298817266208851959374597910) * 10^40
        + 6447593396988372469192073844464840710551) * 10^40
        + 7270434047929105347327669170711391864840) * 10^40
        + 6310296316683054080962499635399392852821) * 10^40
        + 6848126117318894097536780333636030368737) : ℚ) /
        (((((((((((9613901714074408294 * 10^40
        + 510427655086120026614721765258995873519) * 10^40
        + 8198626724018684584781976954492033771081) * 10^40
        + 503109775470080063450266519645800132476) * 10^40
        + 168204821741675328844999283119183711516) * 10^40
        + 6486502679531723947199188530814929891024) * 10^40
        + 6334693940189995484374181592917130138923) * 10^40
        + 3408057392026289924772326357929826553865) * 10^40
        + 5038863888396889573570210177451121050453) * 10^40
        + 7446382091652954241718034847407953464465) * 10^40
        + 2918028670707235358713448381122512311437) * 10^40
        + 6321940978386572751188073664113388027904)),
    ((((((((((1272036522876 * 10^40
        + 561627818311892358225386611418103643034) * 10^40
        + 8427142943493684124101864447617202809109) * 10^40
        + 9097961975749177852396762203201646517553) * 10^40
        + 2822498331859516876205300232041814282992) * 10^40
        + 3133649164499216869121897488548559725827) * 10^40
        + 5911343412256257391473710706613825401480) * 10^40
        + 799440149148418044395454359892733001047) * 10^40
        + 4418395345331556549944056783974335840145) : ℚ) /
        ((((((((8586161 * 10^40
        + 870033919308807125990398611683472923136) * 10^40
        + 8939677028251352170066333672433938305387) * 10^40
        + 4637951702891750373840747761978840379350) * 10^40
        + 397874341948112138381586703476336056610) * 10^40
        + 7562941972917226893071381004799611527500) * 10^40
        + 1658598519830338362836819831749640308739) * 10^40
        + 7715200278131976676670025247987486353372) * 10^40
        + 1795262281207661426871966419183212691456)))

noncomputable def pairedN05440MinusP019Error2553 : ℝ := ((8423310590053608888693934210313 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem pairedN05440MinusP019BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP019Center2553‖ ≤ pairedN05440MinusP019Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP019Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP019Input2553]
  have hs : compactExp2547 pairedN05440MinusP019Input2553 6 =
      (pairedN05440MinusP019Center2553, ((8423310590053608888693934210313 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP019Input2553 6).2 : ℝ) =
      pairedN05440MinusP019Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP019Error2553]
  have h := compactExp_error2547 pairedN05440MinusP019Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP019Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP019Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP019DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP019Factor2553 * embedPair2542
          pairedN05440MinusP019Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP019Factor2553 : ℝ) * pairedN05440MinusP019Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP019Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP019Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP019BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP019Factor2553)

def pairedN05440MinusP020Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-520624750538575899551419) : ℚ) /
        1441151880758558720000000))

def pairedN05440MinusP020Center2553 : RatPair2542 := ((((-6980419667796297935851867826465579) : ℚ)
    /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((59069808794261997953049105203250151 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN05440MinusP020Factor2553 : RatPair2542 := ((((((((((((((4641051043318446297413546 *
    10^40
        + 5442572052343948177903417407217861927620) * 10^40
        + 996094522010713597694422572420086414976) * 10^40
        + 4715682726170753601396708553408909457256) * 10^40
        + 1143677528011650856510335065508792145030) * 10^40
        + 2466304500763621189158089343151191385039) * 10^40
        + 4439485001845218806928677999451250006293) * 10^40
        + 4971662066371531576644447972045428523243) * 10^40
        + 2943756761662475630980156450243183265753) * 10^40
        + 9720264306143349374741091402531230768058) * 10^40
        + 7858794427202713504769237163001027819669) * 10^40
        + 6346449334105509962490441678504648860001) : ℚ) /
        (((((((((((153822427425190532704 * 10^40
        + 8166842481377920425835548244143933976317) * 10^40
        + 1178027584298953356511631271872540337296) * 10^40
        + 8049756407521281015204264314332802119616) * 10^40
        + 2691277147866805261519988529906939384266) * 10^40
        + 3784042872507583155187016493038878256394) * 10^40
        + 1355103043039927749986905486674082222773) * 10^40
        + 4528918272420638796357221726877224861848) * 10^40
        + 621822214350233177123362839217936807259) * 10^40
        + 9142113466447267867488557558527255431444) * 10^40
        + 6688458731315765739415174097960196983002) * 10^40
        + 1151055654185164019009178625814208446464)),
    ((((((((((886944602019749 * 10^40
        + 2691566337907671328278235618846517095823) * 10^40
        + 8989994352679659293310918331171235820759) * 10^40
        + 2592090049652137131102332766971986951804) * 10^40
        + 5241624191999115731535977573639934146392) * 10^40
        + 7400711566273555330787295963484333219780) * 10^40
        + 2332159978897985048026459094005179745038) * 10^40
        + 264896663203800497638811467006480590602) * 10^40
        + 6783366416093393310781858033295078646361) : ℚ) /
        ((((((((4945628786 * 10^40
        + 1139537521872904570469600329680403726850) * 10^40
        + 9253968272778849958208195321948463903179) * 10^40
        + 1460180865648215332270710899812058505622) * 10^40
        + 9175620962112591707793941202369568607795) * 10^40
        + 6254576400322690409115458764576239840095) * 10^40
        + 5352747422274896994008223087792817834108) * 10^40
        + 3955360204018565761934542840792139542375) * 10^40
        + 4071073975612981878252657449530510278656)))

noncomputable def pairedN05440MinusP020Error2553 : ℝ := ((34476628344028209087924675364365 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN05440MinusP020BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP020Center2553‖ ≤ pairedN05440MinusP020Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP020Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP020Input2553]
  have hs : compactExp2547 pairedN05440MinusP020Input2553 6 =
      (pairedN05440MinusP020Center2553, ((34476628344028209087924675364365 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP020Input2553 6).2 : ℝ) =
      pairedN05440MinusP020Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP020Error2553]
  have h := compactExp_error2547 pairedN05440MinusP020Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP020Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP020Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP020DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP020Factor2553 * embedPair2542
          pairedN05440MinusP020Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP020Factor2553 : ℝ) * pairedN05440MinusP020Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP020Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP020Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP020BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP020Factor2553)

def pairedN05440MinusP021Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-547379874475946380671387) : ℚ) /
        1441151880758558720000000))

def pairedN05440MinusP021Center2553 : RatPair2542 := (((5546667542089404187799787667176599 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((11989237669076459402226118305731901 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def pairedN05440MinusP021Factor2553 : RatPair2542 := ((((((((((((((5129819771533651516577939 *
    10^40
        + 4635561474917201782466776202543932238232) * 10^40
        + 881126951305738890282362242916239183254) * 10^40
        + 9466198494532432545825971403965458785360) * 10^40
        + 8478889273115615801828158184138709793603) * 10^40
        + 1412028718802314821043421724464141037676) * 10^40
        + 3592231801249987741183875680875475636384) * 10^40
        + 869556726237947273013895442387343738598) * 10^40
        + 3180251822131241312719644150622309239865) * 10^40
        + 1638638832449619630650159732487575125852) * 10^40
        + 2521885559612473944017260862911373713) * 10^40
        + 5701808293933861073102436317630432277153) : ℚ) /
        (((((((((((153822427425190532704 * 10^40
        + 8166842481377920425835548244143933976317) * 10^40
        + 1178027584298953356511631271872540337296) * 10^40
        + 8049756407521281015204264314332802119616) * 10^40
        + 2691277147866805261519988529906939384266) * 10^40
        + 3784042872507583155187016493038878256394) * 10^40
        + 1355103043039927749986905486674082222773) * 10^40
        + 4528918272420638796357221726877224861848) * 10^40
        + 621822214350233177123362839217936807259) * 10^40
        + 9142113466447267867488557558527255431444) * 10^40
        + 6688458731315765739415174097960196983002) * 10^40
        + 1151055654185164019009178625814208446464)),
    ((((((((((343704139159115 * 10^40
        + 2857687242117532737070139777435314725862) * 10^40
        + 6594869830513050636818840809053789471512) * 10^40
        + 7976431359223578415797773964368320004100) * 10^40
        + 548027156562207837272068605300550472917) * 10^40
        + 9537101052233211959826306969875198651815) * 10^40
        + 2869241318153412604859857267636522288382) * 10^40
        + 4536696275623867963332382967085851755665) * 10^40
        + 2508951378269159672991637110865286787347) : ℚ) /
        ((((((((1648542928 * 10^40
        + 7046512507290968190156533443226801242283) * 10^40
        + 6417989424259616652736065107316154634393) * 10^40
        + 486726955216071777423570299937352835207) * 10^40
        + 6391873654037530569264647067456522869265) * 10^40
        + 2084858800107563469705152921525413280031) * 10^40
        + 8450915807424965664669407695930939278036) * 10^40
        + 1318453401339521920644847613597379847458) * 10^40
        + 4690357991870993959417552483176836759552)))

noncomputable def pairedN05440MinusP021Error2553 : ℝ := ((3065659187948564675395851116657 : ℝ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))

theorem pairedN05440MinusP021BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP021Center2553‖ ≤ pairedN05440MinusP021Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP021Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP021Input2553]
  have hs : compactExp2547 pairedN05440MinusP021Input2553 6 =
      (pairedN05440MinusP021Center2553, ((3065659187948564675395851116657 : ℚ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP021Input2553 6).2 : ℝ) =
      pairedN05440MinusP021Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP021Error2553]
  have h := compactExp_error2547 pairedN05440MinusP021Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP021Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP021Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP021DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP021Factor2553 * embedPair2542
          pairedN05440MinusP021Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP021Factor2553 : ℝ) * pairedN05440MinusP021Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP021Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP021Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP021BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP021Factor2553)

def pairedN05440MinusP022Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-112214826711468142236233) : ℚ) /
        288230376151711744000000))

def pairedN05440MinusP022Center2553 : RatPair2542 := (((63817657112379587604278607655993249 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((14006037680027037671027376792218359 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN05440MinusP022Factor2553 : RatPair2542 := ((((((((((((((5389464511738927496482610 *
    10^40
        + 341961320741640239800931676787216074801) * 10^40
        + 5385965764328558105585414607290459699281) * 10^40
        + 5820477744674736400664902519726901285514) * 10^40
        + 2256083168968079401589403711352753593320) * 10^40
        + 3544963748299950864957940397288890651555) * 10^40
        + 9291339739907571732924538557596854944882) * 10^40
        + 2195614299215455242368544623678002752443) * 10^40
        + 7486432637477282752499060959831386653028) * 10^40
        + 1817409916718054839731074946161914454327) * 10^40
        + 71136742718469868073475475441806373369) * 10^40
        + 8335407488079620360277385593844373815217) : ℚ) /
        (((((((((((153822427425190532704 * 10^40
        + 8166842481377920425835548244143933976317) * 10^40
        + 1178027584298953356511631271872540337296) * 10^40
        + 8049756407521281015204264314332802119616) * 10^40
        + 2691277147866805261519988529906939384266) * 10^40
        + 3784042872507583155187016493038878256394) * 10^40
        + 1355103043039927749986905486674082222773) * 10^40
        + 4528918272420638796357221726877224861848) * 10^40
        + 621822214350233177123362839217936807259) * 10^40
        + 9142113466447267867488557558527255431444) * 10^40
        + 6688458731315765739415174097960196983002) * 10^40
        + 1151055654185164019009178625814208446464)),
    ((((((((((1110590628735490 * 10^40
        + 7032749493232654933721270240483926803483) * 10^40
        + 6110229106905133034543885659491123136347) * 10^40
        + 2096644267445827014717365790694730368229) * 10^40
        + 8308841315843367660978564665513119124011) * 10^40
        + 9553238908739858690774572587902316872775) * 10^40
        + 7781808235666200882433278485500089394142) * 10^40
        + 2443355759022240217926811200621077154938) * 10^40
        + 9515771906382510363944146639167458076815) : ℚ) /
        ((((((((4945628786 * 10^40
        + 1139537521872904570469600329680403726850) * 10^40
        + 9253968272778849958208195321948463903179) * 10^40
        + 1460180865648215332270710899812058505622) * 10^40
        + 9175620962112591707793941202369568607795) * 10^40
        + 6254576400322690409115458764576239840095) * 10^40
        + 5352747422274896994008223087792817834108) * 10^40
        + 3955360204018565761934542840792139542375) * 10^40
        + 4071073975612981878252657449530510278656)))

noncomputable def pairedN05440MinusP022Error2553 : ℝ := ((16548566980209543060734829991673 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN05440MinusP022BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP022Center2553‖ ≤ pairedN05440MinusP022Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP022Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP022Input2553]
  have hs : compactExp2547 pairedN05440MinusP022Input2553 6 =
      (pairedN05440MinusP022Center2553, ((16548566980209543060734829991673 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP022Input2553 6).2 : ℝ) =
      pairedN05440MinusP022Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP022Error2553]
  have h := compactExp_error2547 pairedN05440MinusP022Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP022Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP022Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP022DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP022Factor2553 * embedPair2542
          pairedN05440MinusP022Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP022Factor2553 : ℝ) * pairedN05440MinusP022Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP022Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP022Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP022BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP022Factor2553)

def pairedN05440MinusP023Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-300278613592663314364333) : ℚ) /
        720575940379279360000000))

def pairedN05440MinusP023Center2553 : RatPair2542 := (((546097029598654723288844450884957 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-32650003443169062489187091249533325) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def pairedN05440MinusP023Factor2553 : RatPair2542 := ((((((((((((((1543495583031498467102666 *
    10^40
        + 799690648741173181434789317500177448685) * 10^40
        + 8894903512046540560825037537266644727132) * 10^40
        + 1581876777713273261503825562145312493427) * 10^40
        + 1719826869157638317268497432628292519643) * 10^40
        + 745426102172515351404880043577873042370) * 10^40
        + 4894170605104589117656878418283696825311) * 10^40
        + 1245820308422958402999669024612976795153) * 10^40
        + 2571542035213649009458815964987207618515) * 10^40
        + 9899003739926715895680181367063855968758) * 10^40
        + 9121477403365471741967782138067850105922) * 10^40
        + 9053175707829052952390489318067459658289) : ℚ) /
        (((((((((((38455606856297633176 * 10^40
        + 2041710620344480106458887061035983494079) * 10^40
        + 2794506896074738339127907817968135084324) * 10^40
        + 2012439101880320253801066078583200529904) * 10^40
        + 672819286966701315379997132476734846066) * 10^40
        + 5946010718126895788796754123259719564098) * 10^40
        + 5338775760759981937496726371668520555693) * 10^40
        + 3632229568105159699089305431719306215462) * 10^40
        + 155455553587558294280840709804484201814) * 10^40
        + 9785528366611816966872139389631813857861) * 10^40
        + 1672114682828941434853793524490049245750) * 10^40
        + 5287763913546291004752294656453552111616)),
    ((((((((((170294760869750 * 10^40
        + 3620831302105188528889376794828537277574) * 10^40
        + 9759942517051700952782325996090438896221) * 10^40
        + 7147808942284497793350423692860064079139) * 10^40
        + 9798931351239906895295735555476796458935) * 10^40
        + 3973977320042985207496360744309025356411) * 10^40
        + 2776578460364236922204715389986835912019) * 10^40
        + 6302832473271143106912064272942750419911) * 10^40
        + 5366317990453447856393669978236957336783) : ℚ) /
        ((((((((618203598 * 10^40
        + 2642442190234113071308700041210050465856) * 10^40
        + 3656746034097356244776024415243557987897) * 10^40
        + 3932522608206026916533838862476507313202) * 10^40
        + 8646952620264073963474242650296196075974) * 10^40
        + 4531822050040336301139432345572029980011) * 10^40
        + 9419093427784362124251027885974102229263) * 10^40
        + 5494420025502320720241817855099017442796) * 10^40
        + 9258884246951622734781582181191313784832)))

noncomputable def pairedN05440MinusP023Error2553 : ℝ := ((32628954055431805277938626737177 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN05440MinusP023BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP023Center2553‖ ≤ pairedN05440MinusP023Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP023Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP023Input2553]
  have hs : compactExp2547 pairedN05440MinusP023Input2553 6 =
      (pairedN05440MinusP023Center2553, ((32628954055431805277938626737177 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP023Input2553 6).2 : ℝ) =
      pairedN05440MinusP023Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP023Error2553]
  have h := compactExp_error2547 pairedN05440MinusP023Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP023Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP023Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP023DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP023Factor2553 * embedPair2542
          pairedN05440MinusP023Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP023Factor2553 : ℝ) * pairedN05440MinusP023Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP023Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP023Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP023BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP023Factor2553)

def pairedN05440MinusP024Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-309351029057948556428147) : ℚ) /
        720575940379279360000000))

def pairedN05440MinusP024Center2553 : RatPair2542 := ((((-45593317821105483971316900705359595) :
    ℚ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-23399315272413716566477367365491267) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def pairedN05440MinusP024Factor2553 : RatPair2542 := ((((((((((((((1638100196876699501539050 *
    10^40
        + 4305970117824701852991448356971888687962) * 10^40
        + 5369109702835460545664072689682775441279) * 10^40
        + 5751483717474266438687272268540479906005) * 10^40
        + 9616967732857785742120852844966563728325) * 10^40
        + 1074718894393049429338964863692426787022) * 10^40
        + 536405883939202752804828823904732387918) * 10^40
        + 965140436433874702079888583406442156192) * 10^40
        + 5641178683664602832957696866547335988222) * 10^40
        + 7184041775484760656857847178581660996496) * 10^40
        + 1020949560078167226954816575760351164073) * 10^40
        + 3455618368672743185082650804589253001969) : ℚ) /
        (((((((((((38455606856297633176 * 10^40
        + 2041710620344480106458887061035983494079) * 10^40
        + 2794506896074738339127907817968135084324) * 10^40
        + 2012439101880320253801066078583200529904) * 10^40
        + 672819286966701315379997132476734846066) * 10^40
        + 5946010718126895788796754123259719564098) * 10^40
        + 5338775760759981937496726371668520555693) * 10^40
        + 3632229568105159699089305431719306215462) * 10^40
        + 155455553587558294280840709804484201814) * 10^40
        + 9785528366611816966872139389631813857861) * 10^40
        + 1672114682828941434853793524490049245750) * 10^40
        + 5287763913546291004752294656453552111616)),
    ((((((((((186224254883892 * 10^40
        + 6465896993322178165827542651545285908332) * 10^40
        + 5947094576750736266016145985272674467348) * 10^40
        + 9449725548817607169266907551378775801817) * 10^40
        + 5926125652309448633475660577586111814266) * 10^40
        + 3520678869272761518849340701088313109385) * 10^40
        + 5728439838183295753599887124017882398960) * 10^40
        + 3893849919410797810357110876350642854449) * 10^40
        + 4276152518215873683925943264174864923217) : ℚ) /
        ((((((((618203598 * 10^40
        + 2642442190234113071308700041210050465856) * 10^40
        + 3656746034097356244776024415243557987897) * 10^40
        + 3932522608206026916533838862476507313202) * 10^40
        + 8646952620264073963474242650296196075974) * 10^40
        + 4531822050040336301139432345572029980011) * 10^40
        + 9419093427784362124251027885974102229263) * 10^40
        + 5494420025502320720241817855099017442796) * 10^40
        + 9258884246951622734781582181191313784832)))

noncomputable def pairedN05440MinusP024Error2553 : ℝ := ((17847018982919138271653029957335 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem pairedN05440MinusP024BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP024Center2553‖ ≤ pairedN05440MinusP024Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP024Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP024Input2553]
  have hs : compactExp2547 pairedN05440MinusP024Input2553 6 =
      (pairedN05440MinusP024Center2553, ((17847018982919138271653029957335 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP024Input2553 6).2 : ℝ) =
      pairedN05440MinusP024Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP024Error2553]
  have h := compactExp_error2547 pairedN05440MinusP024Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP024Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP024Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP024DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP024Factor2553 * embedPair2542
          pairedN05440MinusP024Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP024Factor2553 : ℝ) * pairedN05440MinusP024Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP024Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP024Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP024BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP024Factor2553)

def pairedN05440MinusP025Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-10022692915539018190833) : ℚ) /
        22517998136852480000000))

def pairedN05440MinusP025Center2553 : RatPair2542 := ((((-63875530228774256251539673558941199) :
    ℚ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((13739690273093361774554214402741597 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN05440MinusP025Factor2553 : RatPair2542 := ((((((((((((((1719429242713507998946 * 10^40
        + 5993185456474155487174226795811192794404) * 10^40
        + 4316906027326660371480031127482297756246) * 10^40
        + 8546874898098703448916817316646510681074) * 10^40
        + 8683405619576718169209993578312872922606) * 10^40
        + 3659638040138352830449775244889349081763) * 10^40
        + 1343092512024306260697086893315273038885) * 10^40
        + 5570132244117134006505954612471652199379) * 10^40
        + 2326316902372488866935891500678572577369) * 10^40
        + 7988795976162938977006523182249871931930) * 10^40
        + 8358877434426137257319036658559140054292) * 10^40
        + 9035849675395336625954519050069380437993) : ℚ) /
        (((((((((((37554303570603157 * 10^40
        + 3986368858027680156353963756895542952630) * 10^40
        + 9367963385640697986659304597478484506918) * 10^40
        + 2853527772560430000247852603592366406767) * 10^40
        + 4844407050084928419253300778449684311373) * 10^40
        + 1119087901091920796668746830198495819886) * 10^40
        + 8149744898203867169860836646847332539605) * 10^40
        + 1693000224187602695018641899835663384976) * 10^40
        + 371245562064050349896758633505668441603) * 10^40
        + 3349399930045519352506711073622687318220) * 10^40
        + 5675461049494950138119974407738759813716) * 10^40
        + 5532507581946822549809328412750442921984)),
    ((((((((((2111418371 * 10^40
        + 3903589515601048183130339480101727422848) * 10^40
        + 1035377229979265627582526543212013330047) * 10^40
        + 6472255606517257939739823600446472757072) * 10^40
        + 9453646218018504576904086874372272544840) * 10^40
        + 1017754361760308002644066466158851324748) * 10^40
        + 486540711037214553179973714595568752037) * 10^40
        + 3633756179125089866416194725212093033918) * 10^40
        + 9821627168255443539669680081519608431713) : ℚ) /
        ((((((((6288 * 10^40
        + 6922023950624493755219231248983166606144) * 10^40
        + 8756547615010926283327685302982739700907) * 10^40
        + 2662088343532391418730840391427230595980) * 10^40
        + 9692674224371544027445103701198835207072) * 10^40
        + 7129562701640320234540823765384374715474) * 10^40
        + 2432855418837766361105593373900207256085) * 10^40
        + 5027623437703709943854982928648428334731) * 10^40
        + 4737643014366118892646634741029675204608)))

noncomputable def pairedN05440MinusP025Error2553 : ℝ := ((33910517938688277445528691085679 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN05440MinusP025BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP025Center2553‖ ≤ pairedN05440MinusP025Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP025Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP025Input2553]
  have hs : compactExp2547 pairedN05440MinusP025Input2553 6 =
      (pairedN05440MinusP025Center2553, ((33910517938688277445528691085679 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP025Input2553 6).2 : ℝ) =
      pairedN05440MinusP025Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP025Error2553]
  have h := compactExp_error2547 pairedN05440MinusP025Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP025Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP025Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP025DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP025Factor2553 * embedPair2542
          pairedN05440MinusP025Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP025Factor2553 : ℝ) * pairedN05440MinusP025Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP025Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP025Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP025BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP025Factor2553)

def pairedN05440MinusP026Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-20771944281655350607437) : ℚ) /
        45035996273704960000000))

def pairedN05440MinusP026Center2553 : RatPair2542 := ((((-20950550992964738097325173016083277) :
    ℚ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((61886483693119730794800201012074801 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN05440MinusP026Factor2553 : RatPair2542 := ((((((((((((((7384986135142706014860 * 10^40
        + 7234497311785073530833053332058936879983) * 10^40
        + 7925831695394352372603575936718496699693) * 10^40
        + 5128862544801486679432280825479709127783) * 10^40
        + 4003707228367477395499622940944664303245) * 10^40
        + 8854062831560155539153741850916857475050) * 10^40
        + 1067797263726665670600462891139351981195) * 10^40
        + 6217144820941428453393214604160021970606) * 10^40
        + 7055569064020780175475046909211913542175) * 10^40
        + 19853245422596287816802390850391313518) * 10^40
        + 4216355830848374675546142402145300815919) * 10^40
        + 974984343948052777736426762434369350769) : ℚ) /
        (((((((((((150217214282412629 * 10^40
        + 5945475432110720625415855027582171810523) * 10^40
        + 7471853542562791946637218389913938027673) * 10^40
        + 1414111090241720000991410414369465627069) * 10^40
        + 9377628200339713677013203113798737245492) * 10^40
        + 4476351604367683186674987320793983279547) * 10^40
        + 2598979592815468679443346587389330158420) * 10^40
        + 6772000896750410780074567599342653539904) * 10^40
        + 1484982248256201399587034534022673766413) * 10^40
        + 3397599720182077410026844294490749272882) * 10^40
        + 2701844197979800552479897630955039254866) * 10^40
        + 2130030327787290199237313651001771687936)),
    ((((((((((18797850629 * 10^40
        + 3302440159791059364357418660821650326838) * 10^40
        + 8597572428399922788058093992466855480074) * 10^40
        + 1403490710582694954012860290519030574104) * 10^40
        + 8756025647391538445518338216320057209937) * 10^40
        + 2528488871860510924236689599519922926918) * 10^40
        + 2290685375049330660660393097528005759598) * 10^40
        + 3436966349289099332397126900183527876985) * 10^40
        + 5181582504812759223160025689063278345509) : ℚ) /
        ((((((((50309 * 10^40
        + 5376191604995950041753849991865332849159) * 10^40
        + 52380920087410266621482423861917607258) * 10^40
        + 1296706748259131349846723131417844767847) * 10^40
        + 7541393794972352219560829609590681656581) * 10^40
        + 7036501613122561876326590123074997723793) * 10^40
        + 9462843350702130888844746991201658048684) * 10^40
        + 220987501629679550839863429187426677851) * 10^40
        + 7901144114928951141173077928237401636864)))

noncomputable def pairedN05440MinusP026Error2553 : ℝ := ((44459671579128562018930784651135 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN05440MinusP026BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP026Center2553‖ ≤ pairedN05440MinusP026Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP026Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP026Input2553]
  have hs : compactExp2547 pairedN05440MinusP026Input2553 6 =
      (pairedN05440MinusP026Center2553, ((44459671579128562018930784651135 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP026Input2553 6).2 : ℝ) =
      pairedN05440MinusP026Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP026Error2553]
  have h := compactExp_error2547 pairedN05440MinusP026Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP026Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP026Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP026DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP026Factor2553 * embedPair2542
          pairedN05440MinusP026Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP026Factor2553 : ℝ) * pairedN05440MinusP026Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP026Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP026Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP026BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP026Factor2553)

def pairedN05440MinusP027Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-43640783619197408678627) : ℚ) /
        90071992547409920000000))

def pairedN05440MinusP027Center2553 : RatPair2542 := (((59991988506244458811825167593834681 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((6470238432016159455881033226313381 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def pairedN05440MinusP027Factor2553 : RatPair2542 := ((((((((((((((32595298030354008679876 * 10^40
        + 8979580102568069168152269692157700747574) * 10^40
        + 8165367065853637692686573614683131671879) * 10^40
        + 5973233241683839064877154699593720286150) * 10^40
        + 6940195475538761697140270327561019432291) * 10^40
        + 8691989107824507214003898060933209167728) * 10^40
        + 1133045443816915566962892279539471723201) * 10^40
        + 8534238807564137255306553462999718446259) * 10^40
        + 2919256284332516431253942677849508014703) * 10^40
        + 1685767431359208836496051242859160125543) * 10^40
        + 6193859041822253854402690103823099263173) * 10^40
        + 9999605161395535428810704272106491858833) : ℚ) /
        (((((((((((600868857129650518 * 10^40
        + 3781901728442882501663420110328687242094) * 10^40
        + 9887414170251167786548873559655752110692) * 10^40
        + 5656444360966880003965641657477862508279) * 10^40
        + 7510512801358854708052812455194948981969) * 10^40
        + 7905406417470732746699949283175933118189) * 10^40
        + 395918371261874717773386349557320633682) * 10^40
        + 7088003587001643120298270397370614159616) * 10^40
        + 5939928993024805598348138136090695065653) * 10^40
        + 3590398880728309640107377177962997091529) * 10^40
        + 807376791919202209919590523820157019464) * 10^40
        + 8520121311149160796949254604007086751744)),
    ((((((((((523053876282 * 10^40
        + 3047717649031669908384703033644497576619) * 10^40
        + 6272458804772182049549990085560773126563) * 10^40
        + 6623558836028697718175209437070238195667) * 10^40
        + 9906372700509864624789893460351075750761) * 10^40
        + 9339451013086029954053427327493271383282) * 10^40
        + 4597475491920203967249934209413305714748) * 10^40
        + 9419437879712359774118899682630140791443) * 10^40
        + 2181031021168990300144652872301560224961) : ℚ) /
        ((((((((1207428 * 10^40
        + 9028598519902801002092399804767988379816) * 10^40
        + 1257142082097846398915578172686022574195) * 10^40
        + 1120961958219152396321355154028274428346) * 10^40
        + 993451079336453269459910630176359757960) * 10^40
        + 8876038714941485031838162953799945371054) * 10^40
        + 7108240416851141332273927788839793168416) * 10^40
        + 5303700039112309220156722300498240268442) * 10^40
        + 9627458758294827388153870277697639284736)))

noncomputable def pairedN05440MinusP027Error2553 : ℝ := ((33008144590911146402814644922329 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN05440MinusP027BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP027Center2553‖ ≤ pairedN05440MinusP027Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP027Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP027Input2553]
  have hs : compactExp2547 pairedN05440MinusP027Input2553 6 =
      (pairedN05440MinusP027Center2553, ((33008144590911146402814644922329 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP027Input2553 6).2 : ℝ) =
      pairedN05440MinusP027Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP027Error2553]
  have h := compactExp_error2547 pairedN05440MinusP027Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP027Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP027Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP027DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP027Factor2553 * embedPair2542
          pairedN05440MinusP027Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP027Factor2553 : ℝ) * pairedN05440MinusP027Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP027Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP027Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP027BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP027Factor2553)

def pairedN05440MinusP028Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-177883892884016178388727) : ℚ) /
        360287970189639680000000))

def pairedN05440MinusP028Center2553 : RatPair2542 := (((32125150056192319319468236911328825 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-5932145191161807255973200262839383) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def pairedN05440MinusP028Factor2553 : RatPair2542 := ((((((((((((((541544324604954985284855 *
    10^40
        + 9857534772172973614109816732312368657954) * 10^40
        + 8857702032950636206462436769403404139412) * 10^40
        + 3363244529205593693330630473077493149642) * 10^40
        + 1096765393654409101017822582949418590488) * 10^40
        + 1036433657256838232287031680750379431772) * 10^40
        + 5492193518185505005146577189362576568665) * 10^40
        + 9122224422060064327032323284168312486178) * 10^40
        + 8408231819308112657362207593884397875428) * 10^40
        + 967804916903821694674006434870575489272) * 10^40
        + 6099954362422672431211297310450867853209) * 10^40
        + 6526723759244866656669587512681536541913) : ℚ) /
        (((((((((((9613901714074408294 * 10^40
        + 510427655086120026614721765258995873519) * 10^40
        + 8198626724018684584781976954492033771081) * 10^40
        + 503109775470080063450266519645800132476) * 10^40
        + 168204821741675328844999283119183711516) * 10^40
        + 6486502679531723947199188530814929891024) * 10^40
        + 6334693940189995484374181592917130138923) * 10^40
        + 3408057392026289924772326357929826553865) * 10^40
        + 5038863888396889573570210177451121050453) * 10^40
        + 7446382091652954241718034847407953464465) * 10^40
        + 2918028670707235358713448381122512311437) * 10^40
        + 6321940978386572751188073664113388027904)),
    ((((((((((3220410954536 * 10^40
        + 293280729693511226625422591434184731606) * 10^40
        + 6841432371822842347065485576109936350529) * 10^40
        + 6706711624590687393402390127656708524489) * 10^40
        + 7737461850665583539885517113967345439113) * 10^40
        + 8708239825284449542312818700734522655517) * 10^40
        + 6622893127651260940513539270464443847026) * 10^40
        + 5064074586724221837073615235961596861703) * 10^40
        + 8863650135014167209140737691374476130031) : ℚ) /
        ((((((((7025040 * 10^40
        + 8893664115798114921264871591377386937112) * 10^40
        + 41553932205651775508818459264131340771) * 10^40
        + 5612869575093250305869702714346323946740) * 10^40
        + 9416442643412091749584934575571547682681) * 10^40
        + 5278770705114094730694766276654227613409) * 10^40
        + 2266126061679367751411943498704251161696) * 10^40
        + 1766982045744344553639111566535216107304) * 10^40
        + 5105214593715359349258881615695355838464)))

noncomputable def pairedN05440MinusP028Error2553 : ℝ := ((14695639712678390958218844296803 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem pairedN05440MinusP028BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP028Center2553‖ ≤ pairedN05440MinusP028Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP028Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP028Input2553]
  have hs : compactExp2547 pairedN05440MinusP028Input2553 6 =
      (pairedN05440MinusP028Center2553, ((14695639712678390958218844296803 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP028Input2553 6).2 : ℝ) =
      pairedN05440MinusP028Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP028Error2553]
  have h := compactExp_error2547 pairedN05440MinusP028Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP028Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP028Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP028DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP028Factor2553 * embedPair2542
          pairedN05440MinusP028Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP028Factor2553 : ℝ) * pairedN05440MinusP028Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP028Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP028Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP028BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP028Factor2553)

def pairedN05440MinusP029Input2553 : RatPair2542 := ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-182939534351242879487659) : ℚ) /
        360287970189639680000000))

def pairedN05440MinusP029Center2553 : RatPair2542 := (((15378381360168585499056981868587243 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-7205557748376929678185862056215515) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)))

def pairedN05440MinusP029Factor2553 : RatPair2542 := ((((((((((((((572747177653301731128773 *
    10^40
        + 3312986162706169906181878557293935545508) * 10^40
        + 8242696038950801577509319309965542421626) * 10^40
        + 8709626748315744629696801131404057594422) * 10^40
        + 3819666119849094729311829626767142623934) * 10^40
        + 1057961515741877047382842853636528432514) * 10^40
        + 9735025835470153714962366671512436748356) * 10^40
        + 1211951372247750657760454755369331566526) * 10^40
        + 6985513916493482557674198001154419157586) * 10^40
        + 485003827355252469145203626781685213779) * 10^40
        + 4774298016942853383335274916753397784855) * 10^40
        + 4535957995474913591218795454117461248001) : ℚ) /
        (((((((((((9613901714074408294 * 10^40
        + 510427655086120026614721765258995873519) * 10^40
        + 8198626724018684584781976954492033771081) * 10^40
        + 503109775470080063450266519645800132476) * 10^40
        + 168204821741675328844999283119183711516) * 10^40
        + 6486502679531723947199188530814929891024) * 10^40
        + 6334693940189995484374181592917130138923) * 10^40
        + 3408057392026289924772326357929826553865) * 10^40
        + 5038863888396889573570210177451121050453) * 10^40
        + 7446382091652954241718034847407953464465) * 10^40
        + 2918028670707235358713448381122512311437) * 10^40
        + 6321940978386572751188073664113388027904)),
    ((((((((((38534765099606 * 10^40
        + 4998898194049997188971381910728076102454) * 10^40
        + 335304633884581959712558678654863684455) * 10^40
        + 9579891794657936743541626114003730338805) * 10^40
        + 2957155854290257196850395857618984862285) * 10^40
        + 2518724482341889013289875955135292864540) * 10^40
        + 1655778784265161595806912677765944641232) * 10^40
        + 7504107622081059099253474961332364398092) * 10^40
        + 2125986314964341210006123162053506211401) : ℚ) /
        ((((((((77275449 * 10^40
        + 7830305273779264133913587505151256308232) * 10^40
        + 457093254262169530597003051905444748487) * 10^40
        + 1741565326025753364566729857809563414150) * 10^40
        + 3580869077533009245434280331287024509496) * 10^40
        + 8066477756255042037642429043196503747501) * 10^40
        + 4927386678473045265531378485746762778657) * 10^40
        + 9436802503187790090030227231887377180349) * 10^40
        + 6157360530868952841847697772648914223104)))

noncomputable def pairedN05440MinusP029Error2553 : ℝ := ((22065251884334472186547917618333 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem pairedN05440MinusP029BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP029Center2553‖ ≤ pairedN05440MinusP029Error2553 := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN05440MinusP029Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN05440MinusP029Input2553]
  have hs : compactExp2547 pairedN05440MinusP029Input2553 6 =
      (pairedN05440MinusP029Center2553, ((22065251884334472186547917618333 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN05440MinusP029Input2553 6).2 : ℝ) =
      pairedN05440MinusP029Error2553
      := by
    rw [hs]
    norm_num [pairedN05440MinusP029Error2553]
  have h := compactExp_error2547 pairedN05440MinusP029Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      pairedN05440MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN05440MinusP029Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN05440MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN05440MinusP029Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN05440MinusP029DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN05440MinusPosition2553
        -
      embedPair2542 pairedN05440MinusP029Factor2553 * embedPair2542
          pairedN05440MinusP029Center2553‖ ≤
        (pairMagnitude2542 pairedN05440MinusP029Factor2553 : ℝ) * pairedN05440MinusP029Error2553
            := by
  have hx : |pairedN05440MinusPosition2553| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [pairedN05440MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) pairedN05440MinusPosition2553 = embedPair2542
          pairedN05440MinusP029Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN05440MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN05440MinusP029Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN05440MinusP029BaseError2553
    (embedPair_magnitude2542 pairedN05440MinusP029Factor2553)

theorem pairedN05440MinusGrid2553 :
    -stripRadius2303 + (5440 : ℝ) * (2 * stripRadius2303 / 10240) =
      pairedN05440MinusPosition2553 := by
  norm_num [stripRadius2303, pairedN05440MinusPosition2553]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.pairedN05440MinusP000DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP001DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP002DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP003DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP004DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP005DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP006DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP007DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP008DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP009DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP010DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP011DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP012DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP013DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP014DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP015DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP016DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP017DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP018DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP019DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP020DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP021DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP022DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP023DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP024DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP025DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP026DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP027DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP028DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusP029DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN05440MinusGrid2553
