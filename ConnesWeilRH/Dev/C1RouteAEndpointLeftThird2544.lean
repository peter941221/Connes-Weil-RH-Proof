import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def endpointLeftPosition2544 : ℝ := ((65536001 : ℝ) /
        160000000)

def endpointLeftP000Input2544 : RatPair2542 :=
  ((((-((32 * 10^40
        + 6911763763220111443585096710647091568765) * 10^40
        + 8030436439533111481004726762137450891693)) : ℚ) /
        ((68 * 10^40
        + 4108646130446117391380318820003814069094) * 10^40
        + 5827290179342624543465749633167360000000)),
    (((-362039942185747774262029) : ℚ) /
        1441151880758558720000000))

def endpointLeftP000Center2544 : RatPair2542 :=
  ((((-30858366022552697) : ℚ) /
        633825300114114700748351602688),
    ((23926281498988875 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointLeftP000Error2544 : ℝ := ((39654207116799 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP000Factor2544 : RatPair2542 :=
  ((((((((((((((237838029322047241572873 * 10^40
        + 19765206418150337552917579277335509671) * 10^40
        + 5332881280706128872460719061377748358725) * 10^40
        + 5462252879485368562806203022698260613592) * 10^40
        + 9507672179629706616740143231981790155009) * 10^40
        + 9778792599614145261793052789736203436801) * 10^40
        + 3939118959171556555054966911359552693010) * 10^40
        + 5332280920543346867398333648366721146420) * 10^40
        + 2869678931650727988688309931715833466304) * 10^40
        + 1972330708974431120077224188119185307319) * 10^40
        + 7364029696441619332581014370933476558353) * 10^40
        + 9257148209421931924608861952854296745679) : ℚ) /
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
    ((((((((((20939049923664 * 10^40
        + 6283673815508191346113553895469214333739) * 10^40
        + 3456068922743845063377583308469921640981) * 10^40
        + 1872922643956721482842549669487092488482) * 10^40
        + 5098213336758552515822415762919582438256) * 10^40
        + 4724145468482724722239197484382979916333) * 10^40
        + 5850356935151044272039794614054742883303) * 10^40
        + 5402025701389378008951888439092702017320) * 10^40
        + 202610730251155699801961853403903646437) : ℚ) /
        ((((((((347064262 * 10^40
        + 7567007173867870115569880478991789728245) * 10^40
        + 6760705912975754929199920984881470359745) * 10^40
        + 8467471475072895805471424614794166971503) * 10^40
        + 5061188735027225722550733722517957416696) * 10^40
        + 1560718208491165579514798473885035339480) * 10^40
        + 5092715512281319322962596680044233098605) * 10^40
        + 7399419053698630897699024853701654451303) * 10^40
        + 1296852544043064379504336483176836759552)))

theorem endpointLeftP000BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP000Center2544‖ ≤ endpointLeftP000Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP000Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP000Input2544]
  have hc : (compactExp2542 endpointLeftP000Input2544 6).1 = endpointLeftP000Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP000Input2544 6).2 : ℝ) = endpointLeftP000Error2544 := by
    have hq : (compactExp2542 endpointLeftP000Input2544 6).2 =
        ((39654207116799 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP000Error2544]
  have h := compactExp_error2542 endpointLeftP000Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP000Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP000Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP000DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP000Factor2544 * embedPair2542 endpointLeftP000Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP000Factor2544 : ℝ) * endpointLeftP000Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨0, by omega⟩)
      (storedWidth ⟨0, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP000Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP000Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨0, by omega⟩) (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP000BaseError2544
    (embedPair_magnitude2542 endpointLeftP000Factor2544)

def endpointLeftP001Input2544 : RatPair2542 :=
  ((((-(418745829535285177504639993717831830075 * 10^40
        + 5441618534605682304357047648610637783799)) : ℚ) /
        (886210261626655755083735189233369746668 * 10^40
        + 3797746372915947800471746154516480000000)),
    (((-362039942185747774262029) : ℚ) /
        1441151880758558720000000))

def endpointLeftP001Center2544 : RatPair2542 :=
  ((((-86930010245736943) : ℚ) /
        1267650600228229401496703205376),
    ((1053154381178083 : ℚ) /
        39614081257132168796771975168))

noncomputable def endpointLeftP001Error2544 : ℝ := ((54674242154227 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP001Factor2544 : RatPair2542 :=
  ((((((((((((((20591 * 10^40
        + 9139937792313599485969881485548315684323) * 10^40
        + 992267673396713460701828624909231001122) * 10^40
        + 4795825281737399986202987712143689782410) * 10^40
        + 3067677955603572599476774697990667988886) * 10^40
        + 698629118410227078416936001448656510105) * 10^40
        + 5873343167159341961192589722156359702118) * 10^40
        + 5617300499716656695669933590892926265424) * 10^40
        + 8668396081307034214850884347834790920311) * 10^40
        + 6768571550231504213949830224989943153123) * 10^40
        + 6971434356810340214434435467925771011228) * 10^40
        + 5083494245679665782046570786557344449973) : ℚ) /
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
    ((((((((((59 * 10^40
        + 4309564309124148459436583436867434248794) * 10^40
        + 5282632587692368794256925546487031974227) * 10^40
        + 8894048046410632020102510243872451956993) * 10^40
        + 1144083782346571503402810130124260600885) * 10^40
        + 7126002144024823573137266994118315950439) * 10^40
        + 7967172181214379573437386764334353489654) * 10^40
        + 127344834380718360001224746499953377451) * 10^40
        + 5368325951205869646982296522309448794037) : ℚ) /
        (((((((9773647633404747718875879981514886715 * 10^40
        + 8603685856436692169309093239966098853839) * 10^40
        + 7656999226396869036009767818903745503705) * 10^40
        + 3313684529912668061111093298939113317831) * 10^40
        + 5706621653075060341119322492496743759866) * 10^40
        + 5852330712503776286664116254491248412679) * 10^40
        + 2012987523270991628535820178817129352001) * 10^40
        + 4667580454374216993044141776915138609152)))

theorem endpointLeftP001BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP001Center2544‖ ≤ endpointLeftP001Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP001Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP001Input2544]
  have hc : (compactExp2542 endpointLeftP001Input2544 6).1 = endpointLeftP001Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP001Input2544 6).2 : ℝ) = endpointLeftP001Error2544 := by
    have hq : (compactExp2542 endpointLeftP001Input2544 6).2 =
        ((54674242154227 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP001Error2544]
  have h := compactExp_error2542 endpointLeftP001Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP001Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP001Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP001DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP001Factor2544 * embedPair2542 endpointLeftP001Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP001Factor2544 : ℝ) * endpointLeftP001Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP001Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP001Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP001BaseError2544
    (embedPair_magnitude2542 endpointLeftP001Factor2544)

def endpointLeftP002Input2544 : RatPair2542 :=
  ((((-((1 * 10^40
        + 940460184190943091815756058773640907463) * 10^40
        + 6041868381241635646677598458916444775159)) : ℚ) /
        ((2 * 10^40
        + 3288003241060619496441480162260487009338) * 10^40
        + 6963595085534041865672938472263680000000)),
    ((362039942185747774262029 : ℚ) /
        1441151880758558720000000))

def endpointLeftP002Center2544 : RatPair2542 :=
  ((((-25870618901970091) : ℚ) /
        316912650057057350374175801344),
    (((-10029495890177959) : ℚ) /
        316912650057057350374175801344))

noncomputable def endpointLeftP002Error2544 : ℝ := ((64496229382583 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP002Factor2544 : RatPair2542 :=
  ((((((((((((((3318537706058 * 10^40
        + 9322104281790814226070240675697939955444) * 10^40
        + 3728231529901959664725744806387654056563) * 10^40
        + 4939804703635433711256998726338039599233) * 10^40
        + 2978107271543757702451817098115735746203) * 10^40
        + 2114287008645952736453988144518093661790) * 10^40
        + 5418237476781445439226687714136629987654) * 10^40
        + 3951057959029540932341795828618432197718) * 10^40
        + 5491498179424711015568957860828044310249) * 10^40
        + 7520883174688701699515902488226012523479) * 10^40
        + 7297585402219892909969979531731813832796) * 10^40
        + 4272096666470326957257621204732631418293) : ℚ) /
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
    (((-((((((((28333517 * 10^40
        + 8471587419745893268937243870888221662131) * 10^40
        + 9823969953912817593340071394413392074182) * 10^40
        + 9761766775359402061323842820129787965197) * 10^40
        + 1243899896633783544237796398178363616492) * 10^40
        + 8286197571055766514619613359285240078616) * 10^40
        + 9912365658655991393824421276866751076117) * 10^40
        + 5134032108637393878077217608360267502871) * 10^40
        + 8643217184612246013207549578170199211957)) : ℚ) /
        ((((((((466 * 10^40
        + 565230973624133558526167779360043636572) * 10^40
        + 4109669601874930549670219492506828262102) * 10^40
        + 3941139014796456452997852262342750741367) * 10^40
        + 735739778948538230406697993137601521364) * 10^40
        + 5672678517938210646571290218421409642190) * 10^40
        + 6831995526851481057226898214491419635051) * 10^40
        + 3938883756142930537586701324526589209838) * 10^40
        + 9811867037956618140370659910523889385472)))

theorem endpointLeftP002BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP002Center2544‖ ≤ endpointLeftP002Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP002Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP002Input2544]
  have hc : (compactExp2542 endpointLeftP002Input2544 6).1 = endpointLeftP002Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP002Input2544 6).2 : ℝ) = endpointLeftP002Error2544 := by
    have hq : (compactExp2542 endpointLeftP002Input2544 6).2 =
        ((64496229382583 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP002Error2544]
  have h := compactExp_error2542 endpointLeftP002Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP002Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP002Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP002DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP002Factor2544 * embedPair2542 endpointLeftP002Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP002Factor2544 : ℝ) * endpointLeftP002Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP002Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP002Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP002BaseError2544
    (embedPair_magnitude2542 endpointLeftP002Factor2544)

def endpointLeftP003Input2544 : RatPair2542 :=
  ((((-((144 * 10^40
        + 4918766017205838150183104107479631936812) * 10^40
        + 9508214248915683763619074813602294641693)) : ℚ) /
        ((308 * 10^40
        + 5584325157930343245986452666829032621960) * 10^40
        + 3552613615865160449465749633167360000000)),
    ((362039942185747774262029 : ℚ) /
        1441151880758558720000000))

def endpointLeftP003Center2544 : RatPair2542 :=
  ((((-56987816639837217) : ℚ) /
        633825300114114700748351602688),
    (((-44185960524967363) : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointLeftP003Error2544 : ℝ := ((70709719318829 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP003Factor2544 : RatPair2542 :=
  ((((((((((((((207382870652043851992645260 * 10^40
        + 6034377856267861689925454502009333002129) * 10^40
        + 812278517279635830899987961490323019664) * 10^40
        + 9524913583977079844996780171030294096570) * 10^40
        + 9452143555339354710047434857472024821606) * 10^40
        + 5289754309587276709281158657666438830785) * 10^40
        + 5952903174763333498272393825928765625773) * 10^40
        + 4583686984217602872535223632975244839863) * 10^40
        + 612397765655354929324678946793995679905) * 10^40
        + 9872630467502433248721004965312678595252) * 10^40
        + 7831599366140704503389097822790087452684) * 10^40
        + 896861879049809243649087269846484245679) : ℚ) /
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
    (((-((((((((26162666668258273 * 10^40
        + 5878347506809155196151519261998112775802) * 10^40
        + 5749365923675897389748555452904134327389) * 10^40
        + 7923469537609424194593069891862331564835) * 10^40
        + 8097615687863490351305063197239968978242) * 10^40
        + 9096451984905505735800095381671825075935) * 10^40
        + 8416026113189694295757169348285005485823) * 10^40
        + 7987879233583003466421837242791571837701) * 10^40
        + 5741778930542561717332197540289835939311)) : ℚ) /
        ((((((((430903987195 * 10^40
        + 3036787996556007758858814067267494701812) * 10^40
        + 6891598905072457433128610262366956806589) * 10^40
        + 8914893803172754733750964915752643487035) * 10^40
        + 8993085148896280809115752769810975610103) * 10^40
        + 8483110465154781377284322090760779172148) * 10^40
        + 7037556954431239915791614970073949997245) * 10^40
        + 7692066781036377233723245227017918329579) * 10^40
        + 8436973621523872836176599849530510278656)))

theorem endpointLeftP003BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP003Center2544‖ ≤ endpointLeftP003Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP003Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP003Input2544]
  have hc : (compactExp2542 endpointLeftP003Input2544 6).1 = endpointLeftP003Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP003Input2544 6).2 : ℝ) = endpointLeftP003Error2544 := by
    have hq : (compactExp2542 endpointLeftP003Input2544 6).2 =
        ((70709719318829 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP003Error2544]
  have h := compactExp_error2542 endpointLeftP003Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP003Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP003Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP003DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP003Factor2544 * embedPair2542 endpointLeftP003Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP003Factor2544 : ℝ) * endpointLeftP003Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP003Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP003Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP003BaseError2544
    (embedPair_magnitude2542 endpointLeftP003Factor2544)

def endpointLeftP004Input2544 : RatPair2542 :=
  ((((-((2 * 10^40
        + 5103080337848704906504593856765472646849) * 10^40
        + 7747772204514785261573073475518007275159)) : ℚ) /
        ((5 * 10^40
        + 3709268744536454894037321260456311664067) * 10^40
        + 5409328121924953525672938472263680000000)),
    (((-362039942185747774262029) : ℚ) /
        1441151880758558720000000))

def endpointLeftP004Center2544 : RatPair2542 :=
  ((((-60336558659991183) : ℚ) /
        633825300114114700748351602688),
    ((46782434498447973 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointLeftP004Error2544 : ℝ := ((37335442720627 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def endpointLeftP004Factor2544 : RatPair2542 :=
  ((((((((((((((45711498023022 * 10^40
        + 6655554503231325525499925117554119529856) * 10^40
        + 768479761166179097262008906615960981464) * 10^40
        + 8918324197333792295444364648908334397648) * 10^40
        + 4582801049446080492121149661079393947280) * 10^40
        + 4949404354347280186684721701883944366932) * 10^40
        + 5888057601331823828364836154818666168410) * 10^40
        + 116183300794888071359170650264254456117) * 10^40
        + 6360455976471478385752233002416338547969) * 10^40
        + 1608057906383019736633209227220406108260) * 10^40
        + 6709208749698893213109805582053009402599) * 10^40
        + 9545696735985124424801861003560756418293) : ℚ) /
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
    ((((((((((799667460 * 10^40
        + 661653465405721209120986097945005890313) * 10^40
        + 9054574708915023151645054595518682792205) * 10^40
        + 2295053531101043710186863451083149424935) * 10^40
        + 5766203203999626356574350628784883447454) * 10^40
        + 7397443101331529723814228744223939378105) * 10^40
        + 7296729791756652387867600656098119442977) * 10^40
        + 8700714397218793180440760634584286316658) * 10^40
        + 1878124109025388252079836652388949211957) : ℚ) /
        ((((((((13185 * 10^40
        + 8016127353611814584171637125180201618495) * 10^40
        + 4959964127337556780442070131620983631468) * 10^40
        + 6661489113779641054622051588439612160968) * 10^40
        + 2770548086944166362669149970776464771112) * 10^40
        + 4591050674598677700135077169087520748449) * 10^40
        + 3519428327567097900729427518176852050843) * 10^40
        + 6521141887531967185265903260493976329157) * 10^40
        + 3227727773227200841369315910523889385472)))

theorem endpointLeftP004BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP004Center2544‖ ≤ endpointLeftP004Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP004Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP004Input2544]
  have hc : (compactExp2542 endpointLeftP004Input2544 6).1 = endpointLeftP004Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP004Input2544 6).2 : ℝ) = endpointLeftP004Error2544 := by
    have hq : (compactExp2542 endpointLeftP004Input2544 6).2 =
        ((37335442720627 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [endpointLeftP004Error2544]
  have h := compactExp_error2542 endpointLeftP004Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP004Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP004Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP004DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP004Factor2544 * embedPair2542 endpointLeftP004Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP004Factor2544 : ℝ) * endpointLeftP004Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP004Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP004Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP004BaseError2544
    (embedPair_magnitude2542 endpointLeftP004Factor2544)

def endpointLeftP005Input2544 : RatPair2542 :=
  ((((-((119 * 10^40
        + 2052691919609525638601444604262212764412) * 10^40
        + 5534546308631277754165410040806883925079)) : ℚ) /
        ((125 * 10^40
        + 3117539759639451663790354394338218649327) * 10^40
        + 8796645127269504130198624449751040000000)),
    ((0 : ℚ) /
        1))

def endpointLeftP005Center2544 : RatPair2542 :=
  (((19087206308435669 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def endpointLeftP005Error2544 : ℝ := ((9153803216799 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP005Factor2544 : RatPair2542 :=
  (((((((((((((119190335926871954255637425621965903 * 10^40
        + 1100717258376920834712834139478925431512) * 10^40
        + 977928138428650703370826825888541217987) * 10^40
        + 1137725042616640240008152433495025006994) * 10^40
        + 1539993409496797384150060662611526441284) * 10^40
        + 1750889267379058669513414187266680314785) * 10^40
        + 5470491962998366168495752627299563491822) * 10^40
        + 4531686883191774194609573691288114945675) * 10^40
        + 5220206834315387490720310531701705369492) * 10^40
        + 1845553985379968911265104567880298597073) * 10^40
        + 1591421712469185468582524199352569369521) : ℚ) /
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

theorem endpointLeftP005BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP005Center2544‖ ≤ endpointLeftP005Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP005Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP005Input2544]
  have hc : (compactExp2542 endpointLeftP005Input2544 5).1 = endpointLeftP005Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP005Input2544 5).2 : ℝ) = endpointLeftP005Error2544 := by
    have hq : (compactExp2542 endpointLeftP005Input2544 5).2 =
        ((9153803216799 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP005Error2544]
  have h := compactExp_error2542 endpointLeftP005Input2544 hz 5
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^5 * embedPair2542 endpointLeftP005Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP005Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP005DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP005Factor2544 * embedPair2542 endpointLeftP005Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP005Factor2544 : ℝ) * endpointLeftP005Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨5, by omega⟩)
      (storedWidth ⟨5, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP005Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP005Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨5, by omega⟩) (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP005BaseError2544
    (embedPair_magnitude2542 endpointLeftP005Factor2544)

def endpointLeftP006Input2544 : RatPair2542 :=
  ((((-1301865976326665186028202667) : ℚ) /
        1383441177848927569920000000),
    ((0 : ℚ) /
        1))

def endpointLeftP006Center2544 : RatPair2542 :=
  (((105936024065733223 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def endpointLeftP006Error2544 : ℝ := ((5875350411947 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def endpointLeftP006Factor2544 : RatPair2542 :=
  (((((136139772465521927709209199 * 10^40
        + 43336996798618413509185553923419951037) * 10^40
        + 5576266247671356152434820153043048978963) : ℚ) /
        ((13134640807505800999788842 * 10^40
        + 4136026660720274558531709965293476242922) * 10^40
        + 7195280675955333059478561224344391831704)),
    ((0 : ℚ) /
        1))

theorem endpointLeftP006BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP006Center2544‖ ≤ endpointLeftP006Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP006Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP006Input2544]
  have hc : (compactExp2542 endpointLeftP006Input2544 5).1 = endpointLeftP006Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP006Input2544 5).2 : ℝ) = endpointLeftP006Error2544 := by
    have hq : (compactExp2542 endpointLeftP006Input2544 5).2 =
        ((5875350411947 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [endpointLeftP006Error2544]
  have h := compactExp_error2542 endpointLeftP006Input2544 hz 5
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^5 * embedPair2542 endpointLeftP006Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP006Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP006DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP006Factor2544 * embedPair2542 endpointLeftP006Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP006Factor2544 : ℝ) * endpointLeftP006Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP006Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP006Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP006BaseError2544
    (embedPair_magnitude2542 endpointLeftP006Factor2544)

def endpointLeftP007Input2544 : RatPair2542 :=
  ((((-((144 * 10^40
        + 4918766017205838150183104107479631936812) * 10^40
        + 9508214248915683763619074813602294641693)) : ℚ) /
        ((154 * 10^40
        + 2792162578965171622993226333414516310980) * 10^40
        + 1776306807932580224732874816583680000000)),
    ((0 : ℚ) /
        1))

def endpointLeftP007Center2544 : RatPair2542 :=
  (((122240926407716675 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def endpointLeftP007Error2544 : ℝ := ((1646453414559 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

def endpointLeftP007Factor2544 : RatPair2542 :=
  (((((((((((((479141696558335727820180830833655286 * 10^40
        + 3084357191539685714055335403190915152640) * 10^40
        + 7048797807258426102026009002497592603929) * 10^40
        + 9828096356726162576995819376872770148586) * 10^40
        + 2880527219862520935470902871708118079638) * 10^40
        + 1945915926779396898687769895445377863323) * 10^40
        + 4978557559110161039792468404963638387586) * 10^40
        + 514259896902468644336281282580856028449) * 10^40
        + 4959662622389716578793279931397080108784) * 10^40
        + 1592150618216359011765305736470762410119) * 10^40
        + 3221107689883289665545444362938984050723) : ℚ) /
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

theorem endpointLeftP007BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP007Center2544‖ ≤ endpointLeftP007Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP007Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP007Input2544]
  have hc : (compactExp2542 endpointLeftP007Input2544 5).1 = endpointLeftP007Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP007Input2544 5).2 : ℝ) = endpointLeftP007Error2544 := by
    have hq : (compactExp2542 endpointLeftP007Input2544 5).2 =
        ((1646453414559 : ℚ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472)) := by cbv
    rw [hq]
    norm_num [endpointLeftP007Error2544]
  have h := compactExp_error2542 endpointLeftP007Input2544 hz 5
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^5 * embedPair2542 endpointLeftP007Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP007Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP007DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP007Factor2544 * embedPair2542 endpointLeftP007Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP007Factor2544 : ℝ) * endpointLeftP007Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP007Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP007Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP007BaseError2544
    (embedPair_magnitude2542 endpointLeftP007Factor2544)

def endpointLeftP008Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-260739661220379310273297) : ℚ) /
        2882303761517117440000000))

def endpointLeftP008Center2544 : RatPair2542 :=
  (((37584419704424455 : ℚ) /
        633825300114114700748351602688),
    ((10110652316150125 : ℚ) /
        316912650057057350374175801344))

noncomputable def endpointLeftP008Error2544 : ℝ := ((32251369786171 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP008Factor2544 : RatPair2542 :=
  ((((((((((((((813384531785706729834493 * 10^40
        + 7575711562727230052118348564383156936753) * 10^40
        + 2697519472589122011038954109057115082175) * 10^40
        + 8462593944358954547045137942757042653491) * 10^40
        + 785686147593035035246453590208687720149) * 10^40
        + 9366616217318455682738493494520914766066) * 10^40
        + 3763379188360006894101186683397244641608) * 10^40
        + 7620264819850914997836595766894952495541) * 10^40
        + 5361609367328218096267004981478863493428) * 10^40
        + 5358123076936216976797603033368239691440) * 10^40
        + 9716035923137939733332710388320490981081) * 10^40
        + 7917293316126178078897220459090902781911) : ℚ) /
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
    ((((((((((115593511045112 * 10^40
        + 3017688749978081689119624191689906708956) * 10^40
        + 2903099219847527160421627993450035445375) * 10^40
        + 2937205886243099990497069878916690135590) * 10^40
        + 2788913148706777111418363686270053221650) * 10^40
        + 5206836060177306673283812007368966672314) * 10^40
        + 4743768815584013442990300280104786550680) * 10^40
        + 9896132993287540280492187423293152892669) * 10^40
        + 4579609527732526127169652914106352229187) : ℚ) /
        ((((((((39565030288 * 10^40
        + 9116300174983236563756802637443229814807) * 10^40
        + 4031746182230799665665562575587711225433) * 10^40
        + 1681446925185722658165687198496468044983) * 10^40
        + 3404967696900733662351529618956548862365) * 10^40
        + 36611202581523272923670116609918720764) * 10^40
        + 2821979378199175952065784702342542672867) * 10^40
        + 1642881632148526095476342726337116339003) * 10^40
        + 2568591804903855026021259596244082229248)))

theorem endpointLeftP008BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP008Center2544‖ ≤ endpointLeftP008Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP008Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP008Input2544]
  have hc : (compactExp2542 endpointLeftP008Input2544 6).1 = endpointLeftP008Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP008Input2544 6).2 : ℝ) = endpointLeftP008Error2544 := by
    have hq : (compactExp2542 endpointLeftP008Input2544 6).2 =
        ((32251369786171 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP008Error2544]
  have h := compactExp_error2542 endpointLeftP008Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP008Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP008Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP008DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP008Factor2544 * embedPair2542 endpointLeftP008Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP008Factor2544 : ℝ) * endpointLeftP008Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP008Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP008Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP008BaseError2544
    (embedPair_magnitude2542 endpointLeftP008Factor2544)

def endpointLeftP009Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-387788191040974601829711) : ℚ) /
        2882303761517117440000000))

def endpointLeftP009Center2544 : RatPair2542 :=
  ((((-29298495678051691) : ℚ) /
        633825300114114700748351602688),
    (((-31033657801712695) : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointLeftP009Error2544 : ℝ := ((23670158132947 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def endpointLeftP009Factor2544 : RatPair2542 :=
  ((((((((((((((1775792577413529818830354 * 10^40
        + 6023431662116726800804996551528128911631) * 10^40
        + 2648327152699197738113669281687335883308) * 10^40
        + 9519077844723766152570466220026715786136) * 10^40
        + 9737138136522306657318327206269827199151) * 10^40
        + 2560052636036124186606288924901167735027) * 10^40
        + 5312609461094252362575855708159525719767) * 10^40
        + 2387853825245117071452908592198440086224) * 10^40
        + 7141377252310152766570319255375751014227) * 10^40
        + 526380603527641790550633535425776296839) * 10^40
        + 6002675937415168161310406578750998242352) * 10^40
        + 7950948371063293186251326267357873004183) : ℚ) /
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
    ((((((((((124437069269861 * 10^40
        + 5808100553495674887589599359121733986287) * 10^40
        + 6970411249600704156630447991413807311976) * 10^40
        + 3273527022280705697364836658471587714065) * 10^40
        + 3900751806335866445641662049754941230432) * 10^40
        + 3460721822221504770532955550805446638698) * 10^40
        + 217634936083471717337113004814021460743) * 10^40
        + 1109225256802245404788888432047773250379) * 10^40
        + 3201469530090855318947919460177407825759) : ℚ) /
        ((((((((13188343429 * 10^40
        + 6372100058327745521252267545814409938269) * 10^40
        + 1343915394076933221888520858529237075144) * 10^40
        + 3893815641728574219388562399498822681661) * 10^40
        + 1134989232300244554117176539652182954121) * 10^40
        + 6678870400860507757641223372203306240254) * 10^40
        + 7607326459399725317355261567447514224289) * 10^40
        + 547627210716175365158780908779038779667) * 10^40
        + 7522863934967951675340419865414694076416)))

theorem endpointLeftP009BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP009Center2544‖ ≤ endpointLeftP009Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP009Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP009Input2544]
  have hc : (compactExp2542 endpointLeftP009Input2544 6).1 = endpointLeftP009Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP009Input2544 6).2 : ℝ) = endpointLeftP009Error2544 := by
    have hq : (compactExp2542 endpointLeftP009Input2544 6).2 =
        ((23670158132947 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [endpointLeftP009Error2544]
  have h := compactExp_error2542 endpointLeftP009Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP009Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP009Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP009DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP009Factor2544 * embedPair2542 endpointLeftP009Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP009Factor2544 : ℝ) * endpointLeftP009Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP009Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP009Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP009BaseError2544
    (embedPair_magnitude2542 endpointLeftP009Factor2544)

def endpointLeftP010Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-230684447942438333698521) : ℚ) /
        1441151880758558720000000))

def endpointLeftP010Center2544 : RatPair2542 :=
  ((((-29126773493373607) : ℚ) /
        633825300114114700748351602688),
    ((31194884699519655 : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointLeftP010Error2544 : ℝ := ((46549267981635 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP010Factor2544 : RatPair2542 :=
  ((((((((((((((626401963966919747242695 * 10^40
        + 6818252489426576587127181821068064246747) * 10^40
        + 950962493213129432547235964800804081416) * 10^40
        + 6578220621687577950334190016013048212804) * 10^40
        + 5698002054932527925169015241759111753386) * 10^40
        + 5196072982568878261858674968771275916916) * 10^40
        + 9477746525444244731785507350651720289798) * 10^40
        + 8962772402740453320016755659501907708465) * 10^40
        + 7383378227186710698548732637165673800247) * 10^40
        + 9951007256588141983279385512965449563568) * 10^40
        + 7290555509750007826589274359682146935570) * 10^40
        + 9570570314768179636503860120925851334279) : ℚ) /
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
    ((((((((((2897425990820 * 10^40
        + 221478651151429389273259645483398651524) * 10^40
        + 2549184804399325192652550596143201165441) * 10^40
        + 7350767670218696353713218586342928452217) * 10^40
        + 7301348908330673941232278944036498865527) * 10^40
        + 8886752216137621811560162864030496436099) * 10^40
        + 4622753217503309799184702336751936685807) * 10^40
        + 546335010688075470135317440203113845881) * 10^40
        + 4963097240110649539231926409634486402257) : ℚ) /
        ((((((((183171436 * 10^40
        + 5227390278587885354461837049247422360253) * 10^40
        + 7379776602695512961415118345257350514932) * 10^40
        + 5609636328357341308602618922215261426134) * 10^40
        + 1821319294893058952140516340828502541029) * 10^40
        + 4676095422234173718856128102391712586670) * 10^40
        + 2050101756380551740518823077325659919781) * 10^40
        + 7924272600148835768960538623733042205273) * 10^40
        + 1632261999096777106601950275908537417728)))

theorem endpointLeftP010BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP010Center2544‖ ≤ endpointLeftP010Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP010Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP010Input2544]
  have hc : (compactExp2542 endpointLeftP010Input2544 6).1 = endpointLeftP010Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP010Input2544 6).2 : ℝ) = endpointLeftP010Error2544 := by
    have hq : (compactExp2542 endpointLeftP010Input2544 6).2 =
        ((46549267981635 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP010Error2544]
  have h := compactExp_error2542 endpointLeftP010Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP010Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP010Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP010DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP010Factor2544 * embedPair2542 endpointLeftP010Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP010Factor2544 : ℝ) * endpointLeftP010Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP010Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP010Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP010BaseError2544
    (embedPair_magnitude2542 endpointLeftP010Factor2544)

def endpointLeftP011Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-255213677437476200797801) : ℚ) /
        1441151880758558720000000))

def endpointLeftP011Center2544 : RatPair2542 :=
  (((28320014124553967 : ℚ) /
        1267650600228229401496703205376),
    ((80522890299513783 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointLeftP011Error2544 : ℝ := ((42748580416135 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP011Factor2544 : RatPair2542 :=
  ((((((((((((((765618267676720300441441 * 10^40
        + 7987107570815482667563027873705691930547) * 10^40
        + 4329068642140943034199350838942963933320) * 10^40
        + 9071468363311121236187248179917876863547) * 10^40
        + 7774408237976598551259616453710926405286) * 10^40
        + 6568151878387762491537330668185093688493) * 10^40
        + 4120961805890794939245708655402202265561) * 10^40
        + 5924831802128417229853472192386221830536) * 10^40
        + 7246511075962839517410702132220784985428) * 10^40
        + 9236110340120615430883466067518789356807) * 10^40
        + 8465900694587063982936799229404408508117) * 10^40
        + 5701646783061511020747955420192046555239) : ℚ) /
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
    ((((((((((105721731567273 * 10^40
        + 9565656101214259491638204783138796235145) * 10^40
        + 6734053853809543752635529095221287085503) * 10^40
        + 6769661988238366702452426508767843424656) * 10^40
        + 545484520427589382895690978708158792796) * 10^40
        + 411920919548064329070292028071846224269) * 10^40
        + 7035377230692245928147472159815207526156) * 10^40
        + 7931381237612344623265857098292646215543) * 10^40
        + 8393884075364348492714332229949549222939) : ℚ) /
        ((((((((4945628786 * 10^40
        + 1139537521872904570469600329680403726850) * 10^40
        + 9253968272778849958208195321948463903179) * 10^40
        + 1460180865648215332270710899812058505622) * 10^40
        + 9175620962112591707793941202369568607795) * 10^40
        + 6254576400322690409115458764576239840095) * 10^40
        + 5352747422274896994008223087792817834108) * 10^40
        + 3955360204018565761934542840792139542375) * 10^40
        + 4071073975612981878252657449530510278656)))

theorem endpointLeftP011BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP011Center2544‖ ≤ endpointLeftP011Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP011Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP011Input2544]
  have hc : (compactExp2542 endpointLeftP011Input2544 6).1 = endpointLeftP011Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP011Input2544 6).2 : ℝ) = endpointLeftP011Error2544 := by
    have hq : (compactExp2542 endpointLeftP011Input2544 6).2 =
        ((42748580416135 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP011Error2544]
  have h := compactExp_error2542 endpointLeftP011Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP011Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP011Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP011DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP011Factor2544 * embedPair2542 endpointLeftP011Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP011Factor2544 : ℝ) * endpointLeftP011Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP011Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP011Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP011BaseError2544
    (embedPair_magnitude2542 endpointLeftP011Factor2544)

def endpointLeftP012Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-5612399119318874813509) : ℚ) /
        28823037615171174400000))

def endpointLeftP012Center2544 : RatPair2542 :=
  (((84893602246253523 : ℚ) /
        1267650600228229401496703205376),
    ((8890183342168253 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointLeftP012Error2544 : ℝ := ((12514615859921 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def endpointLeftP012Factor2544 : RatPair2542 :=
  ((((((((((((((231157758568366635490124 * 10^40
        + 5368152983908549917688912479031469662191) * 10^40
        + 5805207332600836787541420026744162883738) * 10^40
        + 4720060339088575473304344878173894929197) * 10^40
        + 1776646978769019925376130029162800459132) * 10^40
        + 2175493973963293991292579177668890172568) * 10^40
        + 7489893685270399081468168516309597612869) * 10^40
        + 3818581400232054677770538736296688335495) * 10^40
        + 6338680625522473940417051063570084928498) * 10^40
        + 4891226798790440734508216102326448221509) * 10^40
        + 5290242438938564540532197965429674416230) * 10^40
        + 5025901497423149355433754603678484833327) : ℚ) /
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
    ((((((((((222033892874 * 10^40
        + 5052341723472268716858617011567282166303) * 10^40
        + 6073356435045574910428847559105049879816) * 10^40
        + 5655456270052100409970890211773449092389) * 10^40
        + 1291865419719940838230299881557489072941) * 10^40
        + 9677846847396073452926039354805113719586) * 10^40
        + 6353302256112922565273553488656276564624) * 10^40
        + 7552375081601485622015976304799764797849) * 10^40
        + 8258176865506384914004827021702036122225) : ℚ) /
        ((((((((7825362 * 10^40
        + 33448635319419152801375949888734816023) * 10^40
        + 4982996785241738686642734486268905797315) * 10^40
        + 1568766108964633252108023276740208953331) * 10^40
        + 6818315855952709797006003071522736659189) * 10^40
        + 5500402810760004256976448510703443417468) * 10^40
        + 5055937891490941292712038327670558256066) * 10^40
        + 6272081266145598996458757188039228068896) * 10^40
        + 1636188408189261047275716230141662199808)))

theorem endpointLeftP012BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP012Center2544‖ ≤ endpointLeftP012Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP012Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP012Input2544]
  have hc : (compactExp2542 endpointLeftP012Input2544 6).1 = endpointLeftP012Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP012Input2544 6).2 : ℝ) = endpointLeftP012Error2544 := by
    have hq : (compactExp2542 endpointLeftP012Input2544 6).2 =
        ((12514615859921 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [endpointLeftP012Error2544]
  have h := compactExp_error2542 endpointLeftP012Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP012Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP012Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP012DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP012Factor2544 * embedPair2542 endpointLeftP012Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP012Factor2544 : ℝ) * endpointLeftP012Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP012Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP012Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP012BaseError2544
    (embedPair_magnitude2542 endpointLeftP012Factor2544)

def endpointLeftP013Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-60754466143128272313291) : ℚ) /
        288230376151711744000000))

def endpointLeftP013Center2544 : RatPair2542 :=
  (((25725480424142777 : ℚ) /
        633825300114114700748351602688),
    (((-34054212991899601) : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointLeftP013Error2544 : ℝ := ((2524587552149 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

def endpointLeftP013Factor2544 : RatPair2542 :=
  ((((((((((((((1082668838602686718508562 * 10^40
        + 8065540159398779568182390632050154832870) * 10^40
        + 3911913238070102295240324059582998441875) * 10^40
        + 5427672041943082582119826538379941215639) * 10^40
        + 6416342738053234092260039313600422579865) * 10^40
        + 370411780779825212754179831642807878404) * 10^40
        + 3673664933156191734321510112607024042919) * 10^40
        + 9436976434665561876849442905892728533090) * 10^40
        + 6723030541453210892191827367051652542433) * 10^40
        + 7004408927610144979544297659149729334500) * 10^40
        + 4153164161238577937317768515551545399403) * 10^40
        + 7884146925364978322674742080310826828583) : ℚ) /
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
    ((((((((((59269630938981 * 10^40
        + 389720307254870907923755355616499281911) * 10^40
        + 3587515894119238462259172447922717130515) * 10^40
        + 1977368845926774454838092658123749742724) * 10^40
        + 2572628177575290044733785268552446874763) * 10^40
        + 2687163428766440536371925400580734993468) * 10^40
        + 6525189058867934656385108109198439947298) * 10^40
        + 3328566246134338913157958032387294251477) * 10^40
        + 2659279668912649051191613712477878925335) : ℚ) /
        ((((((((1648542928 * 10^40
        + 7046512507290968190156533443226801242283) * 10^40
        + 6417989424259616652736065107316154634393) * 10^40
        + 486726955216071777423570299937352835207) * 10^40
        + 6391873654037530569264647067456522869265) * 10^40
        + 2084858800107563469705152921525413280031) * 10^40
        + 8450915807424965664669407695930939278036) * 10^40
        + 1318453401339521920644847613597379847458) * 10^40
        + 4690357991870993959417552483176836759552)))

theorem endpointLeftP013BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP013Center2544‖ ≤ endpointLeftP013Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP013Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP013Input2544]
  have hc : (compactExp2542 endpointLeftP013Input2544 6).1 = endpointLeftP013Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP013Input2544 6).2 : ℝ) = endpointLeftP013Error2544 := by
    have hq : (compactExp2542 endpointLeftP013Input2544 6).2 =
        ((2524587552149 : ℚ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736)) := by cbv
    rw [hq]
    norm_num [endpointLeftP013Error2544]
  have h := compactExp_error2542 endpointLeftP013Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP013Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP013Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP013DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP013Factor2544 * embedPair2542 endpointLeftP013Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP013Factor2544 : ℝ) * endpointLeftP013Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP013Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP013Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP013BaseError2544
    (embedPair_magnitude2542 endpointLeftP013Factor2544)

def endpointLeftP014Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-346671309892138695845011) : ℚ) /
        1441151880758558720000000))

def endpointLeftP014Center2544 : RatPair2542 :=
  ((((-81219457813459147) : ℚ) /
        1267650600228229401496703205376),
    (((-26255641959209401) : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointLeftP014Error2544 : ℝ := ((5948224162945 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

def endpointLeftP014Factor2544 : RatPair2542 :=
  ((((((((((((((1408593781806869275418161 * 10^40
        + 7247867754120954396085300489450564709797) * 10^40
        + 2696846008084750881048213098236273902732) * 10^40
        + 7362002982762411021895762242412797488464) * 10^40
        + 3476552954271682736372809717703222236552) * 10^40
        + 3848510033883366180039893288686418072832) * 10^40
        + 184472091499555076525428607084949537489) * 10^40
        + 7261850207554485819825128505745618292921) * 10^40
        + 4682353289475749768953211664534299765686) * 10^40
        + 6475606600429380160764648744235690836662) * 10^40
        + 4230497977106862891298074199421423093426) * 10^40
        + 6617408526842680813019675389450369761359) : ℚ) /
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
    ((((((((((263890706716239 * 10^40
        + 4016156302155820657721827339286329728926) * 10^40
        + 9060260105955032042374140159930269750742) * 10^40
        + 5469260297410919200979195608151019621042) * 10^40
        + 3804271163886140215836624048051927148546) * 10^40
        + 4188070865315787572817712301399748742749) * 10^40
        + 7909332566642463530227703997113721180995) * 10^40
        + 612817620781256444608347691673008037153) * 10^40
        + 2127135201263649142652906257761393170289) : ℚ) /
        ((((((((4945628786 * 10^40
        + 1139537521872904570469600329680403726850) * 10^40
        + 9253968272778849958208195321948463903179) * 10^40
        + 1460180865648215332270710899812058505622) * 10^40
        + 9175620962112591707793941202369568607795) * 10^40
        + 6254576400322690409115458764576239840095) * 10^40
        + 5352747422274896994008223087792817834108) * 10^40
        + 3955360204018565761934542840792139542375) * 10^40
        + 4071073975612981878252657449530510278656)))

theorem endpointLeftP014BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP014Center2544‖ ≤ endpointLeftP014Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP014Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP014Input2544]
  have hc : (compactExp2542 endpointLeftP014Input2544 6).1 = endpointLeftP014Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP014Input2544 6).2 : ℝ) = endpointLeftP014Error2544 := by
    have hq : (compactExp2542 endpointLeftP014Input2544 6).2 =
        ((5948224162945 : ℚ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472)) := by cbv
    rw [hq]
    norm_num [endpointLeftP014Error2544]
  have h := compactExp_error2542 endpointLeftP014Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP014Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP014Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP014DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP014Factor2544 * embedPair2542 endpointLeftP014Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP014Factor2544 : ℝ) * endpointLeftP014Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP014Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP014Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP014BaseError2544
    (embedPair_magnitude2542 endpointLeftP014Factor2544)

def endpointLeftP015Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-377408574479356852679047) : ℚ) /
        1441151880758558720000000))

def endpointLeftP015Center2544 : RatPair2542 :=
  ((((-21148946663486405) : ℚ) /
        633825300114114700748351602688),
    ((37070363102829517 : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointLeftP015Error2544 : ℝ := ((58432555568759 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP015Factor2544 : RatPair2542 :=
  ((((((((((((((1668557456229944236314663 * 10^40
        + 8615366042541590558355252135893265774506) * 10^40
        + 9658045880494370160795326890085634068930) * 10^40
        + 3972037274702260905372984401151942015911) * 10^40
        + 7672815328058216320364147093254107596520) * 10^40
        + 5014093578406521876758797772284637741868) * 10^40
        + 6306116071940726046331193268926994470484) * 10^40
        + 3241366787093884604719223405754252718959) * 10^40
        + 2470775230053402933471624192297732284349) * 10^40
        + 3891762602642372542493551873898792356784) * 10^40
        + 3469840730875421503030832580614632870906) * 10^40
        + 2698276430383715080568545773003715932487) : ℚ) /
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
    ((((((((((340232193302103 * 10^40
        + 1234901143032797871684186173223403493882) * 10^40
        + 3716956511187885515114481639409714593560) * 10^40
        + 5758379547502494340410932990812816772402) * 10^40
        + 3789727318413718204474521944869046158997) * 10^40
        + 3172955211555986416587003269406843298832) * 10^40
        + 1723187513104183813675764656764316600600) * 10^40
        + 2378749225732655822619269497056953244816) * 10^40
        + 534836677685759344992146158938096869461) : ℚ) /
        ((((((((4945628786 * 10^40
        + 1139537521872904570469600329680403726850) * 10^40
        + 9253968272778849958208195321948463903179) * 10^40
        + 1460180865648215332270710899812058505622) * 10^40
        + 9175620962112591707793941202369568607795) * 10^40
        + 6254576400322690409115458764576239840095) * 10^40
        + 5352747422274896994008223087792817834108) * 10^40
        + 3955360204018565761934542840792139542375) * 10^40
        + 4071073975612981878252657449530510278656)))

theorem endpointLeftP015BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP015Center2544‖ ≤ endpointLeftP015Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP015Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP015Input2544]
  have hc : (compactExp2542 endpointLeftP015Input2544 6).1 = endpointLeftP015Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP015Input2544 6).2 : ℝ) = endpointLeftP015Error2544 := by
    have hq : (compactExp2542 endpointLeftP015Input2544 6).2 =
        ((58432555568759 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP015Error2544]
  have h := compactExp_error2542 endpointLeftP015Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP015Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP015Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP015DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP015Factor2544 * embedPair2542 endpointLeftP015Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP015Factor2544 : ℝ) * endpointLeftP015Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP015Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP015Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP015BaseError2544
    (embedPair_magnitude2542 endpointLeftP015Factor2544)

def endpointLeftP016Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-199810861117846303095609) : ℚ) /
        720575940379279360000000))

def endpointLeftP016Center2544 : RatPair2542 :=
  (((38505862022080969 : ℚ) /
        1267650600228229401496703205376),
    ((76179115590422351 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointLeftP016Error2544 : ℝ := ((13635020005641 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

def endpointLeftP016Factor2544 : RatPair2542 :=
  ((((((((((((((467541510898246790463991 * 10^40
        + 5340360912594070741700375262994851720563) * 10^40
        + 1006609977733090639146611092445070754507) * 10^40
        + 4567170454463423044567828337549216228271) * 10^40
        + 6302887027643986329176634644823363930126) * 10^40
        + 6765137494398896538271334418237029041329) * 10^40
        + 8362923456986040857325776914225815323517) * 10^40
        + 493508726007143547179742044443791673992) * 10^40
        + 4357406874831221929587669318775620321136) * 10^40
        + 6866840834999200164880404639060912418316) * 10^40
        + 3024256153957466871073925644672471476721) * 10^40
        + 5207221390426982963942408660390007941063) : ℚ) /
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
    ((((((((((16822218236551 * 10^40
        + 5354631153715928605483645546891636111222) * 10^40
        + 3347301991577150767155173914386161185104) * 10^40
        + 9719765783684063013551081836908913501463) * 10^40
        + 6394441956354114820693086214258773114172) * 10^40
        + 2551495553792729817448282856889542362112) * 10^40
        + 7996276554984444739720034786943392634246) * 10^40
        + 6260505454610213408880128281688978582877) * 10^40
        + 1868943694858895989639025529712242236281) : ℚ) /
        ((((((((206067866 * 10^40
        + 880814063411371023769566680403350155285) * 10^40
        + 4552248678032452081592008138414519329299) * 10^40
        + 1310840869402008972177946287492169104400) * 10^40
        + 9548984206754691321158080883432065358658) * 10^40
        + 1510607350013445433713144115190676660003) * 10^40
        + 9806364475928120708083675961991367409754) * 10^40
        + 5164806675167440240080605951699672480932) * 10^40
        + 3086294748983874244927194060397104594944)))

theorem endpointLeftP016BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP016Center2544‖ ≤ endpointLeftP016Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP016Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP016Input2544]
  have hc : (compactExp2542 endpointLeftP016Input2544 6).1 = endpointLeftP016Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP016Input2544 6).2 : ℝ) = endpointLeftP016Error2544 := by
    have hq : (compactExp2542 endpointLeftP016Input2544 6).2 =
        ((13635020005641 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [endpointLeftP016Error2544]
  have h := compactExp_error2542 endpointLeftP016Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP016Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP016Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP016DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP016Factor2544 * embedPair2542 endpointLeftP016Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP016Factor2544 : ℝ) * endpointLeftP016Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP016Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP016Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP016BaseError2544
    (embedPair_magnitude2542 endpointLeftP016Factor2544)

def endpointLeftP017Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-442769373018475956606027) : ℚ) /
        1441151880758558720000000))

def endpointLeftP017Center2544 : RatPair2542 :=
  (((58646391637649003 : ℚ) /
        1267650600228229401496703205376),
    (((-15505160048524895) : ℚ) /
        316912650057057350374175801344))

noncomputable def endpointLeftP017Error2544 : ℝ := ((49294139097261 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP017Factor2544 : RatPair2542 :=
  ((((((((((((((2294719021230775687572672 * 10^40
        + 248987993218987761391903463550347745718) * 10^40
        + 8149290934785910940638973695548045427564) * 10^40
        + 8045751852063971261954384275942774642614) * 10^40
        + 6921684937892597981340319298317314868588) * 10^40
        + 4073078044081110366304126293354939167367) * 10^40
        + 4154096309467067839315334904299043039903) * 10^40
        + 9612057948721996122677784540990065841182) * 10^40
        + 8865149957930006849128273884443151422196) * 10^40
        + 8905840238928410343146411766239873320621) * 10^40
        + 2908079439528094754443329870207803578110) * 10^40
        + 324047461670292068096903911073197740607) : ℚ) /
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
    ((((((((((182920948249446 * 10^40
        + 1541680949211478988985789878285540535158) * 10^40
        + 9357502297099832457064732344458807513068) * 10^40
        + 6785689894266432424259464948096743948526) * 10^40
        + 5847963502876600975907267632331404106933) * 10^40
        + 8626692228320047330957374855245214023170) * 10^40
        + 6331567411144562644117610744206985271778) * 10^40
        + 9212804402762949866832028194069034536292) * 10^40
        + 6822152834599175922776685154218208979107) : ℚ) /
        ((((((((1648542928 * 10^40
        + 7046512507290968190156533443226801242283) * 10^40
        + 6417989424259616652736065107316154634393) * 10^40
        + 486726955216071777423570299937352835207) * 10^40
        + 6391873654037530569264647067456522869265) * 10^40
        + 2084858800107563469705152921525413280031) * 10^40
        + 8450915807424965664669407695930939278036) * 10^40
        + 1318453401339521920644847613597379847458) * 10^40
        + 4690357991870993959417552483176836759552)))

theorem endpointLeftP017BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP017Center2544‖ ≤ endpointLeftP017Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP017Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP017Input2544]
  have hc : (compactExp2542 endpointLeftP017Input2544 6).1 = endpointLeftP017Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP017Input2544 6).2 : ℝ) = endpointLeftP017Error2544 := by
    have hq : (compactExp2542 endpointLeftP017Input2544 6).2 =
        ((49294139097261 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP017Error2544]
  have h := compactExp_error2542 endpointLeftP017Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP017Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP017Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP017DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP017Factor2544 * embedPair2542 endpointLeftP017Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP017Factor2544 : ℝ) * endpointLeftP017Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP017Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP017Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP017BaseError2544
    (embedPair_magnitude2542 endpointLeftP017Factor2544)

def endpointLeftP018Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-114770645411675231749613) : ℚ) /
        360287970189639680000000))

def endpointLeftP018Center2544 : RatPair2542 :=
  (((1407728604688007 : ℚ) /
        633825300114114700748351602688),
    (((-21327846033567009) : ℚ) /
        316912650057057350374175801344))

noncomputable def endpointLeftP018Error2544 : ℝ := ((14145583295521 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

def endpointLeftP018Factor2544 : RatPair2542 :=
  ((((((((((((((154160219414244564616922 * 10^40
        + 7701246358813627747989302982846132168280) * 10^40
        + 9430775620789613499270380277035159158853) * 10^40
        + 6914414841986971777887828357716515836335) * 10^40
        + 4929620380275440571895858938741127470480) * 10^40
        + 3135725209515789741361104176197275765434) * 10^40
        + 4408057726033925684219282462830033804300) * 10^40
        + 3597574325283380551550368107237042855405) * 10^40
        + 9912974922643267345055040776711897185554) * 10^40
        + 4451504168033997214582090770573275043238) * 10^40
        + 7359843331356965733713139545449019620425) * 10^40
        + 6353424151699699170519444070222871496527) : ℚ) /
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
    ((((((((((9555509633023 * 10^40
        + 4291774942249987413689363499543901155831) * 10^40
        + 3903866000232346460934063023434542221354) * 10^40
        + 2738363268240285892602634856418578664128) * 10^40
        + 4026107590558466352116184862124023264444) * 10^40
        + 7354966266598206269489613303138889478640) * 10^40
        + 7723033546741677844019330005330609079929) * 10^40
        + 6008465629508839593153900094813198791611) * 10^40
        + 6980556508858873073143258909967023764239) : ℚ) /
        ((((((((77275449 * 10^40
        + 7830305273779264133913587505151256308232) * 10^40
        + 457093254262169530597003051905444748487) * 10^40
        + 1741565326025753364566729857809563414150) * 10^40
        + 3580869077533009245434280331287024509496) * 10^40
        + 8066477756255042037642429043196503747501) * 10^40
        + 4927386678473045265531378485746762778657) * 10^40
        + 9436802503187790090030227231887377180349) * 10^40
        + 6157360530868952841847697772648914223104)))

theorem endpointLeftP018BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP018Center2544‖ ≤ endpointLeftP018Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP018Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP018Input2544]
  have hc : (compactExp2542 endpointLeftP018Input2544 6).1 = endpointLeftP018Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP018Input2544 6).2 : ℝ) = endpointLeftP018Error2544 := by
    have hq : (compactExp2542 endpointLeftP018Input2544 6).2 =
        ((14145583295521 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [endpointLeftP018Error2544]
  have h := compactExp_error2542 endpointLeftP018Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP018Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP018Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP018DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP018Factor2544 * embedPair2542 endpointLeftP018Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP018Factor2544 : ℝ) * endpointLeftP018Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP018Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP018Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP018BaseError2544
    (embedPair_magnitude2542 endpointLeftP018Factor2544)

def endpointLeftP019Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-24428249467783476683391) : ℚ) /
        72057594037927936000000))

def endpointLeftP019Center2544 : RatPair2542 :=
  ((((-81682839262770589) : ℚ) /
        1267650600228229401496703205376),
    (((-24776457215971191) : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointLeftP019Error2544 : ℝ := ((22968093507731 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def endpointLeftP019Factor2544 : RatPair2542 :=
  ((((((((((((((174556491064991734697889 * 10^40
        + 4965796800621686960853910494709052126085) * 10^40
        + 2349994497494629948455779399588820209329) * 10^40
        + 682071133193229451530290945437200978103) * 10^40
        + 543608090444613421055999986643080879660) * 10^40
        + 1457225633666729377418870520213714514949) * 10^40
        + 7632378535043382670614669074458172604539) * 10^40
        + 9173824343635529890284004998539155779726) * 10^40
        + 1070618342218359999658276024114573506667) * 10^40
        + 5860345324001364507751651244331315109105) * 10^40
        + 6088810355983896774836086082765819451952) * 10^40
        + 7752621855426076142463219666363969631263) : ℚ) /
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
    ((((((((((1279276966464 * 10^40
        + 275953578779055206214206266592424477008) * 10^40
        + 5558980411684658034469767578247139497805) * 10^40
        + 3356163068501033342710063126483549310475) * 10^40
        + 2076056331211716793880224845249088919228) * 10^40
        + 1422345067676855432515341839867273329656) * 10^40
        + 9895154901511569138389587140358295215826) * 10^40
        + 3180640382831955633228745322017526089285) * 10^40
        + 2121369408080842949944056783974335840145) : ℚ) /
        ((((((((8586161 * 10^40
        + 870033919308807125990398611683472923136) * 10^40
        + 8939677028251352170066333672433938305387) * 10^40
        + 4637951702891750373840747761978840379350) * 10^40
        + 397874341948112138381586703476336056610) * 10^40
        + 7562941972917226893071381004799611527500) * 10^40
        + 1658598519830338362836819831749640308739) * 10^40
        + 7715200278131976676670025247987486353372) * 10^40
        + 1795262281207661426871966419183212691456)))

theorem endpointLeftP019BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP019Center2544‖ ≤ endpointLeftP019Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP019Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP019Input2544]
  have hc : (compactExp2542 endpointLeftP019Input2544 6).1 = endpointLeftP019Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP019Input2544 6).2 : ℝ) = endpointLeftP019Error2544 := by
    have hq : (compactExp2542 endpointLeftP019Input2544 6).2 =
        ((22968093507731 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [endpointLeftP019Error2544]
  have h := compactExp_error2542 endpointLeftP019Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP019Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP019Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP019DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP019Factor2544 * embedPair2542 endpointLeftP019Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP019Factor2544 : ℝ) * endpointLeftP019Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP019Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP019Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP019BaseError2544
    (embedPair_magnitude2542 endpointLeftP019Factor2544)

def endpointLeftP020Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-520624750538575899551419) : ℚ) /
        1441151880758558720000000))

def endpointLeftP020Center2544 : RatPair2542 :=
  ((((-9119453561957117) : ℚ) /
        316912650057057350374175801344),
    ((77170772510733555 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointLeftP020Error2544 : ℝ := ((23476549907841 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def endpointLeftP020Factor2544 : RatPair2542 :=
  ((((((((((((((3170818811912815590435953 * 10^40
        + 3972287311309778908471078427348432540963) * 10^40
        + 4231349948933887518855795383232311633705) * 10^40
        + 9207080828825591125731834543681117939639) * 10^40
        + 5673725615257306199884388165930339636439) * 10^40
        + 6962271198627649931487989990685025287672) * 10^40
        + 4980657645427084132677809070212712617447) * 10^40
        + 3438162990954642187309525553124454065365) * 10^40
        + 9475668892042992801153272806395512785092) * 10^40
        + 9609477531551082425174491717829923701878) * 10^40
        + 9107270765018182694105443783674207973720) * 10^40
        + 6219721012965568437509558321495351139999) : ℚ) /
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
    ((((((((((891388766522094 * 10^40
        + 4648047140539354856590115236199367409850) * 10^40
        + 6008420873358550942392372886660926565325) * 10^40
        + 5487357712265916275567178723176477369448) * 10^40
        + 8705644026478863015736370078662395822215) * 10^40
        + 5456144450431933966746756158900591835147) * 10^40
        + 9367413394554819973178795374709330474197) * 10^40
        + 4341921756181768726426183637826559367743) * 10^40
        + 6484098224088396190781858033295078646361) : ℚ) /
        ((((((((4945628786 * 10^40
        + 1139537521872904570469600329680403726850) * 10^40
        + 9253968272778849958208195321948463903179) * 10^40
        + 1460180865648215332270710899812058505622) * 10^40
        + 9175620962112591707793941202369568607795) * 10^40
        + 6254576400322690409115458764576239840095) * 10^40
        + 5352747422274896994008223087792817834108) * 10^40
        + 3955360204018565761934542840792139542375) * 10^40
        + 4071073975612981878252657449530510278656)))

theorem endpointLeftP020BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP020Center2544‖ ≤ endpointLeftP020Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP020Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP020Input2544]
  have hc : (compactExp2542 endpointLeftP020Input2544 6).1 = endpointLeftP020Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP020Input2544 6).2 : ℝ) = endpointLeftP020Error2544 := by
    have hq : (compactExp2542 endpointLeftP020Input2544 6).2 =
        ((23476549907841 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [endpointLeftP020Error2544]
  have h := compactExp_error2542 endpointLeftP020Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP020Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP020Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP020DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP020Factor2544 * embedPair2542 endpointLeftP020Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP020Factor2544 : ℝ) * endpointLeftP020Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP020Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP020Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP020BaseError2544
    (embedPair_magnitude2542 endpointLeftP020Factor2544)

def endpointLeftP021Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-547379874475946380671387) : ℚ) /
        1441151880758558720000000))

def endpointLeftP021Center2544 : RatPair2542 :=
  (((28985407457410333 : ℚ) /
        633825300114114700748351602688),
    ((31326281619089717 : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointLeftP021Error2544 : ℝ := ((4254407061753 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

def endpointLeftP021Factor2544 : RatPair2542 :=
  ((((((((((((((3504584024371841124746995 * 10^40
        + 8072101872274550657384229979145036211823) * 10^40
        + 8003804427910726341293225759944331445776) * 10^40
        + 5257859455259164691700963872250311432444) * 10^40
        + 4465680209305789276853786399449610228629) * 10^40
        + 5264698610110977635822533837313307387669) * 10^40
        + 5494154808381969719539770268313362465480) * 10^40
        + 449435891377093931630605881378195077833) * 10^40
        + 2614038259405104113973423009004400160837) * 10^40
        + 7845463543377209939050418834443182628956) * 10^40
        + 3235587436290119717465421210232366845158) * 10^40
        + 7799319834547337006897563682369567722847) : ℚ) /
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
    ((((((((((345261656484807 * 10^40
        + 5724711242565608701628138511767694188214) * 10^40
        + 8988456049415578751535570650499224282237) * 10^40
        + 5271259578103739859330948261873609441914) * 10^40
        + 7076365170527048284709992288921584937547) * 10^40
        + 6443303892751965746244121998286565984601) * 10^40
        + 2006800189542699647111694241606454519492) * 10^40
        + 43105064826339764027247155003856434763) * 10^40
        + 124287148120981752991637110865286787347) : ℚ) /
        ((((((((1648542928 * 10^40
        + 7046512507290968190156533443226801242283) * 10^40
        + 6417989424259616652736065107316154634393) * 10^40
        + 486726955216071777423570299937352835207) * 10^40
        + 6391873654037530569264647067456522869265) * 10^40
        + 2084858800107563469705152921525413280031) * 10^40
        + 8450915807424965664669407695930939278036) * 10^40
        + 1318453401339521920644847613597379847458) * 10^40
        + 4690357991870993959417552483176836759552)))

theorem endpointLeftP021BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP021Center2544‖ ≤ endpointLeftP021Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP021Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP021Input2544]
  have hc : (compactExp2542 endpointLeftP021Input2544 6).1 = endpointLeftP021Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP021Input2544 6).2 : ℝ) = endpointLeftP021Error2544 := by
    have hq : (compactExp2542 endpointLeftP021Input2544 6).2 =
        ((4254407061753 : ℚ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472)) := by cbv
    rw [hq]
    norm_num [endpointLeftP021Error2544]
  have h := compactExp_error2542 endpointLeftP021Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP021Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP021Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP021DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP021Factor2544 * embedPair2542 endpointLeftP021Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP021Factor2544 : ℝ) * endpointLeftP021Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP021Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP021Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP021BaseError2544
    (embedPair_magnitude2542 endpointLeftP021Factor2544)

def endpointLeftP022Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-112214826711468142236233) : ℚ) /
        288230376151711744000000))

def endpointLeftP022Center2544 : RatPair2542 :=
  (((10421690030224543 : ℚ) /
        158456325028528675187087900672),
    ((18297955751756599 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointLeftP022Error2544 : ℝ := ((2960087737759 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

def endpointLeftP022Factor2544 : RatPair2542 :=
  ((((((((((((((3681887474604700127725605 * 10^40
        + 4786286509197514610507816078652330392869) * 10^40
        + 4561205435458749926782057688472839798043) * 10^40
        + 268356162259917742342374808873493329590) * 10^40
        + 6961452016588586317659405940955524336605) * 10^40
        + 8359337854110494758938635359327987455548) * 10^40
        + 4249535410501029240657833317268957538587) * 10^40
        + 1816291417219091108014969822712822744830) * 10^40
        + 1631980973880513647200251009047411862563) * 10^40
        + 3027656564757338960662438117725309465354) * 10^40
        + 7520186274988220129365696189387636639346) * 10^40
        + 9240575197829535479722614406155626184783) : ℚ) /
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
    ((((((((((1115380077844393 * 10^40
        + 3035779933223142638496063052533445071952) * 10^40
        + 9027083408403078048981536983653236109552) * 10^40
        + 8910938005583519837359640500446553719793) * 10^40
        + 3824087733393232185533754012246668861054) * 10^40
        + 8435728615879280855024612629314086575073) * 10^40
        + 5904332036487406599318416594861294778425) * 10^40
        + 1562968760710734738957148918199362443412) * 10^40
        + 9427668826138491163944146639167458076815) : ℚ) /
        ((((((((4945628786 * 10^40
        + 1139537521872904570469600329680403726850) * 10^40
        + 9253968272778849958208195321948463903179) * 10^40
        + 1460180865648215332270710899812058505622) * 10^40
        + 9175620962112591707793941202369568607795) * 10^40
        + 6254576400322690409115458764576239840095) * 10^40
        + 5352747422274896994008223087792817834108) * 10^40
        + 3955360204018565761934542840792139542375) * 10^40
        + 4071073975612981878252657449530510278656)))

theorem endpointLeftP022BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP022Center2544‖ ≤ endpointLeftP022Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP022Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP022Input2544]
  have hc : (compactExp2542 endpointLeftP022Input2544 6).1 = endpointLeftP022Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP022Input2544 6).2 : ℝ) = endpointLeftP022Error2544 := by
    have hq : (compactExp2542 endpointLeftP022Input2544 6).2 =
        ((2960087737759 : ℚ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472)) := by cbv
    rw [hq]
    norm_num [endpointLeftP022Error2544]
  have h := compactExp_error2542 endpointLeftP022Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP022Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP022Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP022DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP022Factor2544 * embedPair2542 endpointLeftP022Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP022Factor2544 : ℝ) * endpointLeftP022Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP022Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP022Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP022BaseError2544
    (embedPair_magnitude2542 endpointLeftP022Factor2544)

def endpointLeftP023Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-300278613592663314364333) : ℚ) /
        720575940379279360000000))

def endpointLeftP023Center2544 : RatPair2542 :=
  (((2853757647107117 : ℚ) /
        1267650600228229401496703205376),
    (((-42655055765682821) : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointLeftP023Error2544 : ℝ := ((22277317902181 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def endpointLeftP023Factor2544 : RatPair2542 :=
  ((((((((((((((1054402673694460456871440 * 10^40
        + 7759254154977359393920217118417164336605) * 10^40
        + 3060233150845194788769903324578378626027) * 10^40
        + 9822583039582002339525001987222561836938) * 10^40
        + 4312056016626463418356130847231561947511) * 10^40
        + 3962421275582462607453496776556805378719) * 10^40
        + 2135331576039916528713394427886227748679) * 10^40
        + 3116856626501889467936041904496230404276) * 10^40
        + 7570114075944780776605913945244486103710) * 10^40
        + 7264959574351878572602007539191709786715) * 10^40
        + 3640411976555276609840153313647324737143) * 10^40
        + 6929193812484905447609510681932540341711) : ℚ) /
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
    ((((((((((170935571527504 * 10^40
        + 720028910528992993171165074637810556620) * 10^40
        + 6933849014149309392448070340088151137860) * 10^40
        + 1983902992295400060365745765641814316586) * 10^40
        + 8224372769347371450715105059926914107517) * 10^40
        + 6456302687420077770371408636627582589095) * 10^40
        + 3496274294604377948251774735232082775326) * 10^40
        + 8364196028956692780635767535531854908022) * 10^40
        + 2993564826223774896393669978236957336783) : ℚ) /
        ((((((((618203598 * 10^40
        + 2642442190234113071308700041210050465856) * 10^40
        + 3656746034097356244776024415243557987897) * 10^40
        + 3932522608206026916533838862476507313202) * 10^40
        + 8646952620264073963474242650296196075974) * 10^40
        + 4531822050040336301139432345572029980011) * 10^40
        + 9419093427784362124251027885974102229263) * 10^40
        + 5494420025502320720241817855099017442796) * 10^40
        + 9258884246951622734781582181191313784832)))

theorem endpointLeftP023BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP023Center2544‖ ≤ endpointLeftP023Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP023Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP023Input2544]
  have hc : (compactExp2542 endpointLeftP023Input2544 6).1 = endpointLeftP023Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP023Input2544 6).2 : ℝ) = endpointLeftP023Error2544 := by
    have hq : (compactExp2542 endpointLeftP023Input2544 6).2 =
        ((22277317902181 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [endpointLeftP023Error2544]
  have h := compactExp_error2542 endpointLeftP023Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP023Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP023Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP023DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP023Factor2544 * embedPair2542 endpointLeftP023Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP023Factor2544 : ℝ) * endpointLeftP023Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP023Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP023Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP023BaseError2544
    (embedPair_magnitude2542 endpointLeftP023Factor2544)

def endpointLeftP024Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-309351029057948556428147) : ℚ) /
        720575940379279360000000))

def endpointLeftP024Center2544 : RatPair2542 :=
  ((((-59564634275976993) : ℚ) /
        1267650600228229401496703205376),
    (((-61139295103653053) : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointLeftP024Error2544 : ℝ := ((48533417885251 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP024Factor2544 : RatPair2542 :=
  ((((((((((((((1119005270417352220670051 * 10^40
        + 7925143579339935080403540416858182553630) * 10^40
        + 7354932926081353918072167122883336162113) * 10^40
        + 1987000254296030483587075254092893106393) * 10^40
        + 4533088181552029363837314044589492389578) * 10^40
        + 599827430046044301098054139971304136537) * 10^40
        + 82552714806746685928445421872759604790) * 10^40
        + 458064015065854367929471193807196372518) * 10^40
        + 7043960231346924014468203859911665414705) * 10^40
        + 8299706358074332909386266993056141218073) * 10^40
        + 123081456067632755734216687222903633406) * 10^40
        + 2444186118423986414917349195410746998031) : ℚ) /
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
    ((((((((((186884426562573 * 10^40
        + 4439785886169222378235427436455456500809) * 10^40
        + 2629642928109425479762825750976761157876) * 10^40
        + 1489379459192563536547255687513659885912) * 10^40
        + 6489360443035378336972711793031499290945) * 10^40
        + 627173082552665812740874694049980662830) * 10^40
        + 2741748844249178455725824738594676241348) * 10^40
        + 8841840579075163404291089651892908971575) * 10^40
        + 8000111670610769043925943264174864923217) : ℚ) /
        ((((((((618203598 * 10^40
        + 2642442190234113071308700041210050465856) * 10^40
        + 3656746034097356244776024415243557987897) * 10^40
        + 3932522608206026916533838862476507313202) * 10^40
        + 8646952620264073963474242650296196075974) * 10^40
        + 4531822050040336301139432345572029980011) * 10^40
        + 9419093427784362124251027885974102229263) * 10^40
        + 5494420025502320720241817855099017442796) * 10^40
        + 9258884246951622734781582181191313784832)))

theorem endpointLeftP024BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP024Center2544‖ ≤ endpointLeftP024Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP024Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP024Input2544]
  have hc : (compactExp2542 endpointLeftP024Input2544 6).1 = endpointLeftP024Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP024Input2544 6).2 : ℝ) = endpointLeftP024Error2544 := by
    have hq : (compactExp2542 endpointLeftP024Input2544 6).2 =
        ((48533417885251 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP024Error2544]
  have h := compactExp_error2542 endpointLeftP024Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP024Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP024Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP024DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP024Factor2544 * embedPair2542 endpointLeftP024Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP024Factor2544 : ℝ) * endpointLeftP024Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP024Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP024Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP024BaseError2544
    (embedPair_magnitude2542 endpointLeftP024Factor2544)

def endpointLeftP025Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-10022692915539018190833) : ℚ) /
        22517998136852480000000))

def endpointLeftP025Center2544 : RatPair2542 :=
  ((((-83449127615358963) : ℚ) /
        1267650600228229401496703205376),
    ((17949990597156351 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointLeftP025Error2544 : ℝ := ((46218232174417 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP025Factor2544 : RatPair2542 :=
  ((((((((((((((1174533088859929269158 * 10^40
        + 4373113159625165754490345234744013349960) * 10^40
        + 8812591092381069718906642808856083770536) * 10^40
        + 5256083985998186808191218311900523506809) * 10^40
        + 162513487462822093646941153136291067100) * 10^40
        + 2333219483200958671181149681726750653270) * 10^40
        + 4611882045013990504597724340692058933488) * 10^40
        + 3761342966887876004199807281561330184611) * 10^40
        + 5569192102552182800974470047544465165195) * 10^40
        + 1857102205693891573333315181873798760136) * 10^40
        + 9355595247855504480061459262613578972206) * 10^40
        + 5332323740441867854045480949930619562007) : ℚ) /
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
    ((((((((((2118380924 * 10^40
        + 7579608051296298990003899038858269150541) * 10^40
        + 3662752328916798838593157784022777394607) * 10^40
        + 6663571032585919805923250406322459812131) * 10^40
        + 9103270211688677040266326279353909047049) * 10^40
        + 1910142776427129163531750150105369683717) * 10^40
        + 9345014677310154787883435269010921432022) * 10^40
        + 1402271094764223360933635592168941395931) * 10^40
        + 7544522760457355859669680081519608431713) : ℚ) /
        ((((((((6288 * 10^40
        + 6922023950624493755219231248983166606144) * 10^40
        + 8756547615010926283327685302982739700907) * 10^40
        + 2662088343532391418730840391427230595980) * 10^40
        + 9692674224371544027445103701198835207072) * 10^40
        + 7129562701640320234540823765384374715474) * 10^40
        + 2432855418837766361105593373900207256085) * 10^40
        + 5027623437703709943854982928648428334731) * 10^40
        + 4737643014366118892646634741029675204608)))

theorem endpointLeftP025BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP025Center2544‖ ≤ endpointLeftP025Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP025Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP025Input2544]
  have hc : (compactExp2542 endpointLeftP025Input2544 6).1 = endpointLeftP025Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP025Input2544 6).2 : ℝ) = endpointLeftP025Error2544 := by
    have hq : (compactExp2542 endpointLeftP025Input2544 6).2 =
        ((46218232174417 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP025Error2544]
  have h := compactExp_error2542 endpointLeftP025Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP025Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP025Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP025DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP025Factor2544 * embedPair2542 endpointLeftP025Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP025Factor2544 : ℝ) * endpointLeftP025Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP025Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP025Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP025BaseError2544
    (embedPair_magnitude2542 endpointLeftP025Factor2544)

def endpointLeftP026Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-20771944281655350607437) : ℚ) /
        45035996273704960000000))

def endpointLeftP026Center2544 : RatPair2542 :=
  ((((-27370500051621241) : ℚ) /
        1267650600228229401496703205376),
    ((40425285370441941 : ℚ) /
        633825300114114700748351602688))

noncomputable def endpointLeftP026Error2544 : ℝ := ((59912077754477 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP026Factor2544 : RatPair2542 :=
  ((((((((((((((5044530949742122665371 * 10^40
        + 1535780483968891972056752145470690605579) * 10^40
        + 6639137467520106127041942304381199308709) * 10^40
        + 9545660879932851272792472071044997525490) * 10^40
        + 2946184688308698178009355411895920392886) * 10^40
        + 8880109207071374050782587647840588690432) * 10^40
        + 4414288710823609240042084690697164371623) * 10^40
        + 4473290292290508654863856331076444972787) * 10^40
        + 231704250803245112567823941432462515314) * 10^40
        + 872485363061060215709764118582906599141) * 10^40
        + 5909994420699370354522163784098548070801) * 10^40
        + 3722058406746961622263573237565630649231) : ℚ) /
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
    ((((((((((18855569955 * 10^40
        + 5946064055804588065715381022238331459581) * 10^40
        + 6735460381199714522899829682388417040205) * 10^40
        + 8769159274229903390432217854085955068289) * 10^40
        + 7447025365176510783200184020197442254580) * 10^40
        + 3183600659635007542980974180304877580843) * 10^40
        + 7460862876907733555945901919844893136471) * 10^40
        + 328159549350332844261211439888092143165) * 10^40
        + 4688738251544873143160025689063278345509) : ℚ) /
        ((((((((50309 * 10^40
        + 5376191604995950041753849991865332849159) * 10^40
        + 52380920087410266621482423861917607258) * 10^40
        + 1296706748259131349846723131417844767847) * 10^40
        + 7541393794972352219560829609590681656581) * 10^40
        + 7036501613122561876326590123074997723793) * 10^40
        + 9462843350702130888844746991201658048684) * 10^40
        + 220987501629679550839863429187426677851) * 10^40
        + 7901144114928951141173077928237401636864)))

theorem endpointLeftP026BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP026Center2544‖ ≤ endpointLeftP026Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP026Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP026Input2544]
  have hc : (compactExp2542 endpointLeftP026Input2544 6).1 = endpointLeftP026Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP026Input2544 6).2 : ℝ) = endpointLeftP026Error2544 := by
    have hq : (compactExp2542 endpointLeftP026Input2544 6).2 =
        ((59912077754477 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP026Error2544]
  have h := compactExp_error2542 endpointLeftP026Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP026Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP026Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP026DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP026Factor2544 * embedPair2542 endpointLeftP026Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP026Factor2544 : ℝ) * endpointLeftP026Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP026Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP026Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP026BaseError2544
    (embedPair_magnitude2542 endpointLeftP026Factor2544)

def endpointLeftP027Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-43640783619197408678627) : ℚ) /
        90071992547409920000000))

def endpointLeftP027Center2544 : RatPair2542 :=
  (((78375538908662461 : ℚ) /
        1267650600228229401496703205376),
    ((33811742974582127 : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointLeftP027Error2544 : ℝ := ((22523431186811 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def endpointLeftP027Factor2544 : RatPair2542 :=
  ((((((((((((((22264531230104109363643 * 10^40
        + 8294934862971369772678764196128224436652) * 10^40
        + 8439968748481733647798621890649673810994) * 10^40
        + 7878870726525256962866464057420407546974) * 10^40
        + 955047775223326658010058896708392948022) * 10^40
        + 3794125232878635826764300042484506837475) * 10^40
        + 9302697876588639892774463788390075882951) * 10^40
        + 3033715169185692645783684393907078465922) * 10^40
        + 3868226704479657865809230593516363838379) * 10^40
        + 1480029334335446667334195901245887729427) * 10^40
        + 4492596073953674742047884977944326286608) * 10^40
        + 3738934373296325051189295727893508141167) : ℚ) /
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
    ((((((((((524509060213 * 10^40
        + 4730063243062003179202879809214724707321) * 10^40
        + 1361595891793192807779060346726195342426) * 10^40
        + 5174393961723036589488540939090382131610) * 10^40
        + 8699288214020886663219049019039042331618) * 10^40
        + 2072732842391633816085856631780099708592) * 10^40
        + 608181601771457359137303703626289401722) * 10^40
        + 7053448685314846504185776399798219945287) * 10^40
        + 9628207096281602140144652872301560224961) : ℚ) /
        ((((((((1207428 * 10^40
        + 9028598519902801002092399804767988379816) * 10^40
        + 1257142082097846398915578172686022574195) * 10^40
        + 1120961958219152396321355154028274428346) * 10^40
        + 993451079336453269459910630176359757960) * 10^40
        + 8876038714941485031838162953799945371054) * 10^40
        + 7108240416851141332273927788839793168416) * 10^40
        + 5303700039112309220156722300498240268442) * 10^40
        + 9627458758294827388153870277697639284736)))

theorem endpointLeftP027BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP027Center2544‖ ≤ endpointLeftP027Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP027Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP027Input2544]
  have hc : (compactExp2542 endpointLeftP027Input2544 6).1 = endpointLeftP027Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP027Input2544 6).2 : ℝ) = endpointLeftP027Error2544 := by
    have hq : (compactExp2542 endpointLeftP027Input2544 6).2 =
        ((22523431186811 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [endpointLeftP027Error2544]
  have h := compactExp_error2542 endpointLeftP027Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP027Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP027Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP027DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP027Factor2544 * embedPair2542 endpointLeftP027Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP027Factor2544 : ℝ) * endpointLeftP027Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP027Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP027Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP027BaseError2544
    (embedPair_magnitude2542 endpointLeftP027Factor2544)

def endpointLeftP028Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-177883892884016178388727) : ℚ) /
        360287970189639680000000))

def endpointLeftP028Center2544 : RatPair2542 :=
  (((83938739517315555 : ℚ) /
        1267650600228229401496703205376),
    (((-15499905497993049) : ℚ) /
        1267650600228229401496703205376))

noncomputable def endpointLeftP028Error2544 : ℝ := ((40351813399135 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP028Factor2544 : RatPair2542 :=
  ((((((((((((((369903242132579014792307 * 10^40
        + 9784722258968132735525832954168675676619) * 10^40
        + 1854250499159187422081185986773600972078) * 10^40
        + 8397250446783518021064926735291591516783) * 10^40
        + 2170358750198082156950433451485475550475) * 10^40
        + 1389671004922196187676589972973102847893) * 10^40
        + 3010234271446616846786024875484717792073) * 10^40
        + 7565795771205860679078970269303069795052) * 10^40
        + 8819128402490547536456042348250624441409) * 10^40
        + 5906226127824500075786202441694014871378) * 10^40
        + 1770330176486360945569788416443963545268) * 10^40
        + 1739065084658027423330412487318463458087) : ℚ) /
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
    ((((((((((3229038540054 * 10^40
        + 8559065085899658847785297526672376479011) * 10^40
        + 6959857405656709330024011871165264138672) * 10^40
        + 6299036869487367993868003988804631083822) * 10^40
        + 4005525538637541819561836537771365312998) * 10^40
        + 5167553331546019460608965548088176969375) * 10^40
        + 8945508664021224361695775604352625010568) * 10^40
        + 5966755158457503112279900135502151050597) * 10^40
        + 170531849019118249140737691374476130031) : ℚ) /
        ((((((((7025040 * 10^40
        + 8893664115798114921264871591377386937112) * 10^40
        + 41553932205651775508818459264131340771) * 10^40
        + 5612869575093250305869702714346323946740) * 10^40
        + 9416442643412091749584934575571547682681) * 10^40
        + 5278770705114094730694766276654227613409) * 10^40
        + 2266126061679367751411943498704251161696) * 10^40
        + 1766982045744344553639111566535216107304) * 10^40
        + 5105214593715359349258881615695355838464)))

theorem endpointLeftP028BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP028Center2544‖ ≤ endpointLeftP028Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP028Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP028Input2544]
  have hc : (compactExp2542 endpointLeftP028Input2544 6).1 = endpointLeftP028Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP028Input2544 6).2 : ℝ) = endpointLeftP028Error2544 := by
    have hq : (compactExp2542 endpointLeftP028Input2544 6).2 =
        ((40351813399135 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP028Error2544]
  have h := compactExp_error2542 endpointLeftP028Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP028Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP028Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP028DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP028Factor2544 * embedPair2542 endpointLeftP028Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP028Factor2544 : ℝ) * endpointLeftP028Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP028Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP028Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP028BaseError2544
    (embedPair_magnitude2542 endpointLeftP028Factor2544)

def endpointLeftP029Input2544 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-182939534351242879487659) : ℚ) /
        360287970189639680000000))

def endpointLeftP029Center2544 : RatPair2542 :=
  (((40181662807215871 : ℚ) /
        1267650600228229401496703205376),
    (((-4706790737631139) : ℚ) /
        79228162514264337593543950336))

noncomputable def endpointLeftP029Error2544 : ℝ := ((59484785339005 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def endpointLeftP029Factor2544 : RatPair2542 :=
  ((((((((((((((391210715945477544988182 * 10^40
        + 3433035262708596368652976562687552347807) * 10^40
        + 2482320442447196094731240978580546024719) * 10^40
        + 1507400911363162854903469520617994759469) * 10^40
        + 9751752062897816855460213947456078561549) * 10^40
        + 9128840803663993080115696860691091182258) * 10^40
        + 6494314886967144852302950795687966136111) * 10^40
        + 2565938434113389196537267259212248538620) * 10^40
        + 7574464555633561814852160954998294841554) * 10^40
        + 7773321636310529157254732302430426274784) * 10^40
        + 9892302531371501426505803187692458282362) * 10^40
        + 5238790665121822408781204545882538751999) : ℚ) /
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
    ((((((((((38632365792787 * 10^40
        + 9020222678414363939807502355304344614782) * 10^40
        + 8912998781444887471267394838523599102010) * 10^40
        + 9313310740922479987487607120676374242985) * 10^40
        + 4643624593816439106194721729005756934177) * 10^40
        + 782493070498857830737243050942964376769) * 10^40
        + 6778227943946389668610514768823773997804) * 10^40
        + 5258927975939372577195111943931001572) * 10^40
        + 4648224825113481690006123162053506211401) : ℚ) /
        ((((((((77275449 * 10^40
        + 7830305273779264133913587505151256308232) * 10^40
        + 457093254262169530597003051905444748487) * 10^40
        + 1741565326025753364566729857809563414150) * 10^40
        + 3580869077533009245434280331287024509496) * 10^40
        + 8066477756255042037642429043196503747501) * 10^40
        + 4927386678473045265531378485746762778657) * 10^40
        + 9436802503187790090030227231887377180349) * 10^40
        + 6157360530868952841847697772648914223104)))

theorem endpointLeftP029BaseError2544 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP029Center2544‖ ≤ endpointLeftP029Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hz : ‖embedPair2542 endpointLeftP029Input2544‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, endpointLeftP029Input2544]
  have hc : (compactExp2542 endpointLeftP029Input2544 6).1 = endpointLeftP029Center2544 := by cbv
  have he : ((compactExp2542 endpointLeftP029Input2544 6).2 : ℝ) = endpointLeftP029Error2544 := by
    have hq : (compactExp2542 endpointLeftP029Input2544 6).2 =
        ((59484785339005 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [endpointLeftP029Error2544]
  have h := compactExp_error2542 endpointLeftP029Input2544 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      endpointLeftPosition2544 = Complex.exp ((2 : ℂ)^6 * embedPair2542 endpointLeftP029Input2544)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [endpointLeftPosition2544, storedWidth, nodeModulation2541,
        embedPair2542, endpointLeftP029Input2544, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem endpointLeftP029DerivativeError2544 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ endpointLeftPosition2544 -
      embedPair2542 endpointLeftP029Factor2544 * embedPair2542 endpointLeftP029Center2544‖ ≤
      (pairMagnitude2542 endpointLeftP029Factor2544 : ℝ) * endpointLeftP029Error2544 := by
  have hx : |endpointLeftPosition2544| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [endpointLeftPosition2544, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) endpointLeftPosition2544 = embedPair2542
          endpointLeftP029Factor2544
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        endpointLeftPosition2544, storedWidth, nodeModulation2541, embedPair2542,
            endpointLeftP029Factor2544,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ endpointLeftP029BaseError2544
    (embedPair_magnitude2542 endpointLeftP029Factor2544)

theorem endpointLeft_grid2544 :
    -stripRadius2303 + (5440 : ℝ)*(2*stripRadius2303/10240) = endpointLeftPosition2544 := by
  norm_num [stripRadius2303, endpointLeftPosition2544]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.endpointLeftP000DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP001DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP002DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP003DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP004DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP005DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP006DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP007DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP008DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP009DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP010DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP011DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP012DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP013DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP014DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP015DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP016DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP017DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP018DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP019DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP020DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP021DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP022DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP023DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP024DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP025DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP026DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP027DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP028DerivativeError2544
#print axioms ConnesWeilRH.Dev.endpointLeftP029DerivativeError2544
