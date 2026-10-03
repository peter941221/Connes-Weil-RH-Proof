import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchSeparateC000Position2547 : ℝ := (((-158531586419) : ℝ) /
        51200000000)

def batchSeparateC000Input2547 : RatPair2542 := ((((-((340 * 10^40
        + 1125558694715412604882605546165965236561) * 10^40
        + 9325600687173468560131001925406640200979)) : ℚ) /
        ((941 * 10^40
        + 6102169216506454849034257242358098754684) * 10^40
        + 4000368461807982441421667880140800000000)),
    ((875774620147323865939848151 : ℚ) /
        3689348814741910323200000000))

def batchSeparateC000Center2547 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchSeparateC000Factor2547 : RatPair2542 := ((((((((((((((2822667428909 * 10^40
        + 7446092690887481115023050610041782080926) * 10^40
        + 7003936177476489601432716757152976182870) * 10^40
        + 3020570989241737193364260779072096561631) * 10^40
        + 5126344525108745596765315361116632575315) * 10^40
        + 4749955492260416336064809435915177562135) * 10^40
        + 4559234872892498846665585368239890466759) * 10^40
        + 3017291419452122668776729364408126691220) * 10^40
        + 7657006470432776124440128693142641137814) * 10^40
        + 1782531098713702418681986012597575608956) * 10^40
        + 7776741915673178381424553161286697049007) * 10^40
        + 5593032865644153022592031209923108839493) : ℚ) /
        (((((((((((13294 * 10^40
        + 422711220652669418997196288150872758237) * 10^40
        + 328324554692358369840870378297358441784) * 10^40
        + 5130571111568733489307229608989541006898) * 10^40
        + 6218359640082882112635465897478279280245) * 10^40
        + 3083192855974417819428918948310607969287) * 10^40
        + 9239862000812224941823042183566670493098) * 10^40
        + 6656575616399304468821774186879767982150) * 10^40
        + 15502611651477979806669680036238387146) * 10^40
        + 1940504353614462503247217281208834392816) * 10^40
        + 8346161864622542934526197106185260151752) * 10^40
        + 4566178873527647187885826440531791577088)),
    (((-((((((((12387540 * 10^40
        + 8810297339010001984417860900689147138892) * 10^40
        + 5166761326761848594034252451705591657175) * 10^40
        + 7645819371508389977456993062820991881049) * 10^40
        + 1257869794717343491985632832691347743437) * 10^40
        + 3833609164825148004089821052034810096165) * 10^40
        + 8037150996057262334745039313944938189213) * 10^40
        + 4671783310074104809551853950526133558147) * 10^40
        + 9798926741123541741778267269042308548843)) : ℚ) /
        (((((((2900242863486546972840900254409935003313 * 10^40
        + 2886911659530428454328810684955747709237) * 10^40
        + 2926949848572266501641263971861853851819) * 10^40
        + 3611042156476707720180651710753596486497) * 10^40
        + 2630002623515689516863840004131964275527) * 10^40
        + 4888409820754831583540978359385522341346) * 10^40
        + 3809565805659865221845538113057591023547) * 10^40
        + 5803898216573829710726339938742458908672)))

noncomputable def batchSeparateC000Error2547 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchSeparateC000BaseError2547 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchSeparateC000Position2547 -
      embedPair2542 batchSeparateC000Center2547‖ ≤ batchSeparateC000Error2547 := by
  have hx : |batchSeparateC000Position2547| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchSeparateC000Position2547, storedWidth]
  have hz : ‖embedPair2542 batchSeparateC000Input2547‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchSeparateC000Input2547]
  have hc : (compactExp2547 batchSeparateC000Input2547 9).1 = batchSeparateC000Center2547 := by
      cbv
  have he : ((compactExp2547 batchSeparateC000Input2547 9).2 : ℝ) = batchSeparateC000Error2547 :=
      by
    have hq : (compactExp2547 batchSeparateC000Input2547 9).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [batchSeparateC000Error2547]
  have h := compactExp_error2547 batchSeparateC000Input2547 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      batchSeparateC000Position2547 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          batchSeparateC000Input2547) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchSeparateC000Position2547, storedWidth,
        nodeModulation2541,
      embedPair2542, batchSeparateC000Input2547, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchSeparateC000ThirdError2547 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchSeparateC000Position2547 -
      embedPair2542 batchSeparateC000Factor2547 * embedPair2542 batchSeparateC000Center2547‖ ≤
        (pairMagnitude2542 batchSeparateC000Factor2547 : ℝ) * batchSeparateC000Error2547 := by
  have hx : |batchSeparateC000Position2547| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchSeparateC000Position2547, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchSeparateC000Position2547 = embedPair2542
          batchSeparateC000Factor2547 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchSeparateC000Position2547, storedWidth, nodeModulation2541, embedPair2542,
      batchSeparateC000Factor2547, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchSeparateC000BaseError2547
    (embedPair_magnitude2542 batchSeparateC000Factor2547)



open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchSeparateC001Position2547 : ℝ := (((-158531586419) : ℝ) /
        51200000000)

def batchSeparateC001Input2547 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((912951341665564226630614693 : ℚ) /
        472236648286964521369600000000))

def batchSeparateC001Center2547 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchSeparateC001Factor2547 : RatPair2542 := ((((((((((((((302965006690404118429569397219452 *
    10^40
        + 7564029273269060297094803094618650646126) * 10^40
        + 6976014042493413734324646536657550366259) * 10^40
        + 8542012761723082797140732681300427869187) * 10^40
        + 9003832863128160797281142589005113084940) * 10^40
        + 5403857261296289190055981375421093964361) * 10^40
        + 1687388464958740255095830793390375388654) * 10^40
        + 7139155089816736325876310175091600730161) * 10^40
        + 5165576640165795906519767889776422449191) * 10^40
        + 3633631444022224386675356871545118625362) * 10^40
        + 7581088352030558511256347220219659639919) * 10^40
        + 6695110727042485762669615857190087253367) : ℚ) /
        (((((((((((13282448415 * 10^40
        + 3751862906737114075469030278080835751875) * 10^40
        + 2628107237486823411921077444762763908139) * 10^40
        + 5890379944666146121359885013759151515141) * 10^40
        + 9105505754700664169173964362303503055489) * 10^40
        + 5492971875787620267770212498653701654461) * 10^40
        + 9917397580919462582875861542047875023918) * 10^40
        + 8329582070970086591074054577383756385271) * 10^40
        + 9738501248109756999871127555411343358644) * 10^40
        + 8142452279729649629225556601960818840205) * 10^40
        + 7455672210938309794872243781464869251619) * 10^40
        + 6005055907615662265016388383497282125824)),
    (((-((((((((95397560234492498054 * 10^40
        + 559664516503103964465883624296579507786) * 10^40
        + 9576449776811227752067155597825690514103) * 10^40
        + 8634824245431275282617093544521628683647) * 10^40
        + 5826147713755339701220740176640148799364) * 10^40
        + 9209920101260276513417381362551295587948) * 10^40
        + 4384647982920097284998242820787631977912) * 10^40
        + 7568757345322560558519207297282781586301) * 10^40
        + 7292790321774993435831567198892251823179)) : ℚ) /
        ((((((((966 * 10^40
        + 1854664759073824730069108812637219606340) * 10^40
        + 5597687691702706787457206187151880564181) * 10^40
        + 1195422202881051970022012443698912848523) * 10^40
        + 3875083057406769970465767194818051714366) * 10^40
        + 1046594007454693856580563199902554159399) * 10^40
        + 417992587910568601181232896372719981817) * 10^40
        + 627191162563074044093713889668612473962) * 10^40
        + 4350923635082522974021415051787780489216)))

noncomputable def batchSeparateC001Error2547 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchSeparateC001BaseError2547 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchSeparateC001Position2547 -
      embedPair2542 batchSeparateC001Center2547‖ ≤ batchSeparateC001Error2547 := by
  have hx : |batchSeparateC001Position2547| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchSeparateC001Position2547, storedWidth]
  have hz : ‖embedPair2542 batchSeparateC001Input2547‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchSeparateC001Input2547]
  have hc : (compactExp2547 batchSeparateC001Input2547 16).1 = batchSeparateC001Center2547 := by
      cbv
  have he : ((compactExp2547 batchSeparateC001Input2547 16).2 : ℝ) = batchSeparateC001Error2547 :=
      by
    have hq : (compactExp2547 batchSeparateC001Input2547 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [batchSeparateC001Error2547]
  have h := compactExp_error2547 batchSeparateC001Input2547 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      batchSeparateC001Position2547 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          batchSeparateC001Input2547) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchSeparateC001Position2547, storedWidth,
        nodeModulation2541,
      embedPair2542, batchSeparateC001Input2547, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchSeparateC001ThirdError2547 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchSeparateC001Position2547 -
      embedPair2542 batchSeparateC001Factor2547 * embedPair2542 batchSeparateC001Center2547‖ ≤
        (pairMagnitude2542 batchSeparateC001Factor2547 : ℝ) * batchSeparateC001Error2547 := by
  have hx : |batchSeparateC001Position2547| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchSeparateC001Position2547, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchSeparateC001Position2547 = embedPair2542
          batchSeparateC001Factor2547 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchSeparateC001Position2547, storedWidth, nodeModulation2541, embedPair2542,
      batchSeparateC001Factor2547, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchSeparateC001BaseError2547
    (embedPair_magnitude2542 batchSeparateC001Factor2547)



open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchSeparateC002Position2547 : ℝ := ((65536001 : ℝ) /
        160000000)

def batchSeparateC002Input2547 : RatPair2542 := ((((-(418745829535285177504639993717831830075 *
    10^40
        + 5441618534605682304357047648610637783799)) : ℚ) /
        (886210261626655755083735189233369746668 * 10^40
        + 3797746372915947800471746154516480000000)),
    (((-362039942185747774262029) : ℚ) /
        1441151880758558720000000))

def batchSeparateC002Center2547 : RatPair2542 := ((((-100223478208003658749924307957107195) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((38854538679396106244911782740630351 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchSeparateC002Factor2547 : RatPair2542 := ((((((((((((((20591 * 10^40
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

noncomputable def batchSeparateC002Error2547 : ℝ := ((30249903359130704771307903799783 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchSeparateC002BaseError2547 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchSeparateC002Position2547 -
      embedPair2542 batchSeparateC002Center2547‖ ≤ batchSeparateC002Error2547 := by
  have hx : |batchSeparateC002Position2547| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchSeparateC002Position2547, storedWidth]
  have hz : ‖embedPair2542 batchSeparateC002Input2547‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchSeparateC002Input2547]
  have hc : (compactExp2547 batchSeparateC002Input2547 6).1 = batchSeparateC002Center2547 := by
      cbv
  have he : ((compactExp2547 batchSeparateC002Input2547 6).2 : ℝ) = batchSeparateC002Error2547 :=
      by
    have hq : (compactExp2547 batchSeparateC002Input2547 6).2 =
        ((30249903359130704771307903799783 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by cbv
    rw [hq]
    norm_num [batchSeparateC002Error2547]
  have h := compactExp_error2547 batchSeparateC002Input2547 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      batchSeparateC002Position2547 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          batchSeparateC002Input2547) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchSeparateC002Position2547, storedWidth,
        nodeModulation2541,
      embedPair2542, batchSeparateC002Input2547, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchSeparateC002ThirdError2547 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchSeparateC002Position2547 -
      embedPair2542 batchSeparateC002Factor2547 * embedPair2542 batchSeparateC002Center2547‖ ≤
        (pairMagnitude2542 batchSeparateC002Factor2547 : ℝ) * batchSeparateC002Error2547 := by
  have hx : |batchSeparateC002Position2547| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchSeparateC002Position2547, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchSeparateC002Position2547 = embedPair2542
          batchSeparateC002Factor2547 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchSeparateC002Position2547, storedWidth, nodeModulation2541, embedPair2542,
      batchSeparateC002Factor2547, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchSeparateC002BaseError2547
    (embedPair_magnitude2542 batchSeparateC002Factor2547)



open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchSeparateC003Position2547 : ℝ := ((65536001 : ℝ) /
        160000000)

def batchSeparateC003Input2547 : RatPair2542 := ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-377408574479356852679047) : ℚ) /
        1441151880758558720000000))

def batchSeparateC003Center2547 : RatPair2542 := ((((-24383075408116702160511401368428587) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((42739218804836351522892539497718419 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchSeparateC003Factor2547 : RatPair2542 := ((((((((((((((1668557456229944236314663 * 10^40
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

noncomputable def batchSeparateC003Error2547 : ℝ := ((64832846880555079729111443469351 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchSeparateC003BaseError2547 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchSeparateC003Position2547 -
      embedPair2542 batchSeparateC003Center2547‖ ≤ batchSeparateC003Error2547 := by
  have hx : |batchSeparateC003Position2547| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchSeparateC003Position2547, storedWidth]
  have hz : ‖embedPair2542 batchSeparateC003Input2547‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchSeparateC003Input2547]
  have hc : (compactExp2547 batchSeparateC003Input2547 6).1 = batchSeparateC003Center2547 := by
      cbv
  have he : ((compactExp2547 batchSeparateC003Input2547 6).2 : ℝ) = batchSeparateC003Error2547 :=
      by
    have hq : (compactExp2547 batchSeparateC003Input2547 6).2 =
        ((64832846880555079729111443469351 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [batchSeparateC003Error2547]
  have h := compactExp_error2547 batchSeparateC003Input2547 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      batchSeparateC003Position2547 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          batchSeparateC003Input2547) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchSeparateC003Position2547, storedWidth,
        nodeModulation2541,
      embedPair2542, batchSeparateC003Input2547, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchSeparateC003ThirdError2547 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchSeparateC003Position2547 -
      embedPair2542 batchSeparateC003Factor2547 * embedPair2542 batchSeparateC003Center2547‖ ≤
        (pairMagnitude2542 batchSeparateC003Factor2547 : ℝ) * batchSeparateC003Error2547 := by
  have hx : |batchSeparateC003Position2547| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchSeparateC003Position2547, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchSeparateC003Position2547 = embedPair2542
          batchSeparateC003Factor2547 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchSeparateC003Position2547, storedWidth, nodeModulation2541, embedPair2542,
      batchSeparateC003Factor2547, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchSeparateC003BaseError2547
    (embedPair_magnitude2542 batchSeparateC003Factor2547)

end ConnesWeilRH.Dev
#print axioms ConnesWeilRH.Dev.batchSeparateC000BaseError2547
#print axioms ConnesWeilRH.Dev.batchSeparateC000ThirdError2547
#print axioms ConnesWeilRH.Dev.batchSeparateC001BaseError2547
#print axioms ConnesWeilRH.Dev.batchSeparateC001ThirdError2547
#print axioms ConnesWeilRH.Dev.batchSeparateC002BaseError2547
#print axioms ConnesWeilRH.Dev.batchSeparateC002ThirdError2547
#print axioms ConnesWeilRH.Dev.batchSeparateC003BaseError2547
#print axioms ConnesWeilRH.Dev.batchSeparateC003ThirdError2547
