import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchN05119PlusPosition2559 : ℝ := (((-65536001) : ℝ) /
        51200000000)

theorem batchN05119PlusZero2559 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchN05119PlusP000Input2559 : RatPair2542 := ((((-((263286 * 10^40
        + 3458256302209985671270638930477541551272) * 10^40
        + 9423035339481514105074357807771063447067)) : ℚ) /
        ((280832 * 10^40
        + 7075746226385963181093901624406268978286) * 10^40
        + 887058614369032185159794907545600000000)),
    ((362039942185747774262029 : ℚ) /
        230584300921369395200000000))

def batchN05119PlusP000Center2559 : RatPair2542 := (((136500817425860321500904602802190359 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((3432002866572359709692667475568657 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchN05119PlusP000Factor2559 : RatPair2542 :=
    ((((-(((((((((((10083947182950582365106859338190 *
    10^40
        + 650061263810994688456161852631153874874) * 10^40
        + 9830190616804845253070254296158051078618) * 10^40
        + 2945805428850951195743235656028922014418) * 10^40
        + 6591004831334205747184303586255833289255) * 10^40
        + 8792857941602503574622234599655809298676) * 10^40
        + 5971683871353875907812248331220019246142) * 10^40
        + 8617983497161497542352708313664186479264) * 10^40
        + 1894926906311953256670179459365753427133) * 10^40
        + 6226215106438464615588359741123906495087) * 10^40
        + 5774489607143870657155438399468108804248) * 10^40
        + 9081423088281913536489344599387488400001)) : ℚ) /
        (((((((((((4238379742105261347983491534 * 10^40
        + 2172069037649486766366597765677661151200) * 10^40
        + 5853233825047869967134612167982835204310) * 10^40
        + 2004241371383870890558389947820930391867) * 10^40
        + 2609395657515468678536021695346502047021) * 10^40
        + 3969922584524792973326842363249227838692) * 10^40
        + 5691608200110521148526377547527735812588) * 10^40
        + 5575238920199263801230497412414437426635) * 10^40
        + 7715087760219813799631673967514501792336) * 10^40
        + 1905589974646242649462012172766479453603) * 10^40
        + 7110975445317504348814751266156901897916) * 10^40
        + 1969083960236412519974344865119767363584)),
    ((((((((((27758624952145892611 * 10^40
        + 1609475215193612021840630662934056690613) * 10^40
        + 9379552395984366208222120381684316615408) * 10^40
        + 1563272120720977716313624926416142403256) * 10^40
        + 3191151728805591860036947684306396961100) * 10^40
        + 191680330552533342305362615246980137969) * 10^40
        + 3330090219288311188406973546566729631638) * 10^40
        + 5243929278765255097186866867704103044266) * 10^40
        + 8441058592730761121014012535845083751631) : ℚ) /
        ((((((((451171493800433 * 10^40
        + 289310041348490574715548455196098577920) * 10^40
        + 7902636938171920959638026447709632006500) * 10^40
        + 7648518850311379011259907846647491564509) * 10^40
        + 3217737556976305284719759745611858997651) * 10^40
        + 3266682424345183093751973875588009603237) * 10^40
        + 4753263076802061328706310558860155993222) * 10^40
        + 9798697653014872404551590343080216518117) * 10^40
        + 7295575607033607306793751502848708837376)))

noncomputable def batchN05119PlusP000Error2559 : ℝ := ((12881658643075348419056961036223 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP000BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP000Center2559‖ ≤ batchN05119PlusP000Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP000Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP000Input2559]
  have hs : compactExp2547 batchN05119PlusP000Input2559 5 =
      (batchN05119PlusP000Center2559, ((12881658643075348419056961036223 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP000Input2559 5).2 : ℝ) = batchN05119PlusP000Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP000Error2559]
  have h := compactExp_error2547 batchN05119PlusP000Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP000Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP000Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP000DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP000Factor2559 * embedPair2542 batchN05119PlusP000Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP000Factor2559 : ℝ) * batchN05119PlusP000Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨0, by omega⟩)
      (storedWidth ⟨0, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP000Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP000Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨0, by omega⟩) (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP000BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP000Factor2559)

def batchN05119PlusP001Input2559 : RatPair2542 := ((((-((337 * 10^40
        + 2725569260792112671247571646139251560861) * 10^40
        + 9231853661209284508739684086695388902881)) : ℚ) /
        ((359 * 10^40
        + 7496679727649814571508006900477875828255) * 10^40
        + 3938416230131927613294794771660800000000)),
    ((362039942185747774262029 : ℚ) /
        230584300921369395200000000))

def batchN05119PlusP001Center2559 : RatPair2542 := (((136501255846990318634319534033465733 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((6864027779350790431441383050582143 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119PlusP001Factor2559 : RatPair2542 := ((((-(((((((((((1630068631261 * 10^40
        + 6394424545983562954009827024291191854039) * 10^40
        + 9625043326219529246791963403354860506047) * 10^40
        + 6583642846445222997254379876792244313690) * 10^40
        + 9516387707287717359600487445236558731154) * 10^40
        + 102819225147497954357865668590531423838) * 10^40
        + 9699284034837374452083292727947517113914) * 10^40
        + 1378849335302044451865865240898270480980) * 10^40
        + 1342334893206863944530190872896183686634) * 10^40
        + 5992096182039511350639261619882898073906) * 10^40
        + 5439561005966995448865953129021254628766) * 10^40
        + 9702178421879489678560920871877837152187)) : ℚ) /
        (((((((((((693669163 * 10^40
        + 9592862739856380285594592324710261825499) * 10^40
        + 2001983453619091663956778015130124273208) * 10^40
        + 6499691634308279264881671178390753386540) * 10^40
        + 3098517178661890766302393953454546081519) * 10^40
        + 8404265830829893956225387230955144698589) * 10^40
        + 644139988022957971382450239700890465716) * 10^40
        + 3908961215050070433576103593838610731500) * 10^40
        + 6646531626044674781167319247658595297818) * 10^40
        + 6374069501189420640494596036077385933114) * 10^40
        + 3060757739686092422004405950221554058041) * 10^40
        + 7230305268242272685920158772598782558208)),
    ((((((((((24729797 * 10^40
        + 4058134587371034368543446512158298927954) * 10^40
        + 2537224615155890043878836668147505168626) * 10^40
        + 895618634031717111017030556483401328860) * 10^40
        + 214164596677152075667367882256728216589) * 10^40
        + 2322055049552934929143468856216722802204) * 10^40
        + 7677917275554595514729405196557750640471) * 10^40
        + 4742166689891686796227931964385319174575) * 10^40
        + 4525378559639115895248953248875059443477) : ℚ) /
        ((((((((404 * 10^40
        + 9778364762535834489062983402079652472870) * 10^40
        + 3798373737324381507248095467743663749494) * 10^40
        + 2113004835996725252119258181634413046350) * 10^40
        + 6272275210159077923488246418401714092448) * 10^40
        + 5028575476107494260550002253111228146223) * 10^40
        + 1584573805121281140132696312080425708340) * 10^40
        + 6811623972839899371827609281611885188981) * 10^40
        + 6480975396836903085471284056881618747392)))

noncomputable def batchN05119PlusP001Error2559 : ℝ := ((6440849362091048947774802736935 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN05119PlusP001BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP001Center2559‖ ≤ batchN05119PlusP001Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP001Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP001Input2559]
  have hs : compactExp2547 batchN05119PlusP001Input2559 5 =
      (batchN05119PlusP001Center2559, ((6440849362091048947774802736935 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP001Input2559 5).2 : ℝ) = batchN05119PlusP001Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP001Error2559]
  have h := compactExp_error2547 batchN05119PlusP001Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP001Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP001Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP001DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP001Factor2559 * embedPair2542 batchN05119PlusP001Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP001Factor2559 : ℝ) * batchN05119PlusP001Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP001Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP001Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP001BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP001Factor2559)

def batchN05119PlusP002Input2559 : RatPair2542 := ((((-((8812 * 10^40
        + 1734255686173283723585744500894473875109) * 10^40
        + 8411743673231391209366387108470216586721)) : ℚ) /
        ((9399 * 10^40
        + 4503095778906693550996648513930263830566) * 10^40
        + 1627135197619074312716716346572800000000)),
    (((-362039942185747774262029) : ℚ) /
        230584300921369395200000000))

def batchN05119PlusP002Center2559 : RatPair2542 := (((68250741369189460011026049908270463 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-3432019594343768381238143401513287) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchN05119PlusP002Factor2559 : RatPair2542 := ((((-(((((((((((515248931832011371689 * 10^40
        + 2478321615328651323569018770958411410535) * 10^40
        + 1790990855583529445197850355736533050572) * 10^40
        + 5668333384911629460683778389241531008577) * 10^40
        + 5115846997355177217501802431583391448122) * 10^40
        + 4844232562876502143760746924399053485332) * 10^40
        + 3794789814400310498015623795357729861352) * 10^40
        + 2500476339447319026709531135168387287872) * 10^40
        + 4332943663899796942128507110684915260898) * 10^40
        + 3361506313391409516458734351725703015169) * 10^40
        + 9674747736166379967662036139571941810167) * 10^40
        + 5595540732297904216489614615158376718267)) : ℚ) /
        (((((((((((220680884618476446 * 10^40
        + 1582494608267086813288118384870308357036) * 10^40
        + 7445756569758167915302455815009176938386) * 10^40
        + 2937437442884967457953335159909335774505) * 10^40
        + 3918940163443079277231028993287898566217) * 10^40
        + 1088357850487932258471712694340194848785) * 10^40
        + 4396301898693080587674164114213064704400) * 10^40
        + 6882325384809681550619331075334080088254) * 10^40
        + 1993243750916695801545802597267584543346) * 10^40
        + 1059561030547137038416022999802391159190) * 10^40
        + 5308379370982843981590708374125161024575) * 10^40
        + 1131658798785141397637384656316088188928)),
    (((-((((((((11479641694897 * 10^40
        + 363405720970856555092627670522628908934) * 10^40
        + 1423708281609312280688304892870211767017) * 10^40
        + 3320497509521104407501435159194969757501) * 10^40
        + 5047289362346850801027421971626813248373) * 10^40
        + 3751859845576786532064390394903663749405) * 10^40
        + 7872612562863303936563222979165370679776) * 10^40
        + 5929444226284897023755438928572305930706) * 10^40
        + 5486264633335158514455401882615658411797)) : ℚ) /
        ((((((((188729362 * 10^40
        + 9819701407096191560439935783291819054518) * 10^40
        + 8477595831999746647809341592274305718131) * 10^40
        + 9925177843627926099243621853950442755649) * 10^40
        + 5197984368996465942067804059686875119529) * 10^40
        + 8427309759846740873593659754282592053766) * 10^40
        + 5419148084508808669851942799006996342341) * 10^40
        + 5593321501482920662721494915137035796268) * 10^40
        + 8717394773851440839659151793766229082112)))

noncomputable def batchN05119PlusP002Error2559 : ℝ := ((12881719466926122466927883876781 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP002BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP002Center2559‖ ≤ batchN05119PlusP002Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP002Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP002Input2559]
  have hs : compactExp2547 batchN05119PlusP002Input2559 5 =
      (batchN05119PlusP002Center2559, ((12881719466926122466927883876781 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP002Input2559 5).2 : ℝ) = batchN05119PlusP002Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP002Error2559]
  have h := compactExp_error2547 batchN05119PlusP002Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP002Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP002Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP002DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP002Factor2559 * embedPair2542 batchN05119PlusP002Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP002Factor2559 : ℝ) * batchN05119PlusP002Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP002Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP002Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP002BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP002Factor2559)

def batchN05119PlusP003Input2559 : RatPair2542 := ((((-((1163858 * 10^40
        + 9372666621744544512988010621716635513137) * 10^40
        + 160111086175322188153156521149969697067)) : ℚ) /
        ((1241422 * 10^40
        + 9791856163289381605629288925280480441376) * 10^40
        + 2180804704512656185159794907545600000000)),
    (((-362039942185747774262029) : ℚ) /
        230584300921369395200000000))

def batchN05119PlusP003Center2559 : RatPair2542 := (((68250804796024137938191755620644039 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-3432022783791019134728763512362665) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchN05119PlusP003Factor2559 : RatPair2542 :=
    ((((-(((((((((((73572109728157441098108546354186090 *
    10^40
        + 9999975260414166243566148416393984297955) * 10^40
        + 637449913133518896805774684037354045443) * 10^40
        + 7310559799306593864798157301745764665185) * 10^40
        + 9647952325029508989739478463171221271357) * 10^40
        + 453032978610065528404280979914295797848) * 10^40
        + 5348128674333048506168366218063954394437) * 10^40
        + 6069918375010480569028319347561437703585) * 10^40
        + 8061908413202144505983945273399008246361) * 10^40
        + 3122674076169820098026914658873595018085) * 10^40
        + 9606277962435872332948515937819828304713) * 10^40
        + 8752608674191258439276288823020300900001)) : ℚ) /
        (((((((((((31625137535450292171820127812961 * 10^40
        + 2177130232434449136413451235567530226156) * 10^40
        + 2894208453903185613413355449602439376043) * 10^40
        + 1795377647526585959473790013596185055335) * 10^40
        + 1826799596223546672338095684927957225170) * 10^40
        + 5478673790879380848074563886669218690183) * 10^40
        + 9854279961472462953012800436580498678859) * 10^40
        + 1628773986216942859704146818659789690448) * 10^40
        + 2762271541225614364614719072747579706726) * 10^40
        + 1349410357848030690428599246349557079717) * 10^40
        + 5861882263625912457295346341113133159629) * 10^40
        + 7691702889402778178946504865119767363584)),
    (((-((((((((3485330819429257894185 * 10^40
        + 6699892618263924831273604777837104350597) * 10^40
        + 287740294221908782244656042965052216991) * 10^40
        + 257898579898408474750628089904161727640) * 10^40
        + 3703160334669221061507074237086593736698) * 10^40
        + 2998112583094584540993416982576203390427) * 10^40
        + 4546352508248146160972975953722612989985) * 10^40
        + 5857617523567092970691548560409008880713) * 10^40
        + 9900066068640798133221396851141069583877)) : ℚ) /
        ((((((((57426026769915242 * 10^40
        + 37248946281463179392937859438651564878) * 10^40
        + 6256287755500187344152790019685904898087) * 10^40
        + 778170784074725160988492459117342265649) * 10^40
        + 1100737857569196410743207737374255904533) * 10^40
        + 390936219895805152906399800831493675186) * 10^40
        + 2352201066425665208458231269990101653944) * 10^40
        + 7115000230235373679619827557598974524932) * 10^40
        + 5176876822868632705495303834282902945792)))

noncomputable def batchN05119PlusP003Error2559 : ℝ := ((3220432766018609887051501160593 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN05119PlusP003BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP003Center2559‖ ≤ batchN05119PlusP003Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP003Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP003Input2559]
  have hs : compactExp2547 batchN05119PlusP003Input2559 5 =
      (batchN05119PlusP003Center2559, ((3220432766018609887051501160593 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP003Input2559 5).2 : ℝ) = batchN05119PlusP003Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP003Error2559]
  have h := compactExp_error2547 batchN05119PlusP003Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP003Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP003Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP003DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP003Factor2559 * embedPair2542 batchN05119PlusP003Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP003Factor2559 : ℝ) * batchN05119PlusP003Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP003Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP003Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP003BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP003Factor2559)

def batchN05119PlusP004Input2559 : RatPair2542 := ((((-((20220 * 10^40
        + 3913594997969425406345180654923455796226) * 10^40
        + 3736468577527371852604511693431154086721)) : ℚ) /
        ((21567 * 10^40
        + 9565109682248283934361041297228882745944) * 10^40
        + 4559280761265714312716716346572800000000)),
    ((362039942185747774262029 : ℚ) /
        230584300921369395200000000))

def batchN05119PlusP004Center2559 : RatPair2542 := (((17062710621529482086045265539037215 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((6864049358109080360221951170609823 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119PlusP004Factor2559 : RatPair2542 := ((((-(((((((((((74773720064794513750892 * 10^40
        + 4059755728142036745138860121404311714520) * 10^40
        + 6440858191914637555083822359907351865476) * 10^40
        + 9952471282838445361511279057117664402499) * 10^40
        + 3187468856421207929920557006845097394592) * 10^40
        + 1956447912133836150287053246803081366890) * 10^40
        + 1127362944026768171376966689035403547187) * 10^40
        + 6717404211685624796204269468168628070316) * 10^40
        + 9719591266280685685931448051985626594763) * 10^40
        + 3642534460322878139512546673548972561433) * 10^40
        + 8778075649370087994243081864097042228133) * 10^40
        + 8562341241986940537391441910080251718267)) : ℚ) /
        (((((((((((32210982602346156350 * 10^40
        + 1389289740622240757214914343126930558346) * 10^40
        + 8151898740371966530652543368809641809667) * 10^40
        + 8823916460360432368148466674171030838295) * 10^40
        + 2335315010254403662020823724213198271953) * 10^40
        + 6369295094528260820490125851938607524547) * 10^40
        + 4109474722283296951812829191642627022949) * 10^40
        + 8072255640072724341845774090398911118600) * 10^40
        + 1137405239893919146967989398133872561957) * 10^40
        + 3404346819408191888477898906532431895882) * 10^40
        + 9346483904045060155026393433733124879841) * 10^40
        + 3641634436846469660395784656316088188928)),
    ((((((((((317126999479023 * 10^40
        + 1159463113549666418182564893552175932922) * 10^40
        + 2507750748892299209910232057899850964080) * 10^40
        + 4362226836936992395597325493855105840225) * 10^40
        + 7436321987153308508474452843087250567429) * 10^40
        + 6110538668028658596232598504348156929144) * 10^40
        + 7867161478494077137405048955173906618441) * 10^40
        + 1349706809671231615952153459098911992822) * 10^40
        + 1201343755393455096608168581834408411797) : ℚ) /
        ((((((((5231974822 * 10^40
        + 6906096713019726877942647176479129866244) * 10^40
        + 6662510641073731573846327264297890137098) * 10^40
        + 5179996429186788767012609795602587845298) * 10^40
        + 3094043366723476417559808317780461020908) * 10^40
        + 8395394464568485210476066080501681500556) * 10^40
        + 9590758151795896500712782863622381730739) * 10^40
        + 5646541376728787547171188043564357479665) * 10^40
        + 4615360855713682874961551793766229082112)))

noncomputable def batchN05119PlusP004Error2559 : ℝ := ((12881737955441474859053564950183 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP004BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP004Center2559‖ ≤ batchN05119PlusP004Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP004Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP004Input2559]
  have hs : compactExp2547 batchN05119PlusP004Input2559 5 =
      (batchN05119PlusP004Center2559, ((12881737955441474859053564950183 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP004Input2559 5).2 : ℝ) = batchN05119PlusP004Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP004Error2559]
  have h := compactExp_error2547 batchN05119PlusP004Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP004Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP004Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP004DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP004Factor2559 * embedPair2542 batchN05119PlusP004Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP004Factor2559 : ℝ) * batchN05119PlusP004Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP004Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP004Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP004BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP004Factor2559)

def batchN05119PlusP005Input2559 : RatPair2542 := ((((-((960078 * 10^40
        + 5966730528020333546101385078683677072997) * 10^40
        + 7567817987265680981754829563449909091201)) : ℚ) /
        ((1024061 * 10^40
        + 7791750441362503302291019533199172422902) * 10^40
        + 8340041887645616555479384722636800000000)),
    ((0 : ℚ) /
        1))

def batchN05119PlusP005Center2559 : RatPair2542 := (((136673470031286836338306468367739617 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN05119PlusP005Factor2559 : RatPair2542 := ((((-(((((((((((847 * 10^40
        + 3683888561095068463678777989840198774317) * 10^40
        + 6734428886671653148869553973473449477049) * 10^40
        + 2880150818840237258755682100991933473051) * 10^40
        + 7577394295545166410927214105332753459122) * 10^40
        + 7626219502580782717846297598045792149401) * 10^40
        + 2520760215615597406325898683322786206726) * 10^40
        + 3674807425994089236936649382072428253221) * 10^40
        + 5515164971857799950421243966696310390459) * 10^40
        + 7076155764012473435829337089564242390517) * 10^40
        + 8796425718263154685347219572165718472983) * 10^40
        + 3777346068988645772175457138042596268799)) : ℚ) /
        (((((((((((74 * 10^40
        + 5327801969660940413049312164441975005102) * 10^40
        + 7244884021555685022993277187471426229344) * 10^40
        + 3355303534293723516304928807064899372845) * 10^40
        + 5551533559161479787842615798612334839920) * 10^40
        + 1624793259210871668463247844295135995745) * 10^40
        + 968809906600267260375053559521820527715) * 10^40
        + 2975788045804350711417848547094744102656) * 10^40
        + 7368271671319591975487397847828288588685) * 10^40
        + 4317887316026978952719303162012619330826) * 10^40
        + 8564943959652956377114490519842098168650) * 10^40
        + 1297321705334993822596342895659229849608)),
    ((0 : ℚ) /
        1))

noncomputable def batchN05119PlusP005Error2559 : ℝ := ((6139936456836747326633114671249 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN05119PlusP005BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP005Center2559‖ ≤ batchN05119PlusP005Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP005Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP005Input2559]
  have hs : compactExp2547 batchN05119PlusP005Input2559 5 =
      (batchN05119PlusP005Center2559, ((6139936456836747326633114671249 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP005Input2559 5).2 : ℝ) = batchN05119PlusP005Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP005Error2559]
  have h := compactExp_error2547 batchN05119PlusP005Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP005Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP005Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP005DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP005Factor2559 * embedPair2542 batchN05119PlusP005Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP005Factor2559 : ℝ) * batchN05119PlusP005Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨5, by omega⟩)
      (storedWidth ⟨5, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP005Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP005Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨5, by omega⟩) (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP005BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP005Factor2559)

def batchN05119PlusP006Input2559 : RatPair2542 := ((((-42950589219609969350134813971797333) : ℚ) /
        45812979799416911656822374400000000),
    ((0 : ℚ) /
        1))

def batchN05119PlusP006Center2559 : RatPair2542 := (((17084236685400188774373767127530255 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1))

def batchN05119PlusP006Factor2559 : RatPair2542 := ((((-(((8947989171271200 * 10^40
        + 34782865693524029381831525301582338425) * 10^40
        + 8155120045004161792376985128279670050581) * 10^40
        + 3205807171387232973984431046956951021037)) : ℚ) /
        (((1613189489073774 * 10^40
        + 7850846335343571448973212773441128977131) * 10^40
        + 2962507789998867944049527356204191909545) * 10^40
        + 6360579062433016208124551624344391831704)),
    ((0 : ℚ) /
        1))

noncomputable def batchN05119PlusP006Error2559 : ℝ := ((6139954885568606149536058363403 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN05119PlusP006BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP006Center2559‖ ≤ batchN05119PlusP006Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP006Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP006Input2559]
  have hs : compactExp2547 batchN05119PlusP006Input2559 5 =
      (batchN05119PlusP006Center2559, ((6139954885568606149536058363403 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP006Input2559 5).2 : ℝ) = batchN05119PlusP006Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP006Error2559]
  have h := compactExp_error2547 batchN05119PlusP006Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP006Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP006Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP006DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP006Factor2559 * embedPair2542 batchN05119PlusP006Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP006Factor2559 : ℝ) * batchN05119PlusP006Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP006Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP006Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP006BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP006Factor2559)

def batchN05119PlusP007Input2559 : RatPair2542 := ((((-((1163858 * 10^40
        + 9372666621744544512988010621716635513137) * 10^40
        + 160111086175322188153156521149969697067)) : ℚ) /
        ((1241422 * 10^40
        + 9791856163289381605629288925280480441376) * 10^40
        + 2180804704512656185159794907545600000000)),
    ((0 : ℚ) /
        1))

def batchN05119PlusP007Center2559 : RatPair2542 := (((68337040729705673475078452725726093 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def batchN05119PlusP007Factor2559 : RatPair2542 := ((((-(((((((((((19128 * 10^40
        + 865441781996895422024016777853167125356) * 10^40
        + 372229560812723705623908988486584964848) * 10^40
        + 9537644146844795499060824752536853101385) * 10^40
        + 3782495075088188846589434225634581276887) * 10^40
        + 1573012755213260077022427968014152549293) * 10^40
        + 3846595314846389141864204617951297207229) * 10^40
        + 7024229406513715494087436430400228670750) * 10^40
        + 2318310142431047597257843895790156743324) * 10^40
        + 6828091602476914074687326730319523171223) * 10^40
        + 4171862694462933730545254267726982698764) * 10^40
        + 6366148952324046171049911745853429491437)) : ℚ) /
        (((((((((((6386 * 10^40
        + 6456637323048469198168547229010814852172) * 10^40
        + 6325261343035465992952793683154342677916) * 10^40
        + 7862561082430737350057411565047771776690) * 10^40
        + 5170988453969852435634113035701938441459) * 10^40
        + 7352418098999878002733501729962373799383) * 10^40
        + 4120957009492970868449801096669771525667) * 10^40
        + 1348027570807402139566396236867122281591) * 10^40
        + 3394523176284333643805142994318621504845) * 10^40
        + 9090519994845613470876344697659887311973) * 10^40
        + 2270380723552988600915698573077764760414) * 10^40
        + 9940696381407630631600706033172564068504)),
    ((0 : ℚ) /
        1))

noncomputable def batchN05119PlusP007Error2559 : ℝ := ((12279926132678179428021601892955 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP007BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP007Center2559‖ ≤ batchN05119PlusP007Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP007Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP007Input2559]
  have hs : compactExp2547 batchN05119PlusP007Input2559 5 =
      (batchN05119PlusP007Center2559, ((12279926132678179428021601892955 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP007Input2559 5).2 : ℝ) = batchN05119PlusP007Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP007Error2559]
  have h := compactExp_error2547 batchN05119PlusP007Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP007Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP007Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP007DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP007Factor2559 * embedPair2542 batchN05119PlusP007Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP007Factor2559 : ℝ) * batchN05119PlusP007Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP007Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP007Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP007BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP007Factor2559)

def batchN05119PlusP008Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((260739661220379310273297 : ℚ) /
        461168601842738790400000000))

def batchN05119PlusP008Center2559 : RatPair2542 := (((68325622342905436484799832349822655 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((618156350172482479625242240996801 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN05119PlusP008Factor2559 : RatPair2542 :=
    ((((-(((((((((((52412750469953550969309748700770 *
    10^40
        + 7229854110291011173497504210838807417023) * 10^40
        + 1570418335025464203459473494109956291790) * 10^40
        + 8690006189286810250311313117420928965433) * 10^40
        + 242739907051106831383304854169842466306) * 10^40
        + 4736105766927040410277410927160088922186) * 10^40
        + 6153760492085980095615902867500839092825) * 10^40
        + 6545689044541907825964651775322000536909) * 10^40
        + 6940347863122086635579037565413021689707) * 10^40
        + 343358095709763318560184454410138907572) * 10^40
        + 6557075258353501904541842929883247696616) * 10^40
        + 8063200111406909515793139673683557865209)) : ℚ) /
        (((((((((((166987709152466848905419922790 * 10^40
        + 7902067180490755273591264756201052062845) * 10^40
        + 1295178240211244743905335306408512041230) * 10^40
        + 9328058599808571621467921676928771256567) * 10^40
        + 1156301154391221567934544969527722447347) * 10^40
        + 6469634572688598445188152653426605559611) * 10^40
        + 1039196180597552591176230265990782196071) * 10^40
        + 3645828107844780175664067316102952195777) * 10^40
        + 9723332351859607151055810887552804005532) * 10^40
        + 4245481410255366168537473327222816170889) * 10^40
        + 7458356318482143752135441901226259871744) * 10^40
        + 9650023575513512928614179460479069454336)),
    ((((((((((2431041759403422708 * 10^40
        + 2282327752508354163862751019036694709776) * 10^40
        + 2845738133693516349175303880214205449976) * 10^40
        + 5090109563728456935160381643157340750347) * 10^40
        + 3951316448816255292480865232107077688863) * 10^40
        + 2370029484278430845202938711596385864644) * 10^40
        + 492769625029992914594954787818625864786) * 10^40
        + 5143884385451397029406656997291469181869) * 10^40
        + 5604769971270285292579294879147022468887) : ℚ) /
        ((((((((789760565096797 * 10^40
        + 8095510052729368356927070454129803701516) * 10^40
        + 3743019781947976825806172922048722462656) * 10^40
        + 7549517672188252238923971472068227595581) * 10^40
        + 396392107312125827044244572623346852688) * 10^40
        + 4622570372462752472580018727281281253007) * 10^40
        + 5566503809205145580154189391855073684950) * 10^40
        + 8769806980714736530281372283185850359703) * 10^40
        + 7690234925784503979189695810609031938048)))

noncomputable def batchN05119PlusP008Error2559 : ℝ := ((12495657720597068928919179654881 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP008BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP008Center2559‖ ≤ batchN05119PlusP008Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP008Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP008Input2559]
  have hs : compactExp2547 batchN05119PlusP008Input2559 5 =
      (batchN05119PlusP008Center2559, ((12495657720597068928919179654881 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP008Input2559 5).2 : ℝ) = batchN05119PlusP008Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP008Error2559]
  have h := compactExp_error2547 batchN05119PlusP008Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP008Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP008Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP008DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP008Factor2559 * embedPair2542 batchN05119PlusP008Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP008Factor2559 : ℝ) * batchN05119PlusP008Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP008Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP008Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP008BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP008Factor2559)

def batchN05119PlusP009Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((387788191040974601829711 : ℚ) /
        461168601842738790400000000))

def batchN05119PlusP009Center2559 : RatPair2542 := (((17078017101937518900140786536420235 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((459649832294031300763089470419493 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)))

def batchN05119PlusP009Factor2559 : RatPair2542 :=
    ((((-(((((((((((114034179922522488439047564270069 *
    10^40
        + 3045713313411589277806150717211407985835) * 10^40
        + 1177697978645036015289435053359628847845) * 10^40
        + 532008505893467064417440296425966395717) * 10^40
        + 9461734828773713568858903448859588566622) * 10^40
        + 9602961896568191771515308160406978612264) * 10^40
        + 5861944665937052615101356417853685941898) * 10^40
        + 5229886540829138181738923582291887639527) * 10^40
        + 6504135024701883540042261937425964271717) * 10^40
        + 9807471984051827124963337868996101456907) * 10^40
        + 1128760812317335924800016324521305448577) * 10^40
        + 3777979404656827901950879133782976261177)) : ℚ) /
        (((((((((((166987709152466848905419922790 * 10^40
        + 7902067180490755273591264756201052062845) * 10^40
        + 1295178240211244743905335306408512041230) * 10^40
        + 9328058599808571621467921676928771256567) * 10^40
        + 1156301154391221567934544969527722447347) * 10^40
        + 6469634572688598445188152653426605559611) * 10^40
        + 1039196180597552591176230265990782196071) * 10^40
        + 3645828107844780175664067316102952195777) * 10^40
        + 9723332351859607151055810887552804005532) * 10^40
        + 4245481410255366168537473327222816170889) * 10^40
        + 7458356318482143752135441901226259871744) * 10^40
        + 9650023575513512928614179460479069454336)),
    ((((((((((53449370544747498475 * 10^40
        + 9786094470226093126228882580956318869190) * 10^40
        + 7884684906141206741582189240909124328279) * 10^40
        + 5665789167665391808401812153248953139119) * 10^40
        + 924570702916009507653121715922932571840) * 10^40
        + 4071285975674563831315139220440778453804) * 10^40
        + 1106964217885815924583123518018514397421) * 10^40
        + 7219086422976803358292352740357584413947) * 10^40
        + 5246870918658680052029960583147421971839) : ℚ) /
        ((((((((5528323955677584 * 10^40
        + 6668570369105578498489493178908625910614) * 10^40
        + 6201138473635837780643210454341057238597) * 10^40
        + 2846623705317765672467800304477593169067) * 10^40
        + 2774744751184880789309712008363427968819) * 10^40
        + 2357992607239267308060131090968968771052) * 10^40
        + 8965526664436019061079325742985515794656) * 10^40
        + 1388648865003155711969605982300952517926) * 10^40
        + 3831644480491527854327870674263223566336)))

noncomputable def batchN05119PlusP009Error2559 : ℝ := ((3150295552163713166720439407129 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN05119PlusP009BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP009Center2559‖ ≤ batchN05119PlusP009Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP009Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP009Input2559]
  have hs : compactExp2547 batchN05119PlusP009Input2559 5 =
      (batchN05119PlusP009Center2559, ((3150295552163713166720439407129 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP009Input2559 5).2 : ℝ) = batchN05119PlusP009Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP009Error2559]
  have h := compactExp_error2547 batchN05119PlusP009Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP009Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP009Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP009DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP009Factor2559 * embedPair2542 batchN05119PlusP009Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP009Factor2559 : ℝ) * batchN05119PlusP009Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP009Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP009Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP009BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP009Factor2559)

def batchN05119PlusP010Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((230684447942438333698521 : ℚ) /
        230584300921369395200000000))

def batchN05119PlusP010Center2559 : RatPair2542 := (((34150895378412517260951066159778865 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((4374707784189990731171144820701449 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119PlusP010Factor2559 : RatPair2542 :=
    ((((-(((((((((((40190767739203840200403397926492 *
    10^40
        + 8688479452517268022778042600858960337315) * 10^40
        + 8967156653054720273144921147287303624444) * 10^40
        + 1478302825169437264276701054295872943389) * 10^40
        + 1524493787965857976862773600576980196054) * 10^40
        + 4023748649762368058604416939193676410525) * 10^40
        + 4110236785574128315118283674415593604123) * 10^40
        + 6010680497236838607930422596839139781713) * 10^40
        + 8658482078584983978561630581695806499541) * 10^40
        + 5336976289467093559367244445754103579341) * 10^40
        + 5466013545661762533297318023211581970501) * 10^40
        + 5521301241526631429741292126711886723401)) : ℚ) /
        (((((((((((41746927288116712226354980697 * 10^40
        + 6975516795122688818397816189050263015711) * 10^40
        + 2823794560052811185976333826602128010307) * 10^40
        + 7332014649952142905366980419232192814141) * 10^40
        + 7789075288597805391983636242381930611836) * 10^40
        + 9117408643172149611297038163356651389902) * 10^40
        + 7759799045149388147794057566497695549017) * 10^40
        + 8411457026961195043916016829025738048944) * 10^40
        + 4930833087964901787763952721888201001383) * 10^40
        + 1061370352563841542134368331805704042722) * 10^40
        + 4364589079620535938033860475306564967936) * 10^40
        + 2412505893878378232153544865119767363584)),
    ((((((((((11122431908123032106 * 10^40
        + 7524811091955110225036140702996124094582) * 10^40
        + 8670469980014020853562884827099790517762) * 10^40
        + 4254151918710789894612650158265436947505) * 10^40
        + 321237424252648108867155946974587629246) * 10^40
        + 1746074769467788155001195443589404801999) * 10^40
        + 7230327221751836471738140388223914160964) * 10^40
        + 9423588398666484988133233479757226594722) * 10^40
        + 7734667528441825244896081517935017442873) : ℚ) /
        ((((((((691040494459698 * 10^40
        + 833571296138197312311186647363578238826) * 10^40
        + 8275142309204479722580401306792632154824) * 10^40
        + 6605827963164720709058475038059699146133) * 10^40
        + 4096843093898110098663714001045428496102) * 10^40
        + 4044749075904908413507516386371121096381) * 10^40
        + 6120690833054502382634915717873189474332) * 10^40
        + 173581108125394463996200747787619064740) * 10^40
        + 7978955560061440981790983834282902945792)))

noncomputable def batchN05119PlusP010Error2559 : ℝ := ((6331205461928702441632722340293 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN05119PlusP010BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP010Center2559‖ ≤ batchN05119PlusP010Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP010Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP010Input2559]
  have hs : compactExp2547 batchN05119PlusP010Input2559 5 =
      (batchN05119PlusP010Center2559, ((6331205461928702441632722340293 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP010Input2559 5).2 : ℝ) = batchN05119PlusP010Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP010Error2559]
  have h := compactExp_error2547 batchN05119PlusP010Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP010Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP010Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP010DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP010Factor2559 * embedPair2542 batchN05119PlusP010Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP010Factor2559 : ℝ) * batchN05119PlusP010Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP010Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP010Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP010BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP010Factor2559)

def batchN05119PlusP011Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((255213677437476200797801 : ℚ) /
        230584300921369395200000000))

def batchN05119PlusP011Center2559 : RatPair2542 := (((136587898056514574882487620153157195 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((4839695760755360189548135580818693 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119PlusP011Factor2559 : RatPair2542 :=
    ((((-(((((((((((49104562336696632337893760587211 *
    10^40
        + 8995179826547401312167248998277801381080) * 10^40
        + 7610713680825201420474616607552618820974) * 10^40
        + 3867655225710131620103548285473550541871) * 10^40
        + 6055765953488569115533153532890210044122) * 10^40
        + 3090730832706246989746995102851773291159) * 10^40
        + 3539880843425560768879857420474233765545) * 10^40
        + 3074316969374115815203351526849610279494) * 10^40
        + 8710843788245515700790424707849109689338) * 10^40
        + 5680843889640721765708137138376050545495) * 10^40
        + 4095665670278654711901190085835616414062) * 10^40
        + 3826738953546369665095413580605625825641)) : ℚ) /
        (((((((((((41746927288116712226354980697 * 10^40
        + 6975516795122688818397816189050263015711) * 10^40
        + 2823794560052811185976333826602128010307) * 10^40
        + 7332014649952142905366980419232192814141) * 10^40
        + 7789075288597805391983636242381930611836) * 10^40
        + 9117408643172149611297038163356651389902) * 10^40
        + 7759799045149388147794057566497695549017) * 10^40
        + 8411457026961195043916016829025738048944) * 10^40
        + 4930833087964901787763952721888201001383) * 10^40
        + 1061370352563841542134368331805704042722) * 10^40
        + 4364589079620535938033860475306564967936) * 10^40
        + 2412505893878378232153544865119767363584)),
    ((((((((((14984073767669017933 * 10^40
        + 4948775562973296805643427615233864562682) * 10^40
        + 3762719467619129012367800929905111382948) * 10^40
        + 3036934508755190700756447832428490905188) * 10^40
        + 8277310015522604565257360755337365226569) * 10^40
        + 7105462258419362171213611245467161182339) * 10^40
        + 6719475333542105003641260843967410117395) * 10^40
        + 8134881827184947078073455757513893330793) * 10^40
        + 8990347469066918871769759002775307376873) : ℚ) /
        ((((((((691040494459698 * 10^40
        + 833571296138197312311186647363578238826) * 10^40
        + 8275142309204479722580401306792632154824) * 10^40
        + 6605827963164720709058475038059699146133) * 10^40
        + 4096843093898110098663714001045428496102) * 10^40
        + 4044749075904908413507516386371121096381) * 10^40
        + 6120690833054502382634915717873189474332) * 10^40
        + 173581108125394463996200747787619064740) * 10^40
        + 7978955560061440981790983834282902945792)))

noncomputable def batchN05119PlusP011Error2559 : ℝ := ((3175819955750226711556527560723 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN05119PlusP011BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP011Center2559‖ ≤ batchN05119PlusP011Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP011Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP011Input2559]
  have hs : compactExp2547 batchN05119PlusP011Input2559 5 =
      (batchN05119PlusP011Center2559, ((3175819955750226711556527560723 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP011Input2559 5).2 : ℝ) = batchN05119PlusP011Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP011Error2559]
  have h := compactExp_error2547 batchN05119PlusP011Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP011Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP011Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP011DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP011Factor2559 * embedPair2542 batchN05119PlusP011Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP011Factor2559 : ℝ) * batchN05119PlusP011Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP011Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP011Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP011BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP011Factor2559)

def batchN05119PlusP012Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((5612399119318874813509 : ℚ) /
        4611686018427387904000000))

def batchN05119PlusP012Center2559 : RatPair2542 := (((136569985156640262541922752597216529 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((332578144415372647539056407421451 : ℚ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)))

def batchN05119PlusP012Factor2559 : RatPair2542 :=
    ((((-(((((((((((14821473102801206468647134015030 *
    10^40
        + 9581074823330163877913106775254499050633) * 10^40
        + 4389528062976025351228607039329639528901) * 10^40
        + 1191863580449567541839672968091831360715) * 10^40
        + 5308314454750582011020648125547470171760) * 10^40
        + 7700114393652226483818026932194727541948) * 10^40
        + 8605298586915148011910846922373138547721) * 10^40
        + 6065524436712705876924638483250811919019) * 10^40
        + 7249869043177639289956344916242274256120) * 10^40
        + 9616931955415246677553604964605672972583) * 10^40
        + 9837194550499302803636918277052078701902) * 10^40
        + 8131837119134931675328204854576950900513)) : ℚ) /
        (((((((((((10436731822029178056588745174 * 10^40
        + 4243879198780672204599454047262565753927) * 10^40
        + 8205948640013202796494083456650532002576) * 10^40
        + 9333003662488035726341745104808048203535) * 10^40
        + 4447268822149451347995909060595482652959) * 10^40
        + 2279352160793037402824259540839162847475) * 10^40
        + 6939949761287347036948514391624423887254) * 10^40
        + 4602864256740298760979004207256434512236) * 10^40
        + 1232708271991225446940988180472050250345) * 10^40
        + 7765342588140960385533592082951426010680) * 10^40
        + 6091147269905133984508465118826641241984) * 10^40
        + 603126473469594558038386216279941840896)),
    ((((((((((2480031241052341365 * 10^40
        + 536737662560438339775046655396428272914) * 10^40
        + 7896350873903383052398645624641531988586) * 10^40
        + 2898207057800575656475472498925599951900) * 10^40
        + 8204151863526072886708880716394817208901) * 10^40
        + 7097766328543508688575607021941256272342) * 10^40
        + 612629669015528968421731975370792303179) * 10^40
        + 3631066824021782173734875289194825295612) * 10^40
        + 7387169503464526749930250941689959907925) : ℚ) /
        ((((((((86380061807462 * 10^40
        + 2604196412017274664038898330920447279853) * 10^40
        + 3534392788650559965322550163349079019353) * 10^40
        + 825728495395590088632309379757462393266) * 10^40
        + 6762105386737263762332964250130678562012) * 10^40
        + 8005593634488113551688439548296390137047) * 10^40
        + 7015086354131812797829364464734148684291) * 10^40
        + 5021697638515674307999525093473452383092) * 10^40
        + 5997369445007680122723872979285362868224)))

noncomputable def batchN05119PlusP012Error2559 : ℝ := ((12745648418151806341403167315331 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP012BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP012Center2559‖ ≤ batchN05119PlusP012Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP012Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP012Input2559]
  have hs : compactExp2547 batchN05119PlusP012Input2559 5 =
      (batchN05119PlusP012Center2559, ((12745648418151806341403167315331 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP012Input2559 5).2 : ℝ) = batchN05119PlusP012Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP012Error2559]
  have h := compactExp_error2547 batchN05119PlusP012Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP012Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP012Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP012DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP012Factor2559 * embedPair2542 batchN05119PlusP012Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP012Factor2559 : ℝ) * batchN05119PlusP012Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP012Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP012Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP012BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP012Factor2559)

def batchN05119PlusP013Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((60754466143128272313291 : ℚ) /
        46116860184273879040000000))

def batchN05119PlusP013Center2559 : RatPair2542 := (((68276091431291567924075361002274879 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((5760026563927281923243175505227791 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119PlusP013Factor2559 : RatPair2542 :=
    ((((-(((((((((((69404797229751986751048331755670 *
    10^40
        + 2134395054172230241321595302615008813057) * 10^40
        + 9690583170975154660134843973756797644478) * 10^40
        + 3411485275684749326326195032620967382338) * 10^40
        + 8367224757036967526241723816295792113854) * 10^40
        + 7761192133139205435368964598126226388946) * 10^40
        + 1454868917863006038996187950574803267806) * 10^40
        + 5832219679709123768227498568649187803026) * 10^40
        + 6294336036903192517720131338833875504850) * 10^40
        + 1429976616397440882040651038908384408360) * 10^40
        + 4763715117614414856930433551738834008404) * 10^40
        + 5393607031476970167973921751938996484777)) : ℚ) /
        (((((((((((41746927288116712226354980697 * 10^40
        + 6975516795122688818397816189050263015711) * 10^40
        + 2823794560052811185976333826602128010307) * 10^40
        + 7332014649952142905366980419232192814141) * 10^40
        + 7789075288597805391983636242381930611836) * 10^40
        + 9117408643172149611297038163356651389902) * 10^40
        + 7759799045149388147794057566497695549017) * 10^40
        + 8411457026961195043916016829025738048944) * 10^40
        + 4930833087964901787763952721888201001383) * 10^40
        + 1061370352563841542134368331805704042722) * 10^40
        + 4364589079620535938033860475306564967936) * 10^40
        + 2412505893878378232153544865119767363584)),
    ((((((((((25096940336686668701 * 10^40
        + 4091598500249176400352948430083357103507) * 10^40
        + 3328591807381870957828678915340618139583) * 10^40
        + 2664636958882608974985453658350592470296) * 10^40
        + 4203987935778255500887148806821580638058) * 10^40
        + 8596059400697281631570577214670422117091) * 10^40
        + 1374597575845817554595728572006454940844) * 10^40
        + 7234124916799783934936848743379485130479) * 10^40
        + 8188633489281831897728554569039623540535) : ℚ) /
        ((((((((691040494459698 * 10^40
        + 833571296138197312311186647363578238826) * 10^40
        + 8275142309204479722580401306792632154824) * 10^40
        + 6605827963164720709058475038059699146133) * 10^40
        + 4096843093898110098663714001045428496102) * 10^40
        + 4044749075904908413507516386371121096381) * 10^40
        + 6120690833054502382634915717873189474332) * 10^40
        + 173581108125394463996200747787619064740) * 10^40
        + 7978955560061440981790983834282902945792)))

noncomputable def batchN05119PlusP013Error2559 : ℝ := ((12784292140381913196007361187239 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP013BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP013Center2559‖ ≤ batchN05119PlusP013Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP013Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP013Input2559]
  have hs : compactExp2547 batchN05119PlusP013Input2559 5 =
      (batchN05119PlusP013Center2559, ((12784292140381913196007361187239 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP013Input2559 5).2 : ℝ) = batchN05119PlusP013Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP013Error2559]
  have h := compactExp_error2547 batchN05119PlusP013Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP013Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP013Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP013DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP013Factor2559 * embedPair2542 batchN05119PlusP013Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP013Factor2559 : ℝ) * batchN05119PlusP013Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP013Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP013Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP013BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP013Factor2559)

def batchN05119PlusP014Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((346671309892138695845011 : ℚ) /
        230584300921369395200000000))

def batchN05119PlusP014Center2559 : RatPair2542 := (((136515471229987342697102690921951069 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((1643218362847538391886509892120143 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN05119PlusP014Factor2559 : RatPair2542 :=
    ((((-(((((((((((90273243816134564814427899616005 *
    10^40
        + 2343747428865367863319599627815551693683) * 10^40
        + 8839220731334124148980218544094070867376) * 10^40
        + 1403047676765856368337844755304226270252) * 10^40
        + 407765321930964991177800104585070149970) * 10^40
        + 3709041913496161660846584393507404753195) * 10^40
        + 6794658775466479890931822998938194951408) * 10^40
        + 1992759915276120531137630775573741576122) * 10^40
        + 1012779352149157439581427032603418709855) * 10^40
        + 7769839442518889317276946850401367540228) * 10^40
        + 4325708073258359695004501208536457559634) * 10^40
        + 2979405398659080250124150611767590129921)) : ℚ) /
        (((((((((((41746927288116712226354980697 * 10^40
        + 6975516795122688818397816189050263015711) * 10^40
        + 2823794560052811185976333826602128010307) * 10^40
        + 7332014649952142905366980419232192814141) * 10^40
        + 7789075288597805391983636242381930611836) * 10^40
        + 9117408643172149611297038163356651389902) * 10^40
        + 7759799045149388147794057566497695549017) * 10^40
        + 8411457026961195043916016829025738048944) * 10^40
        + 4930833087964901787763952721888201001383) * 10^40
        + 1061370352563841542134368331805704042722) * 10^40
        + 4364589079620535938033860475306564967936) * 10^40
        + 2412505893878378232153544865119767363584)),
    ((((((((((37160547402063440598 * 10^40
        + 1665843366030567021886769351877220097175) * 10^40
        + 1590105687916649471377299411545616740869) * 10^40
        + 9248236279427952786541028366188495264498) * 10^40
        + 4067189258293023090160267847302277910873) * 10^40
        + 9500622271575195306543597513669546701425) * 10^40
        + 4740665955074995203351848225119851204582) * 10^40
        + 5533555984338373756056156803750390695077) * 10^40
        + 9224292845198251838824683537697468503323) : ℚ) /
        ((((((((691040494459698 * 10^40
        + 833571296138197312311186647363578238826) * 10^40
        + 8275142309204479722580401306792632154824) * 10^40
        + 6605827963164720709058475038059699146133) * 10^40
        + 4096843093898110098663714001045428496102) * 10^40
        + 4044749075904908413507516386371121096381) * 10^40
        + 6120690833054502382634915717873189474332) * 10^40
        + 173581108125394463996200747787619064740) * 10^40
        + 7978955560061440981790983834282902945792)))

noncomputable def batchN05119PlusP014Error2559 : ℝ := ((6427989802512944552770335821299 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN05119PlusP014BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP014Center2559‖ ≤ batchN05119PlusP014Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP014Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP014Input2559]
  have hs : compactExp2547 batchN05119PlusP014Input2559 5 =
      (batchN05119PlusP014Center2559, ((6427989802512944552770335821299 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP014Input2559 5).2 : ℝ) = batchN05119PlusP014Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP014Error2559]
  have h := compactExp_error2547 batchN05119PlusP014Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP014Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP014Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP014DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP014Factor2559 * embedPair2542 batchN05119PlusP014Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP014Factor2559 : ℝ) * batchN05119PlusP014Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP014Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP014Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP014BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP014Factor2559)

def batchN05119PlusP015Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((377408574479356852679047 : ℚ) /
        230584300921369395200000000))

def batchN05119PlusP015Center2559 : RatPair2542 := (((136486191720340377288908220414040657 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((7155139427850531329191306651274829 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119PlusP015Factor2559 : RatPair2542 :=
    ((((-(((((((((((106918297124310064110573081133461 *
    10^40
        + 7835373993997243331390614051058574448962) * 10^40
        + 9192417843025980146305091272241205930454) * 10^40
        + 9034757802711724272107206159402828592999) * 10^40
        + 6742787373919861941812833935978031733115) * 10^40
        + 2418892169897707264292733517147582463668) * 10^40
        + 2024616795779418114074649971437489370107) * 10^40
        + 9872700401845909396915555395401418053086) * 10^40
        + 2495905248808441150680573236953735938439) * 10^40
        + 5433577563325309740850615336529605114867) * 10^40
        + 1108171408698521703474480866860924050303) * 10^40
        + 4998202313806048515088666963460623868553)) : ℚ) /
        (((((((((((41746927288116712226354980697 * 10^40
        + 6975516795122688818397816189050263015711) * 10^40
        + 2823794560052811185976333826602128010307) * 10^40
        + 7332014649952142905366980419232192814141) * 10^40
        + 7789075288597805391983636242381930611836) * 10^40
        + 9117408643172149611297038163356651389902) * 10^40
        + 7759799045149388147794057566497695549017) * 10^40
        + 8411457026961195043916016829025738048944) * 10^40
        + 4930833087964901787763952721888201001383) * 10^40
        + 1061370352563841542134368331805704042722) * 10^40
        + 4364589079620535938033860475306564967936) * 10^40
        + 2412505893878378232153544865119767363584)),
    ((((((((((47853067891200068879 * 10^40
        + 3904280572093361861102277802290418680405) * 10^40
        + 4987363189192157584509694877949434427271) * 10^40
        + 1694681226838078736661448868430302622866) * 10^40
        + 8075940110425631140584699741852707751271) * 10^40
        + 1488605524299472788496416839521971458973) * 10^40
        + 3660822158326460802343135392750444143056) * 10^40
        + 5950923567616777041697997556375864946585) * 10^40
        + 3346445012941179535581595318728884349927) : ℚ) /
        ((((((((691040494459698 * 10^40
        + 833571296138197312311186647363578238826) * 10^40
        + 8275142309204479722580401306792632154824) * 10^40
        + 6605827963164720709058475038059699146133) * 10^40
        + 4096843093898110098663714001045428496102) * 10^40
        + 4044749075904908413507516386371121096381) * 10^40
        + 6120690833054502382634915717873189474332) * 10^40
        + 173581108125394463996200747787619064740) * 10^40
        + 7978955560061440981790983834282902945792)))

noncomputable def batchN05119PlusP015Error2559 : ℝ := ((12907410932199791456265434005263 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP015BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP015Center2559‖ ≤ batchN05119PlusP015Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP015Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP015Input2559]
  have hs : compactExp2547 batchN05119PlusP015Input2559 5 =
      (batchN05119PlusP015Center2559, ((12907410932199791456265434005263 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP015Input2559 5).2 : ℝ) = batchN05119PlusP015Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP015Error2559]
  have h := compactExp_error2547 batchN05119PlusP015Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP015Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP015Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP015DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP015Factor2559 * embedPair2542 batchN05119PlusP015Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP015Factor2559 : ℝ) * batchN05119PlusP015Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP015Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP015Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP015BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP015Factor2559)

def batchN05119PlusP016Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((199810861117846303095609 : ℚ) /
        115292150460684697600000000))

def batchN05119PlusP016Center2559 : RatPair2542 := (((136463486139812693564813795357287141 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((1893962465352736764012372614639977 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN05119PlusP016Factor2559 : RatPair2542 :=
    ((((-(((((((((((29956742164716588524747324203178 *
    10^40
        + 4433965022745014122319327917360973566221) * 10^40
        + 3084855128651259742767818245990811010724) * 10^40
        + 3419907489067968041173353235538745541228) * 10^40
        + 5224030615216314091176931809141824256319) * 10^40
        + 2797467450177481242635565671948179010035) * 10^40
        + 7926016542243612143837318551806174481285) * 10^40
        + 1787258131436617715084198887310490966315) * 10^40
        + 4176138167511218612509242399010412315667) * 10^40
        + 626671370600297565361425184378163512250) * 10^40
        + 1365407441920049784659869781811390285174) * 10^40
        + 9935243482074918021816111832935502373897)) : ℚ) /
        (((((((((((10436731822029178056588745174 * 10^40
        + 4243879198780672204599454047262565753927) * 10^40
        + 8205948640013202796494083456650532002576) * 10^40
        + 9333003662488035726341745104808048203535) * 10^40
        + 4447268822149451347995909060595482652959) * 10^40
        + 2279352160793037402824259540839162847475) * 10^40
        + 6939949761287347036948514391624423887254) * 10^40
        + 4602864256740298760979004207256434512236) * 10^40
        + 1232708271991225446940988180472050250345) * 10^40
        + 7765342588140960385533592082951426010680) * 10^40
        + 6091147269905133984508465118826641241984) * 10^40
        + 603126473469594558038386216279941840896)),
    ((((((((((7093043719438756453 * 10^40
        + 8176522349392795621528661868876071106542) * 10^40
        + 3361469458139858521975875260557793698820) * 10^40
        + 4414604024997343482898709916604194646809) * 10^40
        + 3598988187908373344774887878016538742683) * 10^40
        + 4583006889445021089914788613773782849965) * 10^40
        + 1493030597362471555396749039148852412408) * 10^40
        + 1174549257797408520638568167139570661242) * 10^40
        + 8054485302420625480504048711329631335001) : ℚ) /
        ((((((((86380061807462 * 10^40
        + 2604196412017274664038898330920447279853) * 10^40
        + 3534392788650559965322550163349079019353) * 10^40
        + 825728495395590088632309379757462393266) * 10^40
        + 6762105386737263762332964250130678562012) * 10^40
        + 8005593634488113551688439548296390137047) * 10^40
        + 7015086354131812797829364464734148684291) * 10^40
        + 5021697638515674307999525093473452383092) * 10^40
        + 5997369445007680122723872979285362868224)))

noncomputable def batchN05119PlusP016Error2559 : ℝ := ((12944613758394931643391090394651 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP016BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP016Center2559‖ ≤ batchN05119PlusP016Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP016Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP016Input2559]
  have hs : compactExp2547 batchN05119PlusP016Input2559 5 =
      (batchN05119PlusP016Center2559, ((12944613758394931643391090394651 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP016Input2559 5).2 : ℝ) = batchN05119PlusP016Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP016Error2559]
  have h := compactExp_error2547 batchN05119PlusP016Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP016Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP016Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP016DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP016Factor2559 * embedPair2542 batchN05119PlusP016Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP016Factor2559 : ℝ) * batchN05119PlusP016Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP016Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP016Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP016BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP016Factor2559)

def batchN05119PlusP017Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((442769373018475956606027 : ℚ) /
        230584300921369395200000000))

def batchN05119PlusP017Center2559 : RatPair2542 := (((136415676210486263560913340223322917 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((2098211062269229239063800347812243 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN05119PlusP017Factor2559 : RatPair2542 :=
    ((((-(((((((((((147010408655275228752083999847165 *
    10^40
        + 4852083481686819849840219450707965256908) * 10^40
        + 461762780201614951039782348982163052400) * 10^40
        + 5261599876459924974473417505431085508391) * 10^40
        + 6234166500765777443577964065414028164877) * 10^40
        + 2479304726602709428936612627850051538570) * 10^40
        + 9219662649278665178519728686781871732970) * 10^40
        + 2305843274719380650124126301108947608411) * 10^40
        + 9672939838704922546963048969414720212237) * 10^40
        + 7127560361944290278073096439570307642057) * 10^40
        + 5364084260610013731948855143901310296032) * 10^40
        + 7411747913617133341579025130221141410833)) : ℚ) /
        (((((((((((41746927288116712226354980697 * 10^40
        + 6975516795122688818397816189050263015711) * 10^40
        + 2823794560052811185976333826602128010307) * 10^40
        + 7332014649952142905366980419232192814141) * 10^40
        + 7789075288597805391983636242381930611836) * 10^40
        + 9117408643172149611297038163356651389902) * 10^40
        + 7759799045149388147794057566497695549017) * 10^40
        + 8411457026961195043916016829025738048944) * 10^40
        + 4930833087964901787763952721888201001383) * 10^40
        + 1061370352563841542134368331805704042722) * 10^40
        + 4364589079620535938033860475306564967936) * 10^40
        + 2412505893878378232153544865119767363584)),
    ((((((((((11006398966495522661 * 10^40
        + 4687635031626966845928950542302270297455) * 10^40
        + 8456066678891138658939221399903122289731) * 10^40
        + 3736534831979002051573906766279628879698) * 10^40
        + 9997039420130591180697171273273472045674) * 10^40
        + 7762840160081120887056051969596294611860) * 10^40
        + 8899690552088823407353060735562208900700) * 10^40
        + 9986859262551914500597351202472974124955) * 10^40
        + 3473025541673321255262998585564296712421) : ℚ) /
        ((((((((98720070637099 * 10^40
        + 7261938756591171044615883806766225462689) * 10^40
        + 5467877472743497103225771615256090307832) * 10^40
        + 943689709023531529865496434008528449447) * 10^40
        + 6299549013414015728380530571577918356586) * 10^40
        + 577821296557844059072502340910160156625) * 10^40
        + 9445812976150643197519273673981884210618) * 10^40
        + 8596225872589342066285171535398231294962) * 10^40
        + 9711279365723062997398711976326128992256)))

noncomputable def batchN05119PlusP017Error2559 : ℝ := ((6508480007995604327801519311485 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN05119PlusP017BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP017Center2559‖ ≤ batchN05119PlusP017Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP017Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP017Input2559]
  have hs : compactExp2547 batchN05119PlusP017Input2559 5 =
      (batchN05119PlusP017Center2559, ((6508480007995604327801519311485 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP017Input2559 5).2 : ℝ) = batchN05119PlusP017Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP017Error2559]
  have h := compactExp_error2547 batchN05119PlusP017Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP017Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP017Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP017DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP017Factor2559 * embedPair2542 batchN05119PlusP017Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP017Factor2559 : ℝ) * batchN05119PlusP017Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP017Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP017Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP017BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP017Factor2559)

def batchN05119PlusP018Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((114770645411675231749613 : ℚ) /
        57646075230342348800000000))

def batchN05119PlusP018Center2559 : RatPair2542 := (((34099081494107878000368747841990865 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((8701655628932101754443427486953391 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119PlusP018Factor2559 : RatPair2542 := ((((-(((((((((((9875833323241355200516698276746
    *
    10^40
        + 7251452005802061596052549667958138848578) * 10^40
        + 6873987820797249561350345107435063975231) * 10^40
        + 7191336774420676133001920514419414756765) * 10^40
        + 3738168882109412876283714634808863338789) * 10^40
        + 2866598279108267282868624391335431372509) * 10^40
        + 1491310461043613797401558991858779384328) * 10^40
        + 7845409065134386751422222655647917190873) * 10^40
        + 1021023976921294985764100484232096933151) * 10^40
        + 3231499975856292817179010124725622901692) * 10^40
        + 6008901883554148725767951693807821770866) * 10^40
        + 1222962502683175527057886319845471181313)) : ℚ) /
        (((((((((((2609182955507294514147186293 * 10^40
        + 6060969799695168051149863511815641438481) * 10^40
        + 9551487160003300699123520864162633000644) * 10^40
        + 2333250915622008931585436276202012050883) * 10^40
        + 8611817205537362836998977265148870663239) * 10^40
        + 8069838040198259350706064885209790711868) * 10^40
        + 9234987440321836759237128597906105971813) * 10^40
        + 6150716064185074690244751051814108628059) * 10^40
        + 308177067997806361735247045118012562586) * 10^40
        + 4441335647035240096383398020737856502670) * 10^40
        + 1522786817476283496127116279706660310496) * 10^40
        + 150781618367398639509596554069985460224)),
    ((((((((((1341121766940995670 * 10^40
        + 2757351485286235094714828295793819871192) * 10^40
        + 8954642100611489289587430584829226657834) * 10^40
        + 1403989933842850366760309086996064831708) * 10^40
        + 6397401370432409443652744978059609948990) * 10^40
        + 8082542920712298218873485018105980279697) * 10^40
        + 7411921256047652511663212173688197005470) * 10^40
        + 4914429651431181805138673301495174975746) * 10^40
        + 1412145533313620456586955936428943375973) : ℚ) /
        ((((((((10797507725932 * 10^40
        + 7825524551502159333004862291365055909981) * 10^40
        + 6691799098581319995665318770418634877419) * 10^40
        + 1353216061924448761079038672469682799158) * 10^40
        + 3345263173342157970291620531266334820251) * 10^40
        + 6000699204311014193961054943537048767130) * 10^40
        + 9626885794266476599728670558091768585536) * 10^40
        + 4377712204814459288499940636684181547886) * 10^40
        + 5749671180625960015340484122410670358528)))

noncomputable def batchN05119PlusP018Error2559 : ℝ := ((13044340625762406390314361543371 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP018BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP018Center2559‖ ≤ batchN05119PlusP018Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP018Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP018Input2559]
  have hs : compactExp2547 batchN05119PlusP018Input2559 5 =
      (batchN05119PlusP018Center2559, ((13044340625762406390314361543371 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP018Input2559 5).2 : ℝ) = batchN05119PlusP018Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP018Error2559]
  have h := compactExp_error2547 batchN05119PlusP018Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP018Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP018Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP018DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP018Factor2559 * embedPair2542 batchN05119PlusP018Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP018Factor2559 : ℝ) * batchN05119PlusP018Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP018Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP018Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP018BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP018Factor2559)

def batchN05119PlusP019Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((24428249467783476683391 : ℚ) /
        11529215046068469760000000))

def batchN05119PlusP019Center2559 : RatPair2542 := (((136359581535321501782222006292740117 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((2314911905255504722830856807450735 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN05119PlusP019Factor2559 : RatPair2542 :=
    ((((-(((((((((((11181773584580347933583564204213 *
    10^40
        + 9057665429814724150420720200428578072465) * 10^40
        + 2180875416217532095925411536944736545533) * 10^40
        + 1026768589631470662437880817403897157318) * 10^40
        + 8729921757635375334840205958131403651470) * 10^40
        + 902523659794837104916441699159600117301) * 10^40
        + 3893677363224058304148674013055676613778) * 10^40
        + 7429985476797861637542670191526539858574) * 10^40
        + 5198580569792818056860944678847019078898) * 10^40
        + 6090983363885203911009279366432626996605) * 10^40
        + 9202370880015118989925393785666198908500) * 10^40
        + 2170263721981255765068066661670845467697)) : ℚ) /
        (((((((((((2609182955507294514147186293 * 10^40
        + 6060969799695168051149863511815641438481) * 10^40
        + 9551487160003300699123520864162633000644) * 10^40
        + 2333250915622008931585436276202012050883) * 10^40
        + 8611817205537362836998977265148870663239) * 10^40
        + 8069838040198259350706064885209790711868) * 10^40
        + 9234987440321836759237128597906105971813) * 10^40
        + 6150716064185074690244751051814108628059) * 10^40
        + 308177067997806361735247045118012562586) * 10^40
        + 4441335647035240096383398020737856502670) * 10^40
        + 1522786817476283496127116279706660310496) * 10^40
        + 150781618367398639509596554069985460224)),
    ((((((((((1615088272391579668 * 10^40
        + 3983002095232501892689039824995276291706) * 10^40
        + 7378285579252381667017459930254419475682) * 10^40
        + 1662597633938925646309656177586401484638) * 10^40
        + 376146830286785247055691801888921925541) * 10^40
        + 1151809553067744021141700006696670578546) * 10^40
        + 486483078386281561777479605213080821079) * 10^40
        + 2551470462093687280810526590399356114373) * 10^40
        + 9774970619095668135902975016372473047635) : ℚ) /
        ((((((((10797507725932 * 10^40
        + 7825524551502159333004862291365055909981) * 10^40
        + 6691799098581319995665318770418634877419) * 10^40
        + 1353216061924448761079038672469682799158) * 10^40
        + 3345263173342157970291620531266334820251) * 10^40
        + 6000699204311014193961054943537048767130) * 10^40
        + 9626885794266476599728670558091768585536) * 10^40
        + 4377712204814459288499940636684181547886) * 10^40
        + 5749671180625960015340484122410670358528)))

noncomputable def batchN05119PlusP019Error2559 : ℝ := ((3273465884848201459230052508107 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN05119PlusP019BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP019Center2559‖ ≤ batchN05119PlusP019Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP019Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP019Input2559]
  have hs : compactExp2547 batchN05119PlusP019Input2559 5 =
      (batchN05119PlusP019Center2559, ((3273465884848201459230052508107 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP019Input2559 5).2 : ℝ) = batchN05119PlusP019Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP019Error2559]
  have h := compactExp_error2547 batchN05119PlusP019Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP019Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP019Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP019DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP019Factor2559 * embedPair2542 batchN05119PlusP019Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP019Factor2559 : ℝ) * batchN05119PlusP019Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP019Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP019Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP019BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP019Factor2559)

def batchN05119PlusP020Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((520624750538575899551419 : ℚ) /
        230584300921369395200000000))

def batchN05119PlusP020Center2559 : RatPair2542 := (((68158517073077529248233548624970471 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((4933121530772559661698980588528081 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchN05119PlusP020Factor2559 : RatPair2542 :=
    ((((-(((((((((((203105660238200058426689718932687 *
    10^40
        + 2298599562782014620580547755342212990484) * 10^40
        + 3882108965504799512003178998380628478726) * 10^40
        + 1797108948616599895036388788396763046639) * 10^40
        + 1790048301003442825010987973617951499504) * 10^40
        + 1616649069593307754845951817886746429454) * 10^40
        + 398876907036591641478649522278957247686) * 10^40
        + 6111932317821632236377840301151176528933) * 10^40
        + 9860015039844903093516244148850195877546) * 10^40
        + 2212983603229092492020150252815156906818) * 10^40
        + 11012801734111199960682044683103762073) * 10^40
        + 7197485187603834963723524666592066460081)) : ℚ) /
        (((((((((((41746927288116712226354980697 * 10^40
        + 6975516795122688818397816189050263015711) * 10^40
        + 2823794560052811185976333826602128010307) * 10^40
        + 7332014649952142905366980419232192814141) * 10^40
        + 7789075288597805391983636242381930611836) * 10^40
        + 9117408643172149611297038163356651389902) * 10^40
        + 7759799045149388147794057566497695549017) * 10^40
        + 8411457026961195043916016829025738048944) * 10^40
        + 4930833087964901787763952721888201001383) * 10^40
        + 1061370352563841542134368331805704042722) * 10^40
        + 4364589079620535938033860475306564967936) * 10^40
        + 2412505893878378232153544865119767363584)),
    ((((((((((17854812790581816778 * 10^40
        + 475617787074993140885314163185998790135) * 10^40
        + 4776898525040935879250341833901363756468) * 10^40
        + 3569039056390653953689748635676443709817) * 10^40
        + 53833777549593582549581464173290038271) * 10^40
        + 7366558917278705660829707299381776109749) * 10^40
        + 8363534987797507041352134999886225988085) * 10^40
        + 6375507889974853382480534961574338185382) * 10^40
        + 6002063958235795332179130751125385645461) : ℚ) /
        ((((((((98720070637099 * 10^40
        + 7261938756591171044615883806766225462689) * 10^40
        + 5467877472743497103225771615256090307832) * 10^40
        + 943689709023531529865496434008528449447) * 10^40
        + 6299549013414015728380530571577918356586) * 10^40
        + 577821296557844059072502340910160156625) * 10^40
        + 9445812976150643197519273673981884210618) * 10^40
        + 8596225872589342066285171535398231294962) * 10^40
        + 9711279365723062997398711976326128992256)))

noncomputable def batchN05119PlusP020Error2559 : ℝ := ((13147771897933847848607074750115 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP020BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP020Center2559‖ ≤ batchN05119PlusP020Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP020Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP020Input2559]
  have hs : compactExp2547 batchN05119PlusP020Input2559 5 =
      (batchN05119PlusP020Center2559, ((13147771897933847848607074750115 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP020Input2559 5).2 : ℝ) = batchN05119PlusP020Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP020Error2559]
  have h := compactExp_error2547 batchN05119PlusP020Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP020Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP020Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP020DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP020Factor2559 * embedPair2542 batchN05119PlusP020Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP020Factor2559 : ℝ) * batchN05119PlusP020Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP020Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP020Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP020BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP020Factor2559)

def batchN05119PlusP021Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((547379874475946380671387 : ℚ) /
        230584300921369395200000000))

def batchN05119PlusP021Center2559 : RatPair2542 := (((136279461011980091077114577015383379 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((10372321670565837098370678678115289 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119PlusP021Factor2559 : RatPair2542 :=
    ((((-(((((((((((224476106575074419557202408381383 *
    10^40
        + 5136518462002997660624410778667861259840) * 10^40
        + 7351180206197515743044388147890259931124) * 10^40
        + 2770203017309366493683110406980930221568) * 10^40
        + 8143144273676758517597612861611219294024) * 10^40
        + 555935527528903827784569451041812736033) * 10^40
        + 1005788794389359463287712203237404912859) * 10^40
        + 6990947173438049018841610230675667586736) * 10^40
        + 8296227293273591890281669590301524484619) * 10^40
        + 8691167206620836981091201055079597681689) * 10^40
        + 8311223133767724287395172802384762993840) * 10^40
        + 6990384208565595274729072594971460849393)) : ℚ) /
        (((((((((((41746927288116712226354980697 * 10^40
        + 6975516795122688818397816189050263015711) * 10^40
        + 2823794560052811185976333826602128010307) * 10^40
        + 7332014649952142905366980419232192814141) * 10^40
        + 7789075288597805391983636242381930611836) * 10^40
        + 9117408643172149611297038163356651389902) * 10^40
        + 7759799045149388147794057566497695549017) * 10^40
        + 8411457026961195043916016829025738048944) * 10^40
        + 4930833087964901787763952721888201001383) * 10^40
        + 1061370352563841542134368331805704042722) * 10^40
        + 4364589079620535938033860475306564967936) * 10^40
        + 2412505893878378232153544865119767363584)),
    ((((((((((145182022108736072128 * 10^40
        + 8360109062995162956316500622711085088448) * 10^40
        + 5620894887478338893190185464528317188079) * 10^40
        + 3303127561301432977974810258001595648234) * 10^40
        + 9912760343754286851916533700311867318646) * 10^40
        + 1547961022388476176457878097624655930567) * 10^40
        + 1282192745250065065962862607594787138313) * 10^40
        + 2816246786107729518658535343498991381464) * 10^40
        + 600334761255644794623455720311086583987) : ℚ) /
        ((((((((691040494459698 * 10^40
        + 833571296138197312311186647363578238826) * 10^40
        + 8275142309204479722580401306792632154824) * 10^40
        + 6605827963164720709058475038059699146133) * 10^40
        + 4096843093898110098663714001045428496102) * 10^40
        + 4044749075904908413507516386371121096381) * 10^40
        + 6120690833054502382634915717873189474332) * 10^40
        + 173581108125394463996200747787619064740) * 10^40
        + 7978955560061440981790983834282902945792)))

noncomputable def batchN05119PlusP021Error2559 : ℝ := ((13192804946534098182217288829769 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP021BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP021Center2559‖ ≤ batchN05119PlusP021Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP021Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP021Input2559]
  have hs : compactExp2547 batchN05119PlusP021Input2559 5 =
      (batchN05119PlusP021Center2559, ((13192804946534098182217288829769 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP021Input2559 5).2 : ℝ) = batchN05119PlusP021Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP021Error2559]
  have h := compactExp_error2547 batchN05119PlusP021Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP021Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP021Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP021DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP021Factor2559 * embedPair2542 batchN05119PlusP021Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP021Factor2559 : ℝ) * batchN05119PlusP021Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP021Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP021Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP021BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP021Factor2559)

def batchN05119PlusP022Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((112214826711468142236233 : ℚ) /
        46116860184273879040000000))

def batchN05119PlusP022Center2559 : RatPair2542 := (((136259502735619449854657829734465215 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((10631296477627131283789678185309895 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119PlusP022Factor2559 : RatPair2542 :=
    ((((-(((((((((((235828559518351568207941616984060 *
    10^40
        + 8105911964156242203650118625016634810260) * 10^40
        + 2722164504412903641989912053253489742390) * 10^40
        + 7882419816848796839157195563277547757396) * 10^40
        + 5948316937777283658793723321028209674935) * 10^40
        + 3023746689604798160890840951610152211667) * 10^40
        + 6702603633590176031785483517428724748964) * 10^40
        + 2722389265290449749474996645873383669053) * 10^40
        + 8284908214286334206830939144294783951950) * 10^40
        + 6227478913702999391811397669513020357042) * 10^40
        + 7786878403575953380734933503797414219048) * 10^40
        + 2423856771691861981174188964675688632577)) : ℚ) /
        (((((((((((41746927288116712226354980697 * 10^40
        + 6975516795122688818397816189050263015711) * 10^40
        + 2823794560052811185976333826602128010307) * 10^40
        + 7332014649952142905366980419232192814141) * 10^40
        + 7789075288597805391983636242381930611836) * 10^40
        + 9117408643172149611297038163356651389902) * 10^40
        + 7759799045149388147794057566497695549017) * 10^40
        + 8411457026961195043916016829025738048944) * 10^40
        + 4930833087964901787763952721888201001383) * 10^40
        + 1061370352563841542134368331805704042722) * 10^40
        + 4364589079620535938033860475306564967936) * 10^40
        + 2412505893878378232153544865119767363584)),
    ((((((((((156315016773754402852 * 10^40
        + 2190199528678852417853808693760079238820) * 10^40
        + 2758498087541962998474905319018250057960) * 10^40
        + 376461089823336494830716225856933653251) * 10^40
        + 9099190659570589820509937145058307281377) * 10^40
        + 1729377916832637345090709046257714407831) * 10^40
        + 3880311018987389833554605873139444444529) * 10^40
        + 1496989516405337460009947441602448374716) * 10^40
        + 6972133847590693156884491757706821823205) : ℚ) /
        ((((((((691040494459698 * 10^40
        + 833571296138197312311186647363578238826) * 10^40
        + 8275142309204479722580401306792632154824) * 10^40
        + 6605827963164720709058475038059699146133) * 10^40
        + 4096843093898110098663714001045428496102) * 10^40
        + 4044749075904908413507516386371121096381) * 10^40
        + 6120690833054502382634915717873189474332) * 10^40
        + 173581108125394463996200747787619064740) * 10^40
        + 7978955560061440981790983834282902945792)))

noncomputable def batchN05119PlusP022Error2559 : ℝ := ((825991878142992683952069869231 : ℝ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))

theorem batchN05119PlusP022BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP022Center2559‖ ≤ batchN05119PlusP022Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP022Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP022Input2559]
  have hs : compactExp2547 batchN05119PlusP022Input2559 5 =
      (batchN05119PlusP022Center2559, ((825991878142992683952069869231 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP022Input2559 5).2 : ℝ) = batchN05119PlusP022Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP022Error2559]
  have h := compactExp_error2547 batchN05119PlusP022Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP022Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP022Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP022DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP022Factor2559 * embedPair2542 batchN05119PlusP022Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP022Factor2559 : ℝ) * batchN05119PlusP022Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP022Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP022Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP022BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP022Factor2559)

def batchN05119PlusP023Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((300278613592663314364333 : ℚ) /
        115292150460684697600000000))

def batchN05119PlusP023Center2559 : RatPair2542 := (((136199204618707897869796079847515455 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((11377750734869726781486693679313987 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119PlusP023Factor2559 : RatPair2542 :=
    ((((-(((((((((((67532512552326470325086113394267 *
    10^40
        + 391709790016031059411452989948692819915) * 10^40
        + 4878044409985390368941474785351319475008) * 10^40
        + 6512549889066950604740405938692510288003) * 10^40
        + 7495873934793878361637073733837527365090) * 10^40
        + 5416021549056743332056115814413400365023) * 10^40
        + 4521024552713950409983987615525799432672) * 10^40
        + 6251536037401666163692527956301326179687) * 10^40
        + 820414397245958136736317355601924692213) * 10^40
        + 9633492198907346246681184142945724294638) * 10^40
        + 2107312660186165058207050286681121354593) * 10^40
        + 1492355216130425201696218662484675521409)) : ℚ) /
        (((((((((((10436731822029178056588745174 * 10^40
        + 4243879198780672204599454047262565753927) * 10^40
        + 8205948640013202796494083456650532002576) * 10^40
        + 9333003662488035726341745104808048203535) * 10^40
        + 4447268822149451347995909060595482652959) * 10^40
        + 2279352160793037402824259540839162847475) * 10^40
        + 6939949761287347036948514391624423887254) * 10^40
        + 4602864256740298760979004207256434512236) * 10^40
        + 1232708271991225446940988180472050250345) * 10^40
        + 7765342588140960385533592082951426010680) * 10^40
        + 6091147269905133984508465118826641241984) * 10^40
        + 603126473469594558038386216279941840896)),
    ((((((((((23946715947897287901 * 10^40
        + 1166066764342797127433419149008414422842) * 10^40
        + 7360360228039413332548856931666381892554) * 10^40
        + 5936430929287589584707505796416652872902) * 10^40
        + 4477984427004821983446778615135887158689) * 10^40
        + 8842468997130553498579380901632418703793) * 10^40
        + 5055121733167543056535205276717337399004) * 10^40
        + 9359453763349098308473503656246964872359) * 10^40
        + 484483853769677909772745129720750428581) : ℚ) /
        ((((((((86380061807462 * 10^40
        + 2604196412017274664038898330920447279853) * 10^40
        + 3534392788650559965322550163349079019353) * 10^40
        + 825728495395590088632309379757462393266) * 10^40
        + 6762105386737263762332964250130678562012) * 10^40
        + 8005593634488113551688439548296390137047) * 10^40
        + 7015086354131812797829364464734148684291) * 10^40
        + 5021697638515674307999525093473452383092) * 10^40
        + 5997369445007680122723872979285362868224)))

noncomputable def batchN05119PlusP023Error2559 : ℝ := ((13282429446161009485739197185313 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP023BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP023Center2559‖ ≤ batchN05119PlusP023Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP023Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP023Input2559]
  have hs : compactExp2547 batchN05119PlusP023Input2559 5 =
      (batchN05119PlusP023Center2559, ((13282429446161009485739197185313 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP023Input2559 5).2 : ℝ) = batchN05119PlusP023Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP023Error2559]
  have h := compactExp_error2547 batchN05119PlusP023Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP023Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP023Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP023DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP023Factor2559 * embedPair2542 batchN05119PlusP023Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP023Factor2559 : ℝ) * batchN05119PlusP023Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP023Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP023Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP023BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP023Factor2559)

def batchN05119PlusP024Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((309351029057948556428147 : ℚ) /
        115292150460684697600000000))

def batchN05119PlusP024Center2559 : RatPair2542 := (((136170122513951164501213750743429735 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((5860338835959521097523383063763275 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchN05119PlusP024Factor2559 : RatPair2542 :=
    ((((-(((((((((((71668912257729503207981715058131 *
    10^40
        + 8671871035037095331468869770166825935261) * 10^40
        + 8888370987747788757354162484069891096480) * 10^40
        + 720188856128421935324170507339526122679) * 10^40
        + 700166994862580888075320642663759944060) * 10^40
        + 4063238588937575794999211212212651950089) * 10^40
        + 7019001977739202912271855764193666584521) * 10^40
        + 720737755894811990436466931583771522161) * 10^40
        + 9888956584709178354650600648958701772015) * 10^40
        + 8069861932379042886645213728745613242240) * 10^40
        + 6703559815778957986387576559722264365620) * 10^40
        + 8769584631780490962527200212974320359489)) : ℚ) /
        (((((((((((10436731822029178056588745174 * 10^40
        + 4243879198780672204599454047262565753927) * 10^40
        + 8205948640013202796494083456650532002576) * 10^40
        + 9333003662488035726341745104808048203535) * 10^40
        + 4447268822149451347995909060595482652959) * 10^40
        + 2279352160793037402824259540839162847475) * 10^40
        + 6939949761287347036948514391624423887254) * 10^40
        + 4602864256740298760979004207256434512236) * 10^40
        + 1232708271991225446940988180472050250345) * 10^40
        + 7765342588140960385533592082951426010680) * 10^40
        + 6091147269905133984508465118826641241984) * 10^40
        + 603126473469594558038386216279941840896)),
    ((((((((((26177092682954528742 * 10^40
        + 7849652574594548433236496047447997111061) * 10^40
        + 5877163545345124755455794072723191091802) * 10^40
        + 2367519902767465546798577380050679454747) * 10^40
        + 7384695307846637706661750831852426198746) * 10^40
        + 5100915183803859603485519053431917025248) * 10^40
        + 7374178240655704523312438790628961583298) * 10^40
        + 9028680998252026782111181340274042586919) * 10^40
        + 1845351792579124192262855101498647391419) : ℚ) /
        ((((((((86380061807462 * 10^40
        + 2604196412017274664038898330920447279853) * 10^40
        + 3534392788650559965322550163349079019353) * 10^40
        + 825728495395590088632309379757462393266) * 10^40
        + 6762105386737263762332964250130678562012) * 10^40
        + 8005593634488113551688439548296390137047) * 10^40
        + 7015086354131812797829364464734148684291) * 10^40
        + 5021697638515674307999525093473452383092) * 10^40
        + 5997369445007680122723872979285362868224)))

noncomputable def batchN05119PlusP024Error2559 : ℝ := ((416032698224622400720861711269 : ℝ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))

theorem batchN05119PlusP024BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP024Center2559‖ ≤ batchN05119PlusP024Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP024Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP024Input2559]
  have hs : compactExp2547 batchN05119PlusP024Input2559 5 =
      (batchN05119PlusP024Center2559, ((416032698224622400720861711269 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP024Input2559 5).2 : ℝ) = batchN05119PlusP024Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP024Error2559]
  have h := compactExp_error2547 batchN05119PlusP024Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP024Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP024Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP024DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP024Factor2559 * embedPair2542 batchN05119PlusP024Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP024Factor2559 : ℝ) * batchN05119PlusP024Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP024Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP024Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP024BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP024Factor2559)

def batchN05119PlusP025Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((10022692915539018190833 : ℚ) /
        3602879701896396800000000))

def batchN05119PlusP025Center2559 : RatPair2542 := (((34033109734973648369730144164083891 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((6075269928763691513585373015931861 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchN05119PlusP025Factor2559 : RatPair2542 := ((((-(((((((((((75223780723728681999746550773 *
    10^40
        + 6199483944801879918634727081506601220302) * 10^40
        + 1736643682018786834547212326794358618039) * 10^40
        + 4845350949244510910581970767644949502179) * 10^40
        + 6267896927744505425218389957266513192178) * 10^40
        + 9764828633445679547180317004805706322456) * 10^40
        + 9341593350746715440145305164079275273382) * 10^40
        + 6398317134645621300690057402801428716704) * 10^40
        + 3079041496192831288224195527397002675524) * 10^40
        + 6023521296160115239958122079380255318620) * 10^40
        + 5382019835196336057236074316720966768536) * 10^40
        + 4091251282973250444885062374241653877433)) : ℚ) /
        (((((((((((10192120919950369195887446 * 10^40
        + 4593988163280059250199804154343029849369) * 10^40
        + 701372996718762893355951253375635285158) * 10^40
        + 7665364261389148472389005610453914109573) * 10^40
        + 7650827410959130323582027254941987776028) * 10^40
        + 2804960304844524450588695565957850744968) * 10^40
        + 2379824169688757174840770033585570726452) * 10^40
        + 3969338734625722948008768558796148861828) * 10^40
        + 3555891316671866431100528308769992236572) * 10^40
        + 6032973967371231406626497648518507251963) * 10^40
        + 5552823386005766732406746547967604141837) * 10^40
        + 8750588990696747650935584361539335880704)),
    ((((((((((18163662529861 * 10^40
        + 1839117976153915473046780284557594465304) * 10^40
        + 601126770682046063793730174881626475678) * 10^40
        + 4676185316498159089315107040256640859218) * 10^40
        + 1427846506665796906461640903457528685334) * 10^40
        + 3140369393023549101656519239116345260620) * 10^40
        + 9166769842686943656666302737356421284199) * 10^40
        + 5478271797354515358418185320297482623704) * 10^40
        + 2792830050352998905018659821728236706577) : ℚ) /
        ((((((((53798169 * 10^40
        + 745215967417448093507518558983833730548) * 10^40
        + 208748663699271471021980953637049678306) * 10^40
        + 7473450221301328944359659394126038692217) * 10^40
        + 3905768421472284270158892157707525840714) * 10^40
        + 7852140469044983214157136684146521928057) * 10^40
        + 747516875028869711000277665968581053534) * 10^40
        + 4862904464844770480206116967975908223959) * 10^40
        + 4023366498281950663464681025211866284032)))

noncomputable def batchN05119PlusP025Error2559 : ℝ := ((13351459823462372787032717524695 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP025BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP025Center2559‖ ≤ batchN05119PlusP025Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP025Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP025Input2559]
  have hs : compactExp2547 batchN05119PlusP025Input2559 5 =
      (batchN05119PlusP025Center2559, ((13351459823462372787032717524695 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP025Input2559 5).2 : ℝ) = batchN05119PlusP025Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP025Error2559]
  have h := compactExp_error2547 batchN05119PlusP025Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP025Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP025Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP025DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP025Factor2559 * embedPair2542 batchN05119PlusP025Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP025Factor2559 : ℝ) * batchN05119PlusP025Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP025Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP025Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP025BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP025Factor2559)

def batchN05119PlusP026Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((20771944281655350607437 : ℚ) /
        7205759403792793600000000))

def batchN05119PlusP026Center2559 : RatPair2542 := (((34023131462415362580258952376753619 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((3147429093847085052822186108505965 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN05119PlusP026Factor2559 : RatPair2542 := ((((-(((((((((((323074464223415397063200835178
    *
    10^40
        + 8993748428480249288787051416475451046355) * 10^40
        + 5589976294831331974075388093145587481746) * 10^40
        + 1517527367424391069386399501131053386834) * 10^40
        + 617744667367924462050946619424913506690) * 10^40
        + 8697471529296413893786991687664751021916) * 10^40
        + 6618632315337297859884638900986784280342) * 10^40
        + 3894494861745935824547823984042117345474) * 10^40
        + 8765464136355885221268778449190298469135) * 10^40
        + 796874930330748236748848122279727694285) * 10^40
        + 7830201667065805896411012622121333005797) * 10^40
        + 3748442592638427056962074150298184612289)) : ℚ) /
        (((((((((((40768483679801476783549785 * 10^40
        + 8375952653120237000799216617372119397476) * 10^40
        + 2805491986875051573423805013502541140635) * 10^40
        + 661457045556593889556022441815656438295) * 10^40
        + 603309643836521294328109019767951104113) * 10^40
        + 1219841219378097802354782263831402979872) * 10^40
        + 9519296678755028699363080134342282905809) * 10^40
        + 5877354938502891792035074235184595447313) * 10^40
        + 4223565266687465724402113235079968946290) * 10^40
        + 4131895869484925626505990594074029007854) * 10^40
        + 2211293544023066929626986191870416567351) * 10^40
        + 5002355962786990603742337446157343522816)),
    ((((((((((7920764077784427 * 10^40
        + 8581403485155802138578474831209122780373) * 10^40
        + 2453322118137060942379694986246342572979) * 10^40
        + 4174497256510561640297685633757125882481) * 10^40
        + 9763498717775143578110390377431538564061) * 10^40
        + 1305385350768317167971492049309572164639) * 10^40
        + 4391924581066329998879060568615829591748) * 10^40
        + 5641865812806619787252240409735154675809) * 10^40
        + 6854791513527677305483559656948118611589) : ℚ) /
        ((((((((21088882277 * 10^40
        + 2124659227639652654947275121662822374824) * 10^40
        + 1829476170114416640616533825723473896244) * 10^40
        + 9592486750120946188986482497407167349217) * 10^40
        + 1061221217135433902285725821350129560195) * 10^40
        + 8039063865633419949597580185436595798373) * 10^40
        + 3026615011316926712108845059683772985518) * 10^40
        + 6258550219150028240797851446556023792085) * 10^40
        + 7159667326524660078154961883051583340544)))

noncomputable def batchN05119PlusP026Error2559 : ℝ := ((13390745980153853631447785687381 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP026BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP026Center2559‖ ≤ batchN05119PlusP026Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP026Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP026Input2559]
  have hs : compactExp2547 batchN05119PlusP026Input2559 5 =
      (batchN05119PlusP026Center2559, ((13390745980153853631447785687381 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP026Input2559 5).2 : ℝ) = batchN05119PlusP026Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP026Error2559]
  have h := compactExp_error2547 batchN05119PlusP026Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP026Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP026Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP026DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP026Factor2559 * embedPair2542 batchN05119PlusP026Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP026Factor2559 : ℝ) * batchN05119PlusP026Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP026Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP026Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP026BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP026Factor2559)

def batchN05119PlusP027Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((43640783619197408678627 : ℚ) /
        14411518807585587200000000))

def batchN05119PlusP027Center2559 : RatPair2542 := (((136032432655015167825611034479563907 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((3305807546124834590887137723935529 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN05119PlusP027Factor2559 : RatPair2542 := ((((-(((((((((((1425887147747073635763101014823
    *
    10^40
        + 6451728498121925027762242048320839001776) * 10^40
        + 870665458569197756638529167250203332847) * 10^40
        + 5651318099015924623826852984552390150545) * 10^40
        + 8966423659385195416884689990886369753148) * 10^40
        + 8986885740996251738299690340456953838013) * 10^40
        + 5771473294107301296544780254810471007138) * 10^40
        + 749704017346257664809254983773625549932) * 10^40
        + 8837659630553260417818923054613300223) * 10^40
        + 6287956992202216291939765882427061194397) * 10^40
        + 1522186915385415371982117233285328981780) * 10^40
        + 5708319589837325015156074497651070965473)) : ℚ) /
        (((((((((((163073934719205907134199143 * 10^40
        + 3503810612480948003196866469488477589905) * 10^40
        + 1221967947500206293695220054010164562540) * 10^40
        + 2645828182226375558224089767262625753180) * 10^40
        + 2413238575346085177312436079071804416452) * 10^40
        + 4879364877512391209419129055325611919491) * 10^40
        + 8077186715020114797452320537369131623238) * 10^40
        + 3509419754011567168140296940738381789253) * 10^40
        + 6894261066749862897608452940319875785161) * 10^40
        + 6527583477939702506023962376296116031416) * 10^40
        + 8845174176092267718507944767481666269406) * 10^40
        + 9423851147962414969349784629374091264)),
    ((((((((((73429853715312966 * 10^40
        + 2766659754877857298910563514663846380584) * 10^40
        + 7641745951498916804660832996193071625702) * 10^40
        + 5959784559314380675538966936812231805893) * 10^40
        + 5386752660655896461855710403001159655091) * 10^40
        + 3860253417435989911878938773485409777786) * 10^40
        + 1174109431944922883641820056358415562160) * 10^40
        + 7972406072149658393005965991529431629341) * 10^40
        + 4167195916529316743757640369427422188427) : ℚ) /
        ((((((((168711058217 * 10^40
        + 6997273821117221239578200973302578998593) * 10^40
        + 4635809360915333124932270605787791169959) * 10^40
        + 6739894000967569511891859979257338793736) * 10^40
        + 8489769737083471218285806570801036481566) * 10^40
        + 4312510925067359596780641483492766386986) * 10^40
        + 4212920090535413696870760477470183884149) * 10^40
        + 68401753200225926382811572448190336685) * 10^40
        + 7277338612197280625239695064412666724352)))

noncomputable def batchN05119PlusP027Error2559 : ℝ := ((6723744351291080908153136387505 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN05119PlusP027BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP027Center2559‖ ≤ batchN05119PlusP027Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP027Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP027Input2559]
  have hs : compactExp2547 batchN05119PlusP027Input2559 5 =
      (batchN05119PlusP027Center2559, ((6723744351291080908153136387505 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP027Input2559 5).2 : ℝ) = batchN05119PlusP027Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP027Error2559]
  have h := compactExp_error2547 batchN05119PlusP027Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP027Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP027Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP027DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP027Factor2559 * embedPair2542 batchN05119PlusP027Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP027Factor2559 : ℝ) * batchN05119PlusP027Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP027Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP027Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP027BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP027Factor2559)

def batchN05119PlusP028Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((177883892884016178388727 : ℚ) /
        57646075230342348800000000))

def batchN05119PlusP028Center2559 : RatPair2542 := (((136007825957138393757603533801864003 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((13473968567806708132812455163415457 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119PlusP028Factor2559 : RatPair2542 :=
    ((((-(((((((((((23689509876256120152922349522852 *
    10^40
        + 7107767874891229341976890384505951998774) * 10^40
        + 8513022350867595599692100614912729081313) * 10^40
        + 140238124731095754160578658881912080245) * 10^40
        + 689826819461576972112172649532914693671) * 10^40
        + 8540233971565926604946374702452826850538) * 10^40
        + 7189287933699559069347028858677886054537) * 10^40
        + 8925490692201878024756310664771241126561) * 10^40
        + 1345378452019017713158605268056976330262) * 10^40
        + 945247379153232189445363161178088051912) * 10^40
        + 2641767190703995606226330358670697755220) * 10^40
        + 2779767955703287786632574739740794294953)) : ℚ) /
        (((((((((((2609182955507294514147186293 * 10^40
        + 6060969799695168051149863511815641438481) * 10^40
        + 9551487160003300699123520864162633000644) * 10^40
        + 2333250915622008931585436276202012050883) * 10^40
        + 8611817205537362836998977265148870663239) * 10^40
        + 8069838040198259350706064885209790711868) * 10^40
        + 9234987440321836759237128597906105971813) * 10^40
        + 6150716064185074690244751051814108628059) * 10^40
        + 308177067997806361735247045118012562586) * 10^40
        + 4441335647035240096383398020737856502670) * 10^40
        + 1522786817476283496127116279706660310496) * 10^40
        + 150781618367398639509596554069985460224)),
    ((((((((((452024503262672483 * 10^40
        + 7315465118280231444194749639849960218362) * 10^40
        + 7599936849194974960774717801250965591179) * 10^40
        + 3741153123095043383972203275511636726580) * 10^40
        + 3326454922036037744526067810194807779507) * 10^40
        + 1812912981300024588551079004245773404609) * 10^40
        + 6190543976199101075132975098406003818888) * 10^40
        + 2211032462901001497259019707432792021495) * 10^40
        + 9527526110347382036070412271666508742917) : ℚ) /
        ((((((((981591611448 * 10^40
        + 4347774959227469030273169299215005082725) * 10^40
        + 6062890827143756363242301706401694079765) * 10^40
        + 3759383278356768069189003515679062072650) * 10^40
        + 7576842106667468906390147321024212256386) * 10^40
        + 5090972654937364926723732267594277160648) * 10^40
        + 2693353254024225145429879141644706235048) * 10^40
        + 7670701109528587208045449148789471049807) * 10^40
        + 8704515561875087274121862192946424578048)))

noncomputable def batchN05119PlusP028Error2559 : ℝ := ((13469970627528118889679392474365 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP028BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP028Center2559‖ ≤ batchN05119PlusP028Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP028Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP028Input2559]
  have hs : compactExp2547 batchN05119PlusP028Input2559 5 =
      (batchN05119PlusP028Center2559, ((13469970627528118889679392474365 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP028Input2559 5).2 : ℝ) = batchN05119PlusP028Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP028Error2559]
  have h := compactExp_error2547 batchN05119PlusP028Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP028Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP028Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP028DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP028Factor2559 * embedPair2542 batchN05119PlusP028Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP028Factor2559 : ℝ) * batchN05119PlusP028Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP028Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP028Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP028BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP028Factor2559)

def batchN05119PlusP029Input2559 : RatPair2542 := ((((-((385477 * 10^40
        + 5389239569957726890493077653655650539425) * 10^40
        + 1200921245185496057528457197419500947067)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((182939534351242879487659 : ℚ) /
        57646075230342348800000000))

def batchN05119PlusP029Center2559 : RatPair2542 := (((33992369112637758179745966761293041 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((3463903364671670554359636283511105 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN05119PlusP029Factor2559 : RatPair2542 :=
    ((((-(((((((((((25053792937208149539527848833905 *
    10^40
        + 4182982698607875193406911560838285547028) * 10^40
        + 445868041730874269780135379498979679587) * 10^40
        + 3149563910454935550793801706415296669556) * 10^40
        + 4994977965270132025171201636480005992360) * 10^40
        + 3241272052300240530365648371814496943306) * 10^40
        + 7466819328032651301432463311026178381571) * 10^40
        + 9827908177276342789259261329402822480864) * 10^40
        + 510723082732182525341873017807846639764) * 10^40
        + 6002734050541841133397907805654892261538) * 10^40
        + 5053331716686554537858236953809595950665) * 10^40
        + 7589732869395597663886269270244269888081)) : ℚ) /
        (((((((((((2609182955507294514147186293 * 10^40
        + 6060969799695168051149863511815641438481) * 10^40
        + 9551487160003300699123520864162633000644) * 10^40
        + 2333250915622008931585436276202012050883) * 10^40
        + 8611817205537362836998977265148870663239) * 10^40
        + 8069838040198259350706064885209790711868) * 10^40
        + 9234987440321836759237128597906105971813) * 10^40
        + 6150716064185074690244751051814108628059) * 10^40
        + 308177067997806361735247045118012562586) * 10^40
        + 4441335647035240096383398020737856502670) * 10^40
        + 1522786817476283496127116279706660310496) * 10^40
        + 150781618367398639509596554069985460224)),
    ((((((((((5407495485633143894 * 10^40
        + 3166295389258969090223434429009970428144) * 10^40
        + 3670159387466291951476950374231554382675) * 10^40
        + 2291321088766347078337925063920389822898) * 10^40
        + 5191324564534649456611826125603752877249) * 10^40
        + 9844311544742344712235369030541934819081) * 10^40
        + 2176353865153639680421558529440369081129) * 10^40
        + 125208113674845687701788771693971340977) * 10^40
        + 4043680766013256159804291342583388241507) : ℚ) /
        ((((((((10797507725932 * 10^40
        + 7825524551502159333004862291365055909981) * 10^40
        + 6691799098581319995665318770418634877419) * 10^40
        + 1353216061924448761079038672469682799158) * 10^40
        + 3345263173342157970291620531266334820251) * 10^40
        + 6000699204311014193961054943537048767130) * 10^40
        + 9626885794266476599728670558091768585536) * 10^40
        + 4377712204814459288499940636684181547886) * 10^40
        + 5749671180625960015340484122410670358528)))

noncomputable def batchN05119PlusP029Error2559 : ℝ := ((13504215982396323554612879049929 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119PlusP029BaseError2559 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP029Center2559‖ ≤ batchN05119PlusP029Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119PlusP029Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119PlusP029Input2559]
  have hs : compactExp2547 batchN05119PlusP029Input2559 5 =
      (batchN05119PlusP029Center2559, ((13504215982396323554612879049929 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119PlusP029Input2559 5).2 : ℝ) = batchN05119PlusP029Error2559
      := by
    rw [hs]
    norm_num [batchN05119PlusP029Error2559]
  have h := compactExp_error2547 batchN05119PlusP029Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      batchN05119PlusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119PlusP029Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119PlusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119PlusP029Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119PlusP029DerivativeError2559 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05119PlusPosition2559 -
      embedPair2542 batchN05119PlusP029Factor2559 * embedPair2542 batchN05119PlusP029Center2559‖ ≤
        (pairMagnitude2542 batchN05119PlusP029Factor2559 : ℝ) * batchN05119PlusP029Error2559 := by
  have hx : |batchN05119PlusPosition2559| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchN05119PlusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchN05119PlusPosition2559 = embedPair2542
          batchN05119PlusP029Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119PlusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119PlusP029Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119PlusP029BaseError2559
    (embedPair_magnitude2542 batchN05119PlusP029Factor2559)

theorem batchN05119PlusGrid2559 :
    -stripRadius2303 + (5119 : ℝ) * (2 * stripRadius2303 / 10240) =
      batchN05119PlusPosition2559 := by
  norm_num [stripRadius2303, batchN05119PlusPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchN05119PlusP000DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP001DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP002DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP003DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP004DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP005DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP006DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP007DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP008DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP009DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP010DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP011DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP012DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP013DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP014DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP015DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP016DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP017DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP018DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP019DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP020DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP021DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP022DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP023DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP024DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP025DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP026DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP027DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP028DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusP029DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119PlusGrid2559
